-- Companion obligations file for the `clever_150_compare` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_150_compare

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_150_compareObligations

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_025_remove_duplicates`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_no_bv (i : usize) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hi := (USize64.uaddOverflow_iff i 1).mp hbo
    rw [usize_one_toNat] at hi
    omega

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

@[simp]
private theorem push_one_size
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  simp

/-! ## Step lemmas for `build_at`.

The function body case-splits on `i ≥ s.len() || i ≥ g.len()` (out-of-bounds)
vs the in-range case. In range, it case-splits again on `s[i] ≥ g[i]` to
pick which subtraction to compute as `d`, pushes a 1-element chunk via
`extend_from_slice`, then recurses. -/

/-- Out-of-bounds step: when `i.toNat ≥ s.val.size` or `i.toNat ≥ g.val.size`,
    `build_at` returns the accumulator unchanged. -/
private theorem build_at_oob (s g : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (h_oob : s.val.size ≤ i.toNat ∨ g.val.size ≤ i.toNat) :
    clever_150_compare.build_at s g i acc = RustM.ok acc := by
  conv => lhs; unfold clever_150_compare.build_at
  have h_s_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize
  have h_g_ofNat : (USize64.ofNat g.val.size).toNat = g.val.size :=
    USize64.toNat_ofNat_of_lt' g.size_lt_usizeSize
  have h_cond : (decide (USize64.ofNat s.val.size ≤ i)
                 || decide (USize64.ofNat g.val.size ≤ i)) = true := by
    rcases h_oob with h_s | h_g
    · have h_le : USize64.ofNat s.val.size ≤ i :=
        USize64.le_iff_toNat_le.mpr (by rw [h_s_ofNat]; exact h_s)
      rw [decide_eq_true h_le]; rfl
    · have h_le : USize64.ofNat g.val.size ≤ i :=
        USize64.le_iff_toNat_le.mpr (by rw [h_g_ofNat]; exact h_g)
      rw [decide_eq_true h_le]; exact Bool.or_true _
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             rust_primitives.hax.logical_op.or,
             h_cond, ↓reduceIte]
  rfl

/-! ## In-range step lemmas. -/

/-- Left arm: `s[i] ≥ g[i]` and no subtraction overflow on `s[i] - g[i]`.
    The recursion steps with the chunk value `s[i] - g[i]`. -/
private theorem build_at_step_left
    (s g : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (his : i.toNat < s.val.size) (hig : i.toNat < g.val.size)
    (h_ge : (s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig))
    (h_no_sub : ¬ Int64.subOverflow (s.val[i.toNat]'his) (g.val[i.toNat]'hig))
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_150_compare.build_at s g i acc =
      clever_150_compare.build_at s g (i + 1)
        (push_one acc ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)) h_acc) := by
  conv => lhs; unfold clever_150_compare.build_at
  have h_s_size : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_g_size : g.val.size < USize64.size := g.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_s_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_s_size
  have h_g_ofNat : (USize64.ofNat g.val.size).toNat = g.val.size :=
    USize64.toNat_ofNat_of_lt' h_g_size
  have h_cond_s : decide (USize64.ofNat s.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_s_ofNat] at hle
    omega
  have h_cond_g : decide (USize64.ofNat g.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_g_ofNat] at hle
    omega
  have h_cond_or : (decide (USize64.ofNat s.val.size ≤ i)
                    || decide (USize64.ofNat g.val.size ≤ i)) = false := by
    rw [h_cond_s, h_cond_g]; rfl
  have h_s_idx : (s[i]_? : RustM i64) = RustM.ok (s.val[i.toNat]'his) := by
    show (if h : i.toNat < s.val.size then pure (s.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (s.val[i.toNat]'his)
    rw [dif_pos his]; rfl
  have h_g_idx : (g[i]_? : RustM i64) = RustM.ok (g.val[i.toNat]'hig) := by
    show (if h : i.toNat < g.val.size then pure (g.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (g.val[i.toNat]'hig)
    rw [dif_pos hig]; rfl
  have h_dec_ge : decide ((s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig)) = true :=
    decide_eq_true h_ge
  have h_no_bv_sub : BitVec.ssubOverflow (s.val[i.toNat]'his).toBitVec
                       (g.val[i.toNat]'hig).toBitVec = false := by
    cases hb : BitVec.ssubOverflow (s.val[i.toNat]'his).toBitVec
                                    (g.val[i.toNat]'hig).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_sub
  have h_sub_eq : ((s.val[i.toNat]'his) -? (g.val[i.toNat]'hig) : RustM i64)
      = RustM.ok ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)) := by
    show (rust_primitives.ops.arith.Sub.sub
            (s.val[i.toNat]'his) (g.val[i.toNat]'hig) : RustM i64) = _
    show (if BitVec.ssubOverflow (s.val[i.toNat]'his).toBitVec
              (g.val[i.toNat]'hig).toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig))) = _
    rw [h_no_bv_sub]; rfl
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_s_size; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             rust_primitives.hax.logical_op.or,
             h_cond_or, Bool.false_eq_true, ↓reduceIte,
             h_s_idx, h_g_idx, h_dec_ge,
             rust_primitives.ops.arith.Sub.sub, h_no_bv_sub]
  -- After simp, the chunk and extend_from_slice remain to reduce.
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[(s.val[i.toNat]'his) - (g.val[i.toNat]'hig)] :
              RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[(s.val[i.toNat]'his) - (g.val[i.toNat]'hig)],
              one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[(s.val[i.toNat]'his) - (g.val[i.toNat]'hig)]
        : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[(s.val[i.toNat]'his) - (g.val[i.toNat]'hig)],
                one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc
              ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-- Right arm: `¬ (s[i] ≥ g[i])` and no subtraction overflow on `g[i] - s[i]`.
    The recursion steps with the chunk value `g[i] - s[i]`. -/
private theorem build_at_step_right
    (s g : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (his : i.toNat < s.val.size) (hig : i.toNat < g.val.size)
    (h_nge : ¬ ((s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig)))
    (h_no_sub : ¬ Int64.subOverflow (g.val[i.toNat]'hig) (s.val[i.toNat]'his))
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_150_compare.build_at s g i acc =
      clever_150_compare.build_at s g (i + 1)
        (push_one acc ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)) h_acc) := by
  conv => lhs; unfold clever_150_compare.build_at
  have h_s_size : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_g_size : g.val.size < USize64.size := g.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_s_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_s_size
  have h_g_ofNat : (USize64.ofNat g.val.size).toNat = g.val.size :=
    USize64.toNat_ofNat_of_lt' h_g_size
  have h_cond_s : decide (USize64.ofNat s.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_s_ofNat] at hle
    omega
  have h_cond_g : decide (USize64.ofNat g.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_g_ofNat] at hle
    omega
  have h_cond_or : (decide (USize64.ofNat s.val.size ≤ i)
                    || decide (USize64.ofNat g.val.size ≤ i)) = false := by
    rw [h_cond_s, h_cond_g]; rfl
  have h_s_idx : (s[i]_? : RustM i64) = RustM.ok (s.val[i.toNat]'his) := by
    show (if h : i.toNat < s.val.size then pure (s.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (s.val[i.toNat]'his)
    rw [dif_pos his]; rfl
  have h_g_idx : (g[i]_? : RustM i64) = RustM.ok (g.val[i.toNat]'hig) := by
    show (if h : i.toNat < g.val.size then pure (g.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (g.val[i.toNat]'hig)
    rw [dif_pos hig]; rfl
  have h_dec_ge : decide ((s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig)) = false :=
    decide_eq_false h_nge
  have h_no_bv_sub : BitVec.ssubOverflow (g.val[i.toNat]'hig).toBitVec
                       (s.val[i.toNat]'his).toBitVec = false := by
    cases hb : BitVec.ssubOverflow (g.val[i.toNat]'hig).toBitVec
                                    (s.val[i.toNat]'his).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_sub
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_s_size; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_ov_i
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             rust_primitives.hax.logical_op.or,
             h_cond_or, Bool.false_eq_true, ↓reduceIte,
             h_s_idx, h_g_idx, h_dec_ge,
             rust_primitives.ops.arith.Sub.sub, h_no_bv_sub]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[(g.val[i.toNat]'hig) - (s.val[i.toNat]'his)] :
              RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[(g.val[i.toNat]'hig) - (s.val[i.toNat]'his)],
              one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[(g.val[i.toNat]'hig) - (s.val[i.toNat]'his)]
        : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[(g.val[i.toNat]'hig) - (s.val[i.toNat]'his)],
                one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc
              ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-- Left failure: `s[i] ≥ g[i]` and `Int64.subOverflow s[i] g[i]` is true.
    The function fails with `integerOverflow`. -/
private theorem build_at_step_left_fail
    (s g : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (his : i.toNat < s.val.size) (hig : i.toNat < g.val.size)
    (h_ge : (s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig))
    (h_ov : Int64.subOverflow (s.val[i.toNat]'his) (g.val[i.toNat]'hig)) :
    clever_150_compare.build_at s g i acc = RustM.fail Error.integerOverflow := by
  conv => lhs; unfold clever_150_compare.build_at
  have h_s_size : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_g_size : g.val.size < USize64.size := g.size_lt_usizeSize
  have h_s_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_s_size
  have h_g_ofNat : (USize64.ofNat g.val.size).toNat = g.val.size :=
    USize64.toNat_ofNat_of_lt' h_g_size
  have h_cond_s : decide (USize64.ofNat s.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_s_ofNat] at hle
    omega
  have h_cond_g : decide (USize64.ofNat g.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_g_ofNat] at hle
    omega
  have h_cond_or : (decide (USize64.ofNat s.val.size ≤ i)
                    || decide (USize64.ofNat g.val.size ≤ i)) = false := by
    rw [h_cond_s, h_cond_g]; rfl
  have h_s_idx : (s[i]_? : RustM i64) = RustM.ok (s.val[i.toNat]'his) := by
    show (if h : i.toNat < s.val.size then pure (s.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (s.val[i.toNat]'his)
    rw [dif_pos his]; rfl
  have h_g_idx : (g[i]_? : RustM i64) = RustM.ok (g.val[i.toNat]'hig) := by
    show (if h : i.toNat < g.val.size then pure (g.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (g.val[i.toNat]'hig)
    rw [dif_pos hig]; rfl
  have h_dec_ge : decide ((s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig)) = true :=
    decide_eq_true h_ge
  have h_bv_sub : BitVec.ssubOverflow (s.val[i.toNat]'his).toBitVec
                    (g.val[i.toNat]'hig).toBitVec = true := h_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             rust_primitives.hax.logical_op.or,
             h_cond_or, Bool.false_eq_true, ↓reduceIte,
             h_s_idx, h_g_idx, h_dec_ge,
             rust_primitives.ops.arith.Sub.sub, h_bv_sub]
  rfl

/-- Right failure: `¬ (s[i] ≥ g[i])` and `Int64.subOverflow g[i] s[i]` is true.
    The function fails with `integerOverflow`. -/
private theorem build_at_step_right_fail
    (s g : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (his : i.toNat < s.val.size) (hig : i.toNat < g.val.size)
    (h_nge : ¬ ((s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig)))
    (h_ov : Int64.subOverflow (g.val[i.toNat]'hig) (s.val[i.toNat]'his)) :
    clever_150_compare.build_at s g i acc = RustM.fail Error.integerOverflow := by
  conv => lhs; unfold clever_150_compare.build_at
  have h_s_size : s.val.size < USize64.size := s.size_lt_usizeSize
  have h_g_size : g.val.size < USize64.size := g.size_lt_usizeSize
  have h_s_ofNat : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' h_s_size
  have h_g_ofNat : (USize64.ofNat g.val.size).toNat = g.val.size :=
    USize64.toNat_ofNat_of_lt' h_g_size
  have h_cond_s : decide (USize64.ofNat s.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_s_ofNat] at hle
    omega
  have h_cond_g : decide (USize64.ofNat g.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_g_ofNat] at hle
    omega
  have h_cond_or : (decide (USize64.ofNat s.val.size ≤ i)
                    || decide (USize64.ofNat g.val.size ≤ i)) = false := by
    rw [h_cond_s, h_cond_g]; rfl
  have h_s_idx : (s[i]_? : RustM i64) = RustM.ok (s.val[i.toNat]'his) := by
    show (if h : i.toNat < s.val.size then pure (s.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (s.val[i.toNat]'his)
    rw [dif_pos his]; rfl
  have h_g_idx : (g[i]_? : RustM i64) = RustM.ok (g.val[i.toNat]'hig) := by
    show (if h : i.toNat < g.val.size then pure (g.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (g.val[i.toNat]'hig)
    rw [dif_pos hig]; rfl
  have h_dec_ge : decide ((s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig)) = false :=
    decide_eq_false h_nge
  have h_bv_sub : BitVec.ssubOverflow (g.val[i.toNat]'hig).toBitVec
                    (s.val[i.toNat]'his).toBitVec = true := h_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             rust_primitives.hax.logical_op.or,
             h_cond_or, Bool.false_eq_true, ↓reduceIte,
             h_s_idx, h_g_idx, h_dec_ge,
             rust_primitives.ops.arith.Sub.sub, h_bv_sub]
  rfl

/-! ## Strong induction lemma over `build_at`. -/

private theorem build_at_correct (s g : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (v : alloc.vec.Vec i64 alloc.alloc.Global),
      min s.val.size g.val.size - i.toNat ≤ n →
      i.toNat ≤ min s.val.size g.val.size →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size)
         (hjs : j < s.val.size) (hjg : j < g.val.size),
          (acc.val[j]'hj).toInt =
            ((s.val[j]'hjs).toInt - (g.val[j]'hjg).toInt).natAbs) →
      clever_150_compare.build_at s g i acc = RustM.ok v →
      v.val.size = min s.val.size g.val.size ∧
      (∀ (j : Nat) (hj : j < v.val.size)
         (hjs : j < s.val.size) (hjg : j < g.val.size),
          (v.val[j]'hj).toInt =
            ((s.val[j]'hjs).toInt - (g.val[j]'hjg).toInt).natAbs) := by
  intro n
  induction n with
  | zero =>
    intro i acc v hn hi_le h_acc_size h_acc_inv hres
    -- i.toNat ≥ min, so OOB applies.
    have hi_eq : i.toNat = min s.val.size g.val.size := by omega
    have h_oob : s.val.size ≤ i.toNat ∨ g.val.size ≤ i.toNat := by
      have h_min_le_s : min s.val.size g.val.size ≤ s.val.size := Nat.min_le_left _ _
      have h_min_le_g : min s.val.size g.val.size ≤ g.val.size := Nat.min_le_right _ _
      -- We know i.toNat = min. The min equals either s or g.
      by_cases h_le : s.val.size ≤ g.val.size
      · left
        have h_min_eq : min s.val.size g.val.size = s.val.size :=
          Nat.min_eq_left h_le
        rw [h_min_eq] at hi_eq; omega
      · right
        have h_le' : g.val.size ≤ s.val.size := Nat.le_of_not_le h_le
        have h_min_eq : min s.val.size g.val.size = g.val.size :=
          Nat.min_eq_right h_le'
        rw [h_min_eq] at hi_eq; omega
    rw [build_at_oob s g i acc h_oob] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro j hj hjs hjg
      exact h_acc_inv j hj hjs hjg
  | succ n ih =>
    intro i acc v hn hi_le h_acc_size h_acc_inv hres
    by_cases h_oob_disj : s.val.size ≤ i.toNat ∨ g.val.size ≤ i.toNat
    · -- OOB: use build_at_oob.
      rw [build_at_oob s g i acc h_oob_disj] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      have hi_eq : i.toNat = min s.val.size g.val.size := by
        have h_min_le_s : min s.val.size g.val.size ≤ s.val.size := Nat.min_le_left _ _
        have h_min_le_g : min s.val.size g.val.size ≤ g.val.size := Nat.min_le_right _ _
        rcases h_oob_disj with h_s | h_g
        · -- i.toNat ≥ s.size ≥ min
          have : min s.val.size g.val.size ≤ i.toNat := by omega
          omega
        · have : min s.val.size g.val.size ≤ i.toNat := by omega
          omega
      refine ⟨?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro j hj hjs hjg
        exact h_acc_inv j hj hjs hjg
    · -- In range: i.toNat < s.val.size AND i.toNat < g.val.size.
      have h_not_s : ¬ s.val.size ≤ i.toNat := fun h => h_oob_disj (Or.inl h)
      have h_not_g : ¬ g.val.size ≤ i.toNat := fun h => h_oob_disj (Or.inr h)
      have his : i.toNat < s.val.size := Nat.lt_of_not_le h_not_s
      have hig : i.toNat < g.val.size := Nat.lt_of_not_le h_not_g
      have h_lt_min : i.toNat < min s.val.size g.val.size := by
        rw [Nat.lt_min]; exact ⟨his, hig⟩
      have h_s_size : s.val.size < USize64.size := s.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_s_size; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_usize_size]; rw [h_acc_size]
        have h_s_lt : s.val.size < 2^64 := by rw [h_usize_size] at h_s_size; exact h_s_size
        omega
      -- Case split on s[i] ≥ g[i] vs not, and on subOverflow.
      by_cases h_ge : (s.val[i.toNat]'his) ≥ (g.val[i.toNat]'hig)
      · -- Left arm: case on overflow.
        by_cases h_ov : Int64.subOverflow (s.val[i.toNat]'his) (g.val[i.toNat]'hig)
        · -- Overflow: contradicts hres.
          exfalso
          rw [build_at_step_left_fail s g i acc his hig h_ge h_ov] at hres
          cases hres
        · -- No overflow: step.
          rw [build_at_step_left s g i acc his hig h_ge h_ov h_acc_succ] at hres
          have h_new_size :
              (push_one acc ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)) h_acc_succ).val.size
                = (i + 1).toNat := by
            show (acc.val ++ #[_]).size = (i + 1).toNat
            rw [Array.size_append, h_i1]
            show acc.val.size + 1 = i.toNat + 1
            rw [h_acc_size]
          have h_i1_le : (i + 1).toNat ≤ min s.val.size g.val.size := by
            rw [h_i1]
            have : i.toNat + 1 ≤ min s.val.size g.val.size := h_lt_min
            exact this
          have h_meas : min s.val.size g.val.size - (i + 1).toNat ≤ n := by
            rw [h_i1]; omega
          have h_new_inv : ∀ (j : Nat)
              (hj : j < (push_one acc
                ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)) h_acc_succ).val.size)
              (hjs : j < s.val.size) (hjg : j < g.val.size),
              ((push_one acc
                ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)) h_acc_succ).val[j]'hj).toInt =
                ((s.val[j]'hjs).toInt - (g.val[j]'hjg).toInt).natAbs := by
            intro j hj hjs hjg
            show ((acc.val ++ #[_])[j]'hj).toInt = _
            by_cases hjlt : j < acc.val.size
            · rw [Array.getElem_append_left hjlt]
              exact h_acc_inv j hjlt hjs hjg
            · have h_size_raw : (acc.val ++ #[
                  ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig))]).size =
                  acc.val.size + 1 := by
                rw [Array.size_append]; rfl
              have hj_eq : j = acc.val.size := by
                have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
                omega
              subst hj_eq
              rw [Array.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self]
              show ((#[((s.val[i.toNat]'his) - (g.val[i.toNat]'hig))] :
                    Array i64)[0]).toInt = _
              have h_sub_toInt :
                  ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)).toInt =
                    (s.val[i.toNat]'his).toInt - (g.val[i.toNat]'hig).toInt :=
                Int64.toInt_sub_of_not_subOverflow h_ov
              have h_acc_size_eq_i : acc.val.size = i.toNat := h_acc_size
              have h_s_idx_eq : s.val[acc.val.size]'hjs = s.val[i.toNat]'his :=
                getElem_congr_idx h_acc_size_eq_i
              have h_g_idx_eq : g.val[acc.val.size]'hjg = g.val[i.toNat]'hig :=
                getElem_congr_idx h_acc_size_eq_i
              rw [h_s_idx_eq, h_g_idx_eq]
              show ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)).toInt =
                ((s.val[i.toNat]'his).toInt - (g.val[i.toNat]'hig).toInt).natAbs
              rw [h_sub_toInt]
              have h_int_ge : (g.val[i.toNat]'hig).toInt ≤ (s.val[i.toNat]'his).toInt :=
                Int64.le_iff_toInt_le.mp h_ge
              have h_diff_nneg : 0 ≤
                  (s.val[i.toNat]'his).toInt - (g.val[i.toNat]'hig).toInt := by omega
              rw [Int.natAbs_of_nonneg h_diff_nneg]
          exact ih (i + 1)
            (push_one acc ((s.val[i.toNat]'his) - (g.val[i.toNat]'hig)) h_acc_succ) v
            h_meas h_i1_le h_new_size h_new_inv hres
      · -- Right arm: case on overflow.
        by_cases h_ov : Int64.subOverflow (g.val[i.toNat]'hig) (s.val[i.toNat]'his)
        · -- Overflow: contradicts hres.
          exfalso
          rw [build_at_step_right_fail s g i acc his hig h_ge h_ov] at hres
          cases hres
        · -- No overflow: step.
          rw [build_at_step_right s g i acc his hig h_ge h_ov h_acc_succ] at hres
          have h_new_size :
              (push_one acc ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)) h_acc_succ).val.size
                = (i + 1).toNat := by
            show (acc.val ++ #[_]).size = (i + 1).toNat
            rw [Array.size_append, h_i1]
            show acc.val.size + 1 = i.toNat + 1
            rw [h_acc_size]
          have h_i1_le : (i + 1).toNat ≤ min s.val.size g.val.size := by
            rw [h_i1]; exact h_lt_min
          have h_meas : min s.val.size g.val.size - (i + 1).toNat ≤ n := by
            rw [h_i1]; omega
          have h_new_inv : ∀ (j : Nat)
              (hj : j < (push_one acc
                ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)) h_acc_succ).val.size)
              (hjs : j < s.val.size) (hjg : j < g.val.size),
              ((push_one acc
                ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)) h_acc_succ).val[j]'hj).toInt =
                ((s.val[j]'hjs).toInt - (g.val[j]'hjg).toInt).natAbs := by
            intro j hj hjs hjg
            show ((acc.val ++ #[_])[j]'hj).toInt = _
            by_cases hjlt : j < acc.val.size
            · rw [Array.getElem_append_left hjlt]
              exact h_acc_inv j hjlt hjs hjg
            · have h_size_raw : (acc.val ++ #[
                  ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his))]).size =
                  acc.val.size + 1 := by
                rw [Array.size_append]; rfl
              have hj_eq : j = acc.val.size := by
                have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
                omega
              subst hj_eq
              rw [Array.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self]
              show ((#[((g.val[i.toNat]'hig) - (s.val[i.toNat]'his))] :
                    Array i64)[0]).toInt = _
              have h_sub_toInt :
                  ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)).toInt =
                    (g.val[i.toNat]'hig).toInt - (s.val[i.toNat]'his).toInt :=
                Int64.toInt_sub_of_not_subOverflow h_ov
              have h_acc_size_eq_i : acc.val.size = i.toNat := h_acc_size
              have h_s_idx_eq : s.val[acc.val.size]'hjs = s.val[i.toNat]'his :=
                getElem_congr_idx h_acc_size_eq_i
              have h_g_idx_eq : g.val[acc.val.size]'hjg = g.val[i.toNat]'hig :=
                getElem_congr_idx h_acc_size_eq_i
              rw [h_s_idx_eq, h_g_idx_eq]
              show ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)).toInt =
                ((s.val[i.toNat]'his).toInt - (g.val[i.toNat]'hig).toInt).natAbs
              rw [h_sub_toInt]
              have h_int_lt : (s.val[i.toNat]'his).toInt < (g.val[i.toNat]'hig).toInt := by
                have h_not_le : ¬ (g.val[i.toNat]'hig).toInt ≤ (s.val[i.toNat]'his).toInt := by
                  intro h
                  exact h_ge (Int64.le_iff_toInt_le.mpr h)
                omega
              have h_diff_nneg : (0 : Int) ≤
                  (g.val[i.toNat]'hig).toInt - (s.val[i.toNat]'his).toInt := by omega
              have h_neg_eq : (s.val[i.toNat]'his).toInt - (g.val[i.toNat]'hig).toInt =
                  -((g.val[i.toNat]'hig).toInt - (s.val[i.toNat]'his).toInt) := by omega
              rw [h_neg_eq, Int.natAbs_neg, Int.natAbs_of_nonneg h_diff_nneg]
          exact ih (i + 1)
            (push_one acc ((g.val[i.toNat]'hig) - (s.val[i.toNat]'his)) h_acc_succ) v
            h_meas h_i1_le h_new_size h_new_inv hres

/-! ## Top-level obligations. -/

/-- Auxiliary lemma: specialise `build_at_correct` at the initial state of
    `compare`, i.e. `i = 0`, `acc = #[]`. -/
private theorem compare_aux (s g : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_150_compare.compare s g = RustM.ok v) :
    v.val.size = min s.val.size g.val.size ∧
    (∀ (j : Nat) (hj : j < v.val.size)
       (hjs : j < s.val.size) (hjg : j < g.val.size),
        (v.val[j]'hj).toInt =
          ((s.val[j]'hjs).toInt - (g.val[j]'hjg).toInt).natAbs) := by
  unfold clever_150_compare.compare at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_size : acc0.val.size = (0 : usize).toNat := by
    show (List.nil : List i64).toArray.size = 0
    rfl
  have h_acc0_inv : ∀ (j : Nat) (hj : j < acc0.val.size)
      (hjs : j < s.val.size) (hjg : j < g.val.size),
      (acc0.val[j]'hj).toInt =
        ((s.val[j]'hjs).toInt - (g.val[j]'hjg).toInt).natAbs := by
    intro j hj hjs hjg
    exfalso
    have h0 : acc0.val.size = 0 := by show (List.nil : List i64).toArray.size = 0; rfl
    rw [h0] at hj; omega
  have h_meas : min s.val.size g.val.size - (0 : usize).toNat
                  ≤ min s.val.size g.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ min s.val.size g.val.size := by
    rw [h_zero_toNat]; omega
  exact build_at_correct s g (min s.val.size g.val.size) (0 : usize) acc0 v
    h_meas h_i_le h_acc0_size h_acc0_inv hres

/-- Length postcondition.

    When `compare s g` succeeds with output `v`, the length of `v` equals the
    minimum of the two input slice lengths.

    Corresponds to the proptest `length_is_min_of_inputs`. -/
theorem compare_length
    (s g : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_150_compare.compare s g = RustM.ok v) :
    v.val.size = min s.val.size g.val.size := by
  exact (compare_aux s g v hres).1

/-- Element-value postcondition.

    When `compare s g` succeeds with output `v`, for every output index `i`
    (which is also a valid index into both input slices, since the output
    length is `min s.size g.size`), the i-th output equals the absolute
    difference `|s[i] - g[i]|` interpreted as integers.

    Corresponds to the proptest `element_is_absolute_difference`. -/
theorem compare_element_is_abs_difference
    (s g : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_150_compare.compare s g = RustM.ok v)
    (i : Nat) (hi : i < v.val.size)
    (his : i < s.val.size) (hig : i < g.val.size) :
    (v.val[i]'hi).toInt =
      ((s.val[i]'his).toInt - (g.val[i]'hig).toInt).natAbs := by
  exact (compare_aux s g v hres).2 i hi his hig

end Clever_150_compareObligations
