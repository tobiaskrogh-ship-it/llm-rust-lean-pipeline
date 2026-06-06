-- Companion obligations file for the `big_endian_from_slice_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import big_endian_from_slice_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Big_endian_from_slice_u64Obligations

/-! ## Specification oracle: big-endian (byte-reversal) of a `u64`.

On a little-endian host, "convert to big endian" (`u64::to_be`, which the
Rust source inlines as `swap_bytes_u64`) is exactly a byte reversal: the
result's byte `k` is the input's byte `7 - k`. We express this at the
`Nat` level, independent of the implementation's shift/mask form, so the
postcondition is a genuine semantic specification rather than a restatement
of the code. (`byteorder` doc: "Converts the given slice of unsigned 64
bit integers to big endian.") -/
private def byteRev64 (n : Nat) : Nat :=
  (n % 256) * 2 ^ 56
    + ((n / 2 ^ 8) % 256) * 2 ^ 48
    + ((n / 2 ^ 16) % 256) * 2 ^ 40
    + ((n / 2 ^ 24) % 256) * 2 ^ 32
    + ((n / 2 ^ 32) % 256) * 2 ^ 24
    + ((n / 2 ^ 40) % 256) * 2 ^ 16
    + ((n / 2 ^ 48) % 256) * 2 ^ 8
    + ((n / 2 ^ 56) % 256)

/-! ## Generic helpers (pattern reused from `clever_009_rolling_max`,
`clever_021_rescale_to_unit`, `contains_u64`, `average_ceil_u64`). -/

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

/-- Push a single element (1-chunk `extend_from_slice`). -/
private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Byte-swap (`swap_bytes_u64`) correctness.

`swap_bytes_u64` is a pure shift/mask function. We follow the
`average_ceil_u64` pattern: a Hoare triple discharged by `bv_decide`, then
a `Triple_iff_BitVec` unfold to the equational form `swap_bytes_u64 x =
RustM.ok (swapExpr x)`. Finally `swapExpr_toNat` bridges the bitvector
form to the `Nat`-level `byteRev64` oracle. -/

/-- The OR-of-masked-shifts form of `swap_bytes_u64`, mirroring the
    extracted body (shift amounts as `UInt64`, like the `average_ceil`
    reference's `>>> (1 : UInt64)`). -/
private def swapExpr (x : u64) : u64 :=
  ((x &&& 255) <<< (56 : UInt64))
    ||| ((x &&& 65280) <<< (40 : UInt64))
    ||| ((x &&& 16711680) <<< (24 : UInt64))
    ||| ((x &&& 4278190080) <<< (8 : UInt64))
    ||| ((x &&& 1095216660480) >>> (8 : UInt64))
    ||| ((x &&& 280375465082880) >>> (24 : UInt64))
    ||| ((x &&& 71776119061217280) >>> (40 : UInt64))
    ||| ((x &&& 18374686479671623680) >>> (56 : UInt64))

private theorem swap_bytes_triple (x : u64) :
    ⦃ ⌜ True ⌝ ⦄ big_endian_from_slice_u64.swap_bytes_u64 x
    ⦃ ⇓ r => ⌜ r = swapExpr x ⌝ ⦄ := by
  hax_mvcgen [big_endian_from_slice_u64.swap_bytes_u64, swapExpr]
  <;> bv_decide

/-- Derive the equation form from the Hoare triple (same shape as
    `average_ceil_unfold`). -/
private theorem swap_bytes_unfold (x : u64) :
    big_endian_from_slice_u64.swap_bytes_u64 x = RustM.ok (swapExpr x) := by
  have h := swap_bytes_triple x
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  cases hf : big_endian_from_slice_u64.swap_bytes_u64 x with
  | none =>
    rw [hf] at hok
    simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v =>
      rw [hf] at hval
      simp [RustM.toBVRustM] at hval
      exact congrArg (fun w => RustM.ok w) hval
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

/-- Byte-reversal at the `BitVec 64` level, in *additive* normal form so
    that `.toNat` distributes into the `byteRev64` arithmetic without ever
    producing a `Nat.land`. Masking is via `setWidth 8` (= `% 256`),
    division via `>>>`. -/
private def bvRev (a : BitVec 64) : BitVec 64 :=
  (((a >>> (56 : Nat)).setWidth 8).setWidth 64)
    + ((((a >>> (48 : Nat)).setWidth 8).setWidth 64) <<< (8 : Nat))
    + ((((a >>> (40 : Nat)).setWidth 8).setWidth 64) <<< (16 : Nat))
    + ((((a >>> (32 : Nat)).setWidth 8).setWidth 64) <<< (24 : Nat))
    + ((((a >>> (24 : Nat)).setWidth 8).setWidth 64) <<< (32 : Nat))
    + ((((a >>> (16 : Nat)).setWidth 8).setWidth 64) <<< (40 : Nat))
    + ((((a >>> (8 : Nat)).setWidth 8).setWidth 64) <<< (48 : Nat))
    + (((a.setWidth 8).setWidth 64) <<< (56 : Nat))

/-- The OR/shift/mask `swapExpr` equals the additive `bvRev` (a pure
    bitvector identity: the eight byte slots are disjoint, so `|||` = `+`).
    Discharged by `bv_decide`. -/
private theorem swapExpr_toBitVec (x : u64) :
    (swapExpr x).toBitVec = bvRev x.toBitVec := by
  unfold swapExpr bvRev
  bv_decide

/-- `bvRev` at the `Nat` level is exactly `byteRev64`. After pushing
    `BitVec.toNat` through the additive form (no `Nat.land` thanks to the
    `setWidth` masking), the residual is Presburger and `omega` closes
    it. -/
private theorem bvRev_toNat (a : BitVec 64) :
    (bvRev a).toNat = byteRev64 a.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  unfold bvRev byteRev64
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
             BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
             Nat.shiftLeft_eq]
  omega

private theorem swapExpr_toNat (x : u64) :
    (swapExpr x).toNat = byteRev64 x.toNat := by
  have h := congrArg BitVec.toNat (swapExpr_toBitVec x)
  rw [bvRev_toNat] at h
  exact h

/-- `swap_bytes_u64` is total and its output's `.toNat` is `byteRev64`. -/
private theorem swap_bytes_spec (x : u64) :
    big_endian_from_slice_u64.swap_bytes_u64 x = RustM.ok (swapExpr x)
    ∧ (swapExpr x).toNat = byteRev64 x.toNat :=
  ⟨swap_bytes_unfold x, swapExpr_toNat x⟩

/-! ## `build_swapped` step lemmas (pattern from `shift_at_step`). -/

private theorem build_swapped_oob
    (numbers : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : numbers.val.size ≤ i.toNat) :
    big_endian_from_slice_u64.build_swapped numbers i acc = RustM.ok acc := by
  conv => lhs; unfold big_endian_from_slice_u64.build_swapped
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem build_swapped_step
    (numbers : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    big_endian_from_slice_u64.build_swapped numbers i acc =
      big_endian_from_slice_u64.build_swapped numbers (i + 1)
        (push_one acc (swapExpr (numbers.val[i.toNat]'hi)) h_acc) := by
  conv => lhs; unfold big_endian_from_slice_u64.build_swapped
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM u64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_swap :
      (big_endian_from_slice_u64.swap_bytes_u64 (numbers.val[i.toNat]'hi))
        = RustM.ok (swapExpr (numbers.val[i.toNat]'hi)) :=
    swap_bytes_unfold (numbers.val[i.toNat]'hi)
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_swap]
  -- Reduce unsize and extend_from_slice using the 1-chunk pattern.
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[(swapExpr (numbers.val[i.toNat]'hi))]
                : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
            = RustM.ok ⟨#[(swapExpr (numbers.val[i.toNat]'hi))],
                        one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size +
        (#[(swapExpr (numbers.val[i.toNat]'hi))] : Array u64).size
          < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[(swapExpr (numbers.val[i.toNat]'hi))], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc (swapExpr (numbers.val[i.toNat]'hi)) h_acc)
      from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-! ## Strong induction for `build_swapped` (mirrors `shift_at_correct`).
Invariant: `acc.val.size = i.toNat`, and `acc` holds the byte-reversed
prefix. -/

private theorem build_swapped_correct (numbers : RustSlice u64) :
    ∀ (k : Nat) (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ k →
      i.toNat ≤ numbers.val.size →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size) (hj_n : j < numbers.val.size),
          (acc.val[j]'hj).toNat = byteRev64 (numbers.val[j]'hj_n).toNat) →
      ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
        big_endian_from_slice_u64.build_swapped numbers i acc = RustM.ok v ∧
        v.val.size = numbers.val.size ∧
        (∀ (j : Nat) (hj : j < v.val.size) (hj_n : j < numbers.val.size),
            (v.val[j]'hj).toNat = byteRev64 (numbers.val[j]'hj_n).toNat) := by
  intro k
  induction k with
  | zero =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨acc, build_swapped_oob numbers i acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intros j hj hj_n; exact h_acc_chunk j hj hj_n
  | succ k ih =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      refine ⟨acc, build_swapped_oob numbers i acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intros j hj hj_n; exact h_acc_chunk j hj hj_n
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, h_usize_size]; omega
      have h_step := build_swapped_step numbers i acc hi_lt h_acc_succ
      rw [h_step]
      have h_acc'_size :
          (push_one acc (swapExpr (numbers.val[i.toNat]'hi_lt)) h_acc_succ).val.size
            = (i + 1).toNat := by
        show (acc.val ++ #[_]).size = (i + 1).toNat
        rw [Array.size_append, h_i1, h_acc_size]
        rfl
      have h_acc'_chunk :
          ∀ (j : Nat)
            (hj : j < (push_one acc (swapExpr (numbers.val[i.toNat]'hi_lt))
                        h_acc_succ).val.size)
            (hj_n : j < numbers.val.size),
            ((push_one acc (swapExpr (numbers.val[i.toNat]'hi_lt))
                h_acc_succ).val[j]'hj).toNat
              = byteRev64 (numbers.val[j]'hj_n).toNat := by
        intro j hj hj_n
        show ((acc.val ++ #[swapExpr (numbers.val[i.toNat]'hi_lt)])[j]'hj).toNat
              = _
        by_cases hjlt : j < acc.val.size
        · rw [Array.getElem_append_left hjlt]
          exact h_acc_chunk j hjlt hj_n
        · have h_size_raw :
              (acc.val ++ #[swapExpr (numbers.val[i.toNat]'hi_lt)]).size
                = acc.val.size + 1 := by rw [Array.size_append]; rfl
          have hj_eq : j = acc.val.size := by
            have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
            omega
          subst hj_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show ((#[swapExpr (numbers.val[i.toNat]'hi_lt)] : Array u64)[0]).toNat
                = _
          have h_num_eq :
              numbers.val[i.toNat]'hi_lt = numbers.val[acc.val.size]'hj_n :=
            getElem_congr_idx h_acc_size.symm
          rw [← h_num_eq]
          exact swapExpr_toNat (numbers.val[i.toNat]'hi_lt)
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_k_le : numbers.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      exact ih (i + 1) _ h_k_le h_i1_le h_acc'_size h_acc'_chunk

/-! ## `from_slice_u64` reduces to `build_swapped` from the empty buffer.

`if true` takes the then-branch; `Vec::new` is the empty buffer;
`Deref::deref` is the identity; `copy_from_slice` returns its `src`
argument (via `mem.replace`). So the whole function is exactly
`build_swapped numbers 0 []`. -/

private theorem from_slice_u64_eq_build (numbers : RustSlice u64) :
    big_endian_from_slice_u64.from_slice_u64 numbers
      = big_endian_from_slice_u64.build_swapped numbers (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ := by
  unfold big_endian_from_slice_u64.from_slice_u64
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk
                  : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
                = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  simp only [if_true, h_new, RustM_ok_bind,
             core_models.ops.deref.Deref.deref,
             core_models.slice.Impl.copy_from_slice, rust_primitives.mem.replace,
             pure_bind, bind_pure]

/-! ## Aux: `from_slice_u64` is total, length-preserving and byte-reversing. -/

private theorem from_slice_u64_aux (numbers : RustSlice u64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      big_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v ∧
      v.val.size = numbers.val.size ∧
      (∀ (j : Nat) (hj : j < v.val.size) (hj_n : j < numbers.val.size),
          (v.val[j]'hj).toNat = byteRev64 (numbers.val[j]'hj_n).toNat) := by
  rw [from_slice_u64_eq_build numbers]
  have h_acc0_size :
      (⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global).val.size
        = (0 : usize).toNat := rfl
  have h_acc0_chunk :
      ∀ (j : Nat)
        (hj : j < (⟨(List.nil).toArray, by grind⟩
                    : alloc.vec.Vec u64 alloc.alloc.Global).val.size)
        (hj_n : j < numbers.val.size),
        (((⟨(List.nil).toArray, by grind⟩
            : alloc.vec.Vec u64 alloc.alloc.Global).val[j]'hj).toNat)
          = byteRev64 (numbers.val[j]'hj_n).toNat := by
    intro j hj hj_n
    exact absurd hj (by simp)
  have h_zero_le : (0 : usize).toNat ≤ numbers.val.size := by
    show 0 ≤ numbers.val.size; omega
  have h_m_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    show numbers.val.size - 0 ≤ numbers.val.size; omega
  exact build_swapped_correct numbers numbers.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩
          h_m_le h_zero_le h_acc0_size h_acc0_chunk

/-! ## Obligations. -/

/-- Failure condition / totality. `from_slice_u64`'s Rust return type is
    `()` (here the rewritten slice); it has no preconditions and no
    panic/overflow path. The decreasing recursion in `build_swapped`
    always terminates and every `extend_from_slice` stays within `usize`
    because the final buffer length equals the input length. Captures the
    "completes without panicking" assertion of
    `prop_empty_slice_is_total_and_noop` in its general form. -/
theorem from_slice_u64_total (numbers : RustSlice u64) :
    ∃ v : RustSlice u64,
      big_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v := by
  obtain ⟨v, hv, _, _⟩ := from_slice_u64_aux numbers
  exact ⟨v, hv⟩

/-- Length-preservation postcondition. Captures the
    `assert_eq!(numbers.len(), original.len())` clause of
    `prop_each_element_becomes_big_endian`: the slice is rewritten in
    place with exactly one output element per input element. -/
theorem from_slice_u64_preserves_length
    (numbers : RustSlice u64)
    (v : RustSlice u64)
    (hres : big_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v) :
    v.val.size = numbers.val.size := by
  obtain ⟨v', hv', hsz, _⟩ := from_slice_u64_aux numbers
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hsz

/-- Core functional postcondition. Captures the
    `assert_eq!(numbers[i], original[i].to_be())` clause of
    `prop_each_element_becomes_big_endian` (and the `doc_example_big_endian`
    doc-test, which is a concrete instance): each output element is the
    byte-reversed image of the corresponding input element, taken at its
    own index (so no reordering and, with the length clause, no drops). -/
theorem from_slice_u64_elementwise_be
    (numbers : RustSlice u64)
    (v : RustSlice u64)
    (hres : big_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v)
    (j : Nat) (hj : j < v.val.size) (hj' : j < numbers.val.size) :
    (v.val[j]'hj).toNat = byteRev64 (numbers.val[j]'hj').toNat := by
  obtain ⟨v', hv', _, hel⟩ := from_slice_u64_aux numbers
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hel j hj hj'

/-- Empty-slice edge case. Captures `prop_empty_slice_is_total_and_noop`:
    on an empty input the function completes successfully and yields an
    empty slice (the `build_swapped` base case fires immediately, and the
    whole-slice `copy_from_slice` write-back is a no-op). -/
theorem from_slice_u64_empty_noop
    (numbers : RustSlice u64)
    (hempty : numbers.val.size = 0) :
    ∃ v : RustSlice u64,
      big_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v ∧
      v.val.size = 0 := by
  obtain ⟨v, hv, hsz, _⟩ := from_slice_u64_aux numbers
  exact ⟨v, hv, by rw [hsz, hempty]⟩

end Big_endian_from_slice_u64Obligations
