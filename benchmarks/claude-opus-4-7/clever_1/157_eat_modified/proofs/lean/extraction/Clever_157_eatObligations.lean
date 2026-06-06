-- Companion obligations file for the `clever_157_eat` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs are filled in below by a master reduction lemma `eat_take` / `eat_skip` that
-- splits on the `remaining ≥ need` branch.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_157_eat

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_157_eatObligations

/-! ## RustM helper. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-! ## Numeric helper lemmas (u64 partial-operator discharge) -/

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl

/-- `x +? y = pure (x + y)` when `x.toNat + y.toNat` fits in `u64`. -/
private theorem add_pure (x y : u64) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x +? y : RustM u64) = pure (x + y) := by
  show (rust_primitives.ops.arith.Add.add x y : RustM u64) = pure (x + y)
  show (if BitVec.uaddOverflow x.toBitVec y.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x + y)) = _
  have h_no : ¬ UInt64.addOverflow x y := by
    rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow x.toBitVec y.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- `x -? y = pure (x - y)` when `y.toNat ≤ x.toNat`. -/
private theorem sub_pure (x y : u64) (h : y.toNat ≤ x.toNat) :
    (x -? y : RustM u64) = pure (x - y) := by
  show (rust_primitives.ops.arith.Sub.sub x y : RustM u64) = pure (x - y)
  show (if BitVec.usubOverflow x.toBitVec y.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x - y)) = _
  have h_no : ¬ UInt64.subOverflow x y := by
    rw [UInt64.subOverflow_iff]; omega
  have h_bv : BitVec.usubOverflow x.toBitVec y.toBitVec = false := by
    simpa [UInt64.subOverflow] using h_no
  rw [h_bv]; rfl

/-- toNat after an addition that fits. -/
private theorem add_toNat (x y : u64) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := UInt64.toNat_add_of_lt h

/-- toNat after a subtraction that doesn't underflow. -/
private theorem sub_toNat (x y : u64) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := UInt64.toNat_sub_of_le' h

/-! ## Output-shape: a fixed 2-element `Vec u64`. -/

/-- The 2-element output `Vec u64`. -/
private def pairVec (a b : u64) : alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨#[a, b], by show (2 : Nat) < USize64.size; decide⟩

private theorem pairVec_size (a b : u64) : (pairVec a b).val.size = 2 := rfl
private theorem pairVec_getElem_0 (a b : u64) (h : 0 < (pairVec a b).val.size) :
    (pairVec a b).val[0]'h = a := rfl
private theorem pairVec_getElem_1 (a b : u64) (h : 1 < (pairVec a b).val.size) :
    (pairVec a b).val[1]'h = b := rfl

/-! ## Master reduction: `eat` evaluates by branch. -/

/-- Reduce `eat` in the take branch (`need ≤ remaining`). -/
private theorem eat_take
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2 ^ 64)
    (h_ge : need.toNat ≤ remaining.toNat) :
    clever_157_eat.eat number need remaining
      = RustM.ok (pairVec (number + need) (remaining - need)) := by
  -- Reduce the operations along the take path to pure ones.
  have h_add : (number +? need : RustM u64) = pure (number + need) :=
    add_pure number need h_nn
  have h_sub : (remaining -? need : RustM u64) = pure (remaining - need) :=
    sub_pure remaining need h_ge
  have h_ge_cmp : (remaining >=? need : RustM Bool) = pure true := by
    show (rust_primitives.cmp.ge remaining need : RustM Bool) = pure true
    show (pure (decide (remaining ≥ need)) : RustM Bool) = pure true
    have h_dec : decide (remaining ≥ need) = true := by
      apply decide_eq_true_iff.mpr
      show need ≤ remaining
      rw [UInt64.le_iff_toNat_le]; exact h_ge
    rw [h_dec]
  -- New-vec for the initial empty result.
  let init_vec : alloc.vec.Vec u64 alloc.alloc.Global :=
    ⟨(List.nil : List u64).toArray, by decide⟩
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk
                  : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
              = RustM.ok init_vec := rfl
  -- Unfold and step through.
  unfold clever_157_eat.eat
  rw [h_new]
  simp only [RustM_ok_bind]
  rw [h_ge_cmp]
  simp only [pure_bind, ↓reduceIte]
  rw [h_add]
  simp only [pure_bind]
  rw [h_sub]
  simp only [pure_bind]
  -- Now reduce unsize + extend_from_slice on the 2-element chunk.
  have h_unsize :
      (rust_primitives.unsize
            (RustArray.ofVec (n := (2 : usize)) #v[number + need, remaining - need])
          : RustM (rust_primitives.sequence.Seq u64))
        = RustM.ok ⟨#[number + need, remaining - need],
                    by show (2 : Nat) < USize64.size; decide⟩ := rfl
  rw [h_unsize]
  simp only [RustM_ok_bind]
  have h_app_size :
      init_vec.val.size + (#[number + need, remaining - need] : Array u64).size
        < USize64.size := by
    show 0 + 2 < USize64.size
    decide
  have h_ext :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global init_vec
            ⟨#[number + need, remaining - need],
              by show (2 : Nat) < USize64.size; decide⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (pairVec (number + need) (remaining - need)) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl
  rw [h_ext]
  rfl

/-- Reduce `eat` in the skip branch (`remaining < need`). -/
private theorem eat_skip
    (number need remaining : u64)
    (h_nr : number.toNat + remaining.toNat < 2 ^ 64)
    (h_lt : remaining.toNat < need.toNat) :
    clever_157_eat.eat number need remaining
      = RustM.ok (pairVec (number + remaining) 0) := by
  have h_add : (number +? remaining : RustM u64) = pure (number + remaining) :=
    add_pure number remaining h_nr
  have h_ge_cmp : (remaining >=? need : RustM Bool) = pure false := by
    show (rust_primitives.cmp.ge remaining need : RustM Bool) = pure false
    show (pure (decide (remaining ≥ need)) : RustM Bool) = pure false
    have h_dec : decide (remaining ≥ need) = false := by
      apply decide_eq_false_iff_not.mpr
      show ¬ need ≤ remaining
      rw [UInt64.le_iff_toNat_le]; omega
    rw [h_dec]
  let init_vec : alloc.vec.Vec u64 alloc.alloc.Global :=
    ⟨(List.nil : List u64).toArray, by decide⟩
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk
                  : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
              = RustM.ok init_vec := rfl
  unfold clever_157_eat.eat
  rw [h_new]
  simp only [RustM_ok_bind]
  rw [h_ge_cmp]
  simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [h_add]
  simp only [pure_bind]
  have h_unsize :
      (rust_primitives.unsize
            (RustArray.ofVec (n := (2 : usize)) #v[number + remaining, (0 : u64)])
          : RustM (rust_primitives.sequence.Seq u64))
        = RustM.ok ⟨#[number + remaining, (0 : u64)],
                    by show (2 : Nat) < USize64.size; decide⟩ := rfl
  rw [h_unsize]
  simp only [RustM_ok_bind]
  have h_app_size :
      init_vec.val.size + (#[number + remaining, (0 : u64)] : Array u64).size
        < USize64.size := by
    show 0 + 2 < USize64.size
    decide
  have h_ext :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global init_vec
            ⟨#[number + remaining, (0 : u64)],
              by show (2 : Nat) < USize64.size; decide⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (pairVec (number + remaining) 0) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl
  rw [h_ext]
  rfl

/-! ## Contract clauses for `eat`. -/

/-- Length: the returned vector always has exactly two elements.
    Corresponds to Rust proptest `length_is_two`. -/
theorem eat_length_is_two
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      v.val.size = 2 := by
  by_cases h_ge : need.toNat ≤ remaining.toNat
  · refine ⟨pairVec (number + need) (remaining - need),
            eat_take number need remaining h_nn h_ge,
            pairVec_size _ _⟩
  · have h_lt : remaining.toNat < need.toNat := Nat.lt_of_not_le h_ge
    refine ⟨pairVec (number + remaining) 0,
            eat_skip number need remaining h_nr h_lt,
            pairVec_size _ _⟩

/-- Conservation: the two output slots sum to `number + remaining`. -/
theorem eat_conservation
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size) (h1 : 1 < v.val.size),
        (v.val[0]'h0).toNat + (v.val[1]'h1).toNat
          = number.toNat + remaining.toNat := by
  by_cases h_ge : need.toNat ≤ remaining.toNat
  · refine ⟨pairVec (number + need) (remaining - need),
            eat_take number need remaining h_nn h_ge, ?_, ?_, ?_⟩
    · show 0 < 2; decide
    · show 1 < 2; decide
    · rw [pairVec_getElem_0, pairVec_getElem_1]
      rw [add_toNat _ _ h_nn, sub_toNat _ _ h_ge]
      omega
  · have h_lt : remaining.toNat < need.toNat := Nat.lt_of_not_le h_ge
    refine ⟨pairVec (number + remaining) 0,
            eat_skip number need remaining h_nr h_lt, ?_, ?_, ?_⟩
    · show 0 < 2; decide
    · show 1 < 2; decide
    · rw [pairVec_getElem_0, pairVec_getElem_1]
      rw [add_toNat _ _ h_nr, u64_zero_toNat]

/-- Monotonicity in the first slot: `number ≤ r[0]`. -/
theorem eat_first_at_least_number
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size),
        number.toNat ≤ (v.val[0]'h0).toNat := by
  by_cases h_ge : need.toNat ≤ remaining.toNat
  · refine ⟨pairVec (number + need) (remaining - need),
            eat_take number need remaining h_nn h_ge, ?_, ?_⟩
    · show 0 < 2; decide
    · rw [pairVec_getElem_0, add_toNat _ _ h_nn]
      omega
  · have h_lt : remaining.toNat < need.toNat := Nat.lt_of_not_le h_ge
    refine ⟨pairVec (number + remaining) 0,
            eat_skip number need remaining h_nr h_lt, ?_, ?_⟩
    · show 0 < 2; decide
    · rw [pairVec_getElem_0, add_toNat _ _ h_nr]
      omega

/-- Bounded appetite: `r[0] - number ≤ need`. -/
theorem eat_diff_le_need
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size),
        (v.val[0]'h0).toNat - number.toNat ≤ need.toNat := by
  by_cases h_ge : need.toNat ≤ remaining.toNat
  · refine ⟨pairVec (number + need) (remaining - need),
            eat_take number need remaining h_nn h_ge, ?_, ?_⟩
    · show 0 < 2; decide
    · rw [pairVec_getElem_0, add_toNat _ _ h_nn]
      omega
  · have h_lt : remaining.toNat < need.toNat := Nat.lt_of_not_le h_ge
    refine ⟨pairVec (number + remaining) 0,
            eat_skip number need remaining h_nr h_lt, ?_, ?_⟩
    · show 0 < 2; decide
    · rw [pairVec_getElem_0, add_toNat _ _ h_nr]
      omega

/-- Maximality: `r[0] = number + need ∨ r[1] = 0`. -/
theorem eat_sated_or_finished
    (number need remaining : u64)
    (h_nn : number.toNat + need.toNat < 2^64)
    (h_nr : number.toNat + remaining.toNat < 2^64) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_157_eat.eat number need remaining = RustM.ok v ∧
      ∃ (h0 : 0 < v.val.size) (h1 : 1 < v.val.size),
        (v.val[0]'h0).toNat = number.toNat + need.toNat ∨
        (v.val[1]'h1).toNat = 0 := by
  by_cases h_ge : need.toNat ≤ remaining.toNat
  · refine ⟨pairVec (number + need) (remaining - need),
            eat_take number need remaining h_nn h_ge, ?_, ?_, ?_⟩
    · show 0 < 2; decide
    · show 1 < 2; decide
    · left
      rw [pairVec_getElem_0, add_toNat _ _ h_nn]
  · have h_lt : remaining.toNat < need.toNat := Nat.lt_of_not_le h_ge
    refine ⟨pairVec (number + remaining) 0,
            eat_skip number need remaining h_nr h_lt, ?_, ?_, ?_⟩
    · show 0 < 2; decide
    · show 1 < 2; decide
    · right
      rw [pairVec_getElem_1, u64_zero_toNat]

end Clever_157_eatObligations
