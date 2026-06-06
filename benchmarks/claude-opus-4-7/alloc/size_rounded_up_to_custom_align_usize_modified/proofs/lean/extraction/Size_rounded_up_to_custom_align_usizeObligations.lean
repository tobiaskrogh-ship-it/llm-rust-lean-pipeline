-- Companion obligations file for the `size_rounded_up_to_custom_align_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import size_rounded_up_to_custom_align_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Size_rounded_up_to_custom_align_usizeObligations

/-- Precondition fragment: `align` is a power of two. Powers of two are exactly
    the legal alignments enumerated by the Rust property tests (`cases()` ranges
    `align = 1usize << shift` over every `shift in 0..usize::BITS`). A power of
    two is `≥ 1`, so this also discharges the `align -? 1` no-underflow side
    condition. The companion precondition — `size + (align - 1)` does not
    overflow `usize` (documented `Layout` invariant; the implementation
    adds/subtracts unchecked) — is carried as the separate hypothesis
    `size.toNat + (align.toNat - 1) < 2 ^ 64`. -/
def IsPow2 (a : usize) : Prop := ∃ k : Nat, a.toNat = 2 ^ k

/-- Definitional unfolding of the partial `usize` addition (the `add_one`
    `hax_add_def_u8` trick, transposed to `USize64`): `x +? y` is, by `rfl`,
    the overflow-guarded `if`. -/
private theorem hax_add_def_usize (x y : usize) :
    x +? y = if USize64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-- Definitional unfolding of the partial `usize` subtraction. -/
private theorem hax_sub_def_usize (x y : usize) :
    x -? y = if USize64.subOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl

/-- Bridge: `USize64` bitwise-and projects through to `Nat.land` of the
    `toNat`s. `USize64.land a b := ⟨a.toBitVec &&& b.toBitVec⟩` and
    `toNat := ·.toBitVec.toNat`, so this is `BitVec.toNat_and` under the
    structure projection. -/
private theorem usize_toNat_and (a b : usize) :
    (a &&& b).toNat = a.toNat &&& b.toNat := by
  have h : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_and]

/-- Bridge: `USize64` complement projects through to the 64-bit `BitVec`
    complement value `2^64 - 1 - n`. -/
private theorem usize_toNat_compl (a : usize) :
    (~~~ a).toNat = 2 ^ 64 - 1 - a.toNat := by
  have h : (~~~ a).toBitVec = ~~~ a.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_not]

/-- Power-of-two bitmask round-down identity at the `Nat` level: masking off
    the low `k` bits (anding with the 64-bit high mask `2^64 - 2^k`) of any
    value `< 2^64` equals clearing the low `k` bits, i.e.
    `2^k * (sn / 2^k)`. Proved by bit extensionality
    (`Nat.eq_of_testBit_eq`): bit `i` of the result is `sn`'s bit `i` when
    `k ≤ i` and `0` otherwise; the only subtlety is that a set bit of `sn`
    forces `i < 64`, discharged from `sn < 2^64` via
    `Nat.ge_two_pow_of_testBit`. -/
private theorem mask_clear (sn k : Nat) (hsn : sn < 2 ^ 64) (hk : k ≤ 64) :
    sn &&& (2 ^ 64 - 2 ^ k) = 2 ^ k * (sn / 2 ^ k) := by
  have hfac : (2 : Nat) ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    have hpow : (2 : Nat) ^ (64 - k) * 2 ^ k = 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.sub_mul, Nat.one_mul, hpow]
  rw [hfac]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
             Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow, ge_iff_le]
  by_cases hkj : k ≤ j
  · have d1 : decide (k ≤ j) = true := decide_eq_true hkj
    have d3 : j - k + k = j := by omega
    rw [d1, d3]
    simp only [Bool.true_and]
    by_cases hb : sn.testBit j = true
    · have hj : j < 64 := by
        have hge2 : sn ≥ 2 ^ j := Nat.ge_two_pow_of_testBit hb
        have hlt2 : (2 : Nat) ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt hge2 hsn
        exact (Nat.pow_lt_pow_iff_right (by decide)).mp hlt2
      rw [hb]
      simp only [Bool.true_and, decide_eq_true_eq]
      omega
    · simp only [Bool.not_eq_true] at hb
      simp [hb]
  · have d1 : decide (k ≤ j) = false := decide_eq_false hkj
    rw [d1]
    simp only [Bool.false_and, Bool.and_false]

/-- The exact `Nat` value of the rounded size, under the invariant. Combines
    the partial-operator `toNat` bridges (`toNat_sub_of_le`,
    `toNat_add_of_lt`), the complement bridge `usize_toNat_compl`
    (`~~~(a-1)` ↦ `2^64 - 2^k`), and the `mask_clear` round-down identity. -/
private theorem result_toNat (s a : usize) (k : Nat)
    (hk : a.toNat = 2 ^ k)
    (hnof : s.toNat + (a.toNat - 1) < 2 ^ 64) :
    ((s + (a - 1)) &&& ~~~(a - 1)).toNat
      = 2 ^ k * ((s.toNat + (2 ^ k - 1)) / 2 ^ k) := by
  have hk64 : k ≤ 64 := by
    have hlt : a.toNat < 2 ^ 64 := a.toNat_lt
    rw [hk] at hlt
    have hk' : k < 64 := (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
    omega
  have hone : (1 : usize).toNat = 1 := by decide
  have hle1 : (1 : usize) ≤ a := by
    rw [USize64.le_iff_toNat_le, hone, hk]
    exact Nat.one_le_two_pow
  have ham1 : (a - (1 : usize)).toNat = 2 ^ k - 1 := by
    rw [USize64.toNat_sub_of_le _ _ hle1, hone, hk]
  have hbnd : s.toNat + (a - (1 : usize)).toNat < 2 ^ 64 := by
    rw [ham1]
    have hz : a.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  have hSeq : (s + (a - 1)).toNat = s.toNat + (2 ^ k - 1) := by
    rw [USize64.toNat_add_of_lt hbnd, ham1]
  have hCeq : (~~~ (a - (1 : usize))).toNat = 2 ^ 64 - 2 ^ k := by
    rw [usize_toNat_compl, ham1]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk64
    omega
  have hsn' : s.toNat + (2 ^ k - 1) < 2 ^ 64 := by
    have hz : a.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  rw [usize_toNat_and, hSeq, hCeq]
  exact mask_clear (s.toNat + (2 ^ k - 1)) k hsn' hk64

/-- Functional correctness / postcondition in closed form. Under the function's
    precondition (`align` a power of two and `size + (align - 1)` not
    overflowing `usize`), the call succeeds and returns exactly
    `(size + (align - 1)) & ~(align - 1)`. The concrete `rounds_up` anchor test
    is the input/output instantiation of this clause, and the three
    postcondition projections below all follow from it. The instructions list
    "result equals the closed form" as a contract clause that must be kept. -/
theorem size_rounded_up_to_custom_align_spec (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align size align
      = RustM.ok ((size + (align - 1)) &&& (~~~(align - 1))) := by
  obtain ⟨k, hk⟩ := hpow
  have hone : (1 : usize).toNat = 1 := by decide
  have hsub_no : ¬ USize64.subOverflow align (1 : usize) := by
    rw [USize64.subOverflow_iff, hone, hk]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hle1 : (1 : usize) ≤ align := by
    rw [USize64.le_iff_toNat_le, hone, hk]
    exact Nat.one_le_two_pow
  have ham1 : (align - (1 : usize)).toNat = 2 ^ k - 1 := by
    rw [USize64.toNat_sub_of_le _ _ hle1, hone, hk]
  have hadd_no : ¬ USize64.addOverflow size (align - (1 : usize)) := by
    rw [USize64.addOverflow_iff, ham1]
    have hz : align.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  unfold size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align
  rw [hax_sub_def_usize, if_neg hsub_no]
  simp only [pure_bind]
  rw [hax_add_def_usize, if_neg hadd_no]
  simp only [pure_bind]
  rfl

/-- Totality / no-panic under the precondition. The Rust source documents that
    the `unchecked_sub`/`unchecked_add` intrinsics cannot overflow given the
    `Layout` invariants, so under the precondition the function never panics.
    Every property test only feeds valid `(size, align)` pairs from `cases()`,
    implicitly asserting this no-failure clause. -/
theorem size_rounded_up_to_custom_align_total (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    ∃ r : usize,
      size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align size align
        = RustM.ok r :=
  ⟨_, size_rounded_up_to_custom_align_spec size align hpow hnof⟩

/-- Postcondition (1/3) — Rust test `result_is_multiple_of_align`: the result
    is a multiple of `align` (`r % align == 0`). -/
theorem size_rounded_up_to_custom_align_result_is_multiple_of_align
    (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    ∃ r : usize,
      size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align size align
        = RustM.ok r
      ∧ r.toNat % align.toNat = 0 := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, size_rounded_up_to_custom_align_spec size align ⟨k, hk⟩ hnof, ?_⟩
  show ((size + (align - 1)) &&& ~~~(align - 1)).toNat % align.toNat = 0
  rw [result_toNat size align k hk hnof, hk]
  exact Nat.mul_mod_right _ _

/-- Postcondition (2/3) — Rust test `result_is_at_least_size`: rounding is
    upward, the result is never below `size` (`r >= size`). -/
theorem size_rounded_up_to_custom_align_result_is_at_least_size
    (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    ∃ r : usize,
      size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align size align
        = RustM.ok r
      ∧ size.toNat ≤ r.toNat := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, size_rounded_up_to_custom_align_spec size align ⟨k, hk⟩ hnof, ?_⟩
  show size.toNat ≤ ((size + (align - 1)) &&& ~~~(align - 1)).toNat
  rw [result_toNat size align k hk hnof]
  have hdm := Nat.div_add_mod (size.toNat + (2 ^ k - 1)) (2 ^ k)
  have hmod : (size.toNat + (2 ^ k - 1)) % 2 ^ k < 2 ^ k :=
    Nat.mod_lt _ (Nat.two_pow_pos k)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- Postcondition (3/3) — Rust test `result_is_smallest_such_multiple`: the
    result is the *least* multiple of `align` that is `≥ size`, i.e. the gap
    above `size` is strictly less than `align` (Rust `r - size < align`, stated
    here as the underflow-free equivalent `r < size + align`). Independent of
    (1) and (2); together the three pin the return value uniquely. -/
theorem size_rounded_up_to_custom_align_result_is_smallest_such_multiple
    (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    ∃ r : usize,
      size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align size align
        = RustM.ok r
      ∧ r.toNat < size.toNat + align.toNat := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, size_rounded_up_to_custom_align_spec size align ⟨k, hk⟩ hnof, ?_⟩
  show ((size + (align - 1)) &&& ~~~(align - 1)).toNat < size.toNat + align.toNat
  rw [result_toNat size align k hk hnof, hk]
  have hdm := Nat.div_add_mod (size.toNat + (2 ^ k - 1)) (2 ^ k)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- Concrete anchor (`rounds_up`, 1/6): size 9, align 4 ↦ 12. -/
theorem size_rounded_up_to_custom_align_example_9_4 :
    size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align 9 4
      = RustM.ok 12 := by
  refine (size_rounded_up_to_custom_align_spec 9 4 ⟨2, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete anchor (`rounds_up`, 2/6): size 6, align 4 ↦ 8. -/
theorem size_rounded_up_to_custom_align_example_6_4 :
    size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align 6 4
      = RustM.ok 8 := by
  refine (size_rounded_up_to_custom_align_spec 6 4 ⟨2, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete anchor (`rounds_up`, 3/6): an already-aligned size 12, align 4 is
    unchanged (↦ 12). -/
theorem size_rounded_up_to_custom_align_example_12_4 :
    size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align 12 4
      = RustM.ok 12 := by
  refine (size_rounded_up_to_custom_align_spec 12 4 ⟨2, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete anchor (`rounds_up`, 4/6): size 1, align 8 ↦ 8. -/
theorem size_rounded_up_to_custom_align_example_1_8 :
    size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align 1 8
      = RustM.ok 8 := by
  refine (size_rounded_up_to_custom_align_spec 1 8 ⟨3, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete anchor (`rounds_up`, 5/6): size 0, align `1 << 20 = 1048576` ↦ 0
    (zero is a multiple of every alignment). -/
theorem size_rounded_up_to_custom_align_example_0_big :
    size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align 0 1048576
      = RustM.ok 0 := by
  refine (size_rounded_up_to_custom_align_spec 0 1048576 ⟨20, by decide⟩ (by decide)).trans ?_
  rfl

/-- Concrete anchor (`rounds_up`, 6/6): align 1 is the identity (size 13 ↦ 13). -/
theorem size_rounded_up_to_custom_align_example_13_1 :
    size_rounded_up_to_custom_align_usize.size_rounded_up_to_custom_align 13 1
      = RustM.ok 13 := by
  refine (size_rounded_up_to_custom_align_spec 13 1 ⟨0, by decide⟩ (by decide)).trans ?_
  rfl

end Size_rounded_up_to_custom_align_usizeObligations
