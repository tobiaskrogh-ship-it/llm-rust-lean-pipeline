-- Companion obligations file for the `is_size_align_valid_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import is_size_align_valid_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Is_size_align_valid_usizeObligations

open is_size_align_valid_usize

-- Bit identity: 2^k AND (2^k - 1) = 0 at the Nat level.
private theorem nat_and_pow2_sub_one (k : Nat) : (2^k) &&& (2^k - 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hik : i = k
  · subst hik
    simp [Nat.testBit_two_pow_self, Nat.testBit_two_pow_sub_one]
  · simp [Nat.testBit_two_pow_of_ne (Ne.symm hik)]

/-- Equational form of `is_power_of_two_usize` when `align ≠ 0`: the function
    succeeds and returns whether `align &&& (align - 1) = 0`. -/
private theorem is_power_of_two_usize_eq_of_ne_zero (align : usize) (h : align ≠ 0) :
    is_power_of_two_usize align = RustM.ok (decide ((align &&& (align - 1)) = 0)) := by
  unfold is_power_of_two_usize
  -- The subtraction does not overflow: from `align ≠ 0` we have `align.toNat ≥ 1`.
  have h_toNat_ne : align.toNat ≠ 0 := by
    intro h0
    apply h
    apply USize64.toNat_inj.mp
    rw [h0]; rfl
  have h_no_overflow : ¬ BitVec.usubOverflow align.toBitVec (1 : usize).toBitVec = true := by
    show ¬ USize64.subOverflow align 1 = true
    rw [USize64.subOverflow_iff]
    have : (1 : usize).toNat = 1 := rfl
    omega
  show (do
    let b1 ← rust_primitives.cmp.ne align (0 : usize)
    let s ← rust_primitives.ops.arith.Sub.sub align (1 : usize)
    let b2 ← (fun a b => pure (a &&& b)) align s
    let b3 ← rust_primitives.cmp.eq b2 (0 : usize)
    rust_primitives.hax.logical_op.and b1 b3) = _
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.ops.arith.Sub.sub,
             rust_primitives.hax.logical_op.and,
             h_no_overflow,
             pure_bind, bind_pure_comp]
  have h_neq : (align != (0 : usize)) = true := by
    rw [bne_iff_ne]; exact h
  rw [h_neq]
  rfl

/-- Nat-level "is a power of two" predicate. Mirrors the Rust standard
    library's `usize::is_power_of_two()` — `0` is *not* a power of two
    (no `k` satisfies `2^k = 0`). -/
private def IsPowerOfTwoNat (n : Nat) : Prop := ∃ k : Nat, n = 2 ^ k

/-- Overflow-safe `Nat`-level oracle for the documented postcondition:
    `size` rounded up to the next multiple of `align` does not exceed
    `isize::MAX = 2^63 - 1`. Mirrors the property test's `u128` oracle
    `((size + a - 1) / a) * a ≤ isize::MAX`. Only meaningful when
    `align ≥ 1` (always true when `align` is a power of two). -/
private def RoundsUpFits (size align : Nat) : Prop :=
  (size + align - 1) / align * align ≤ 2 ^ 63 - 1

/-- A power-of-two `usize` is nonzero. -/
private theorem usize_ne_zero_of_pow2 (align : usize)
    (h : IsPowerOfTwoNat align.toNat) : align ≠ 0 := by
  obtain ⟨k, hk⟩ := h
  intro heq
  have : align.toNat = 0 := by rw [heq]; rfl
  rw [this] at hk
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  omega

/-- For `align` a power of two (i.e. `align.toNat = 2^k`), the bitwise
    expression `align &&& (align - 1)` equals `0` as a `usize`. -/
private theorem and_sub_one_pow2_usize (align : usize)
    (h : IsPowerOfTwoNat align.toNat) :
    align &&& (align - 1) = 0 := by
  obtain ⟨k, hk⟩ := h
  -- hk : align.toNat = 2^k
  have h_lt : align.toNat < 2^64 := align.toNat_lt
  have hk64 : k < 64 := by
    rw [hk] at h_lt
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_lt
  have h_ne_zero : align ≠ 0 :=
    usize_ne_zero_of_pow2 align ⟨k, hk⟩
  have h_toNat_pos : 1 ≤ align.toNat := by
    rw [hk]; exact Nat.one_le_two_pow
  -- Use toNat_inj to reduce to Nat-level equality.
  apply USize64.toNat_inj.mp
  -- `(align &&& (align - 1)).toNat = align.toNat &&& (align - 1).toNat`
  show (align &&& (align - 1)).toNat = (0 : usize).toNat
  -- Unfold via toBitVec.
  rw [show (align &&& (align - 1)).toNat = (align.toBitVec &&& (align - 1).toBitVec).toNat from rfl,
      BitVec.toNat_and]
  -- `(align - 1).toNat = align.toNat - 1` (no underflow)
  have h_sub_toNat : (align - 1).toNat = align.toNat - 1 := by
    rw [USize64.toNat_sub_of_le]
    · show align.toNat - (1 : usize).toNat = align.toNat - 1
      have : (1 : usize).toNat = 1 := rfl
      rw [this]
    · show (1 : usize) ≤ align
      rw [USize64.le_iff_toNat_le]
      have : (1 : usize).toNat = 1 := rfl
      omega
  show align.toBitVec.toNat &&& (align - 1).toBitVec.toNat = (0 : usize).toNat
  rw [show align.toBitVec.toNat = align.toNat from rfl,
      show (align - 1).toBitVec.toNat = (align - 1).toNat from rfl,
      h_sub_toNat, hk,
      show (0 : usize).toNat = 0 from rfl]
  -- Now: 2^k &&& (2^k - 1) = 0
  exact nat_and_pow2_sub_one k

/-- When `align` is a power of two, `is_power_of_two_usize align` returns
    `RustM.ok true`. -/
private theorem is_power_of_two_usize_of_pow2 (align : usize)
    (h : IsPowerOfTwoNat align.toNat) :
    is_power_of_two_usize align = RustM.ok true := by
  have h_ne_zero : align ≠ 0 := usize_ne_zero_of_pow2 align h
  have h_and : align &&& (align - 1) = 0 := and_sub_one_pow2_usize align h
  rw [is_power_of_two_usize_eq_of_ne_zero align h_ne_zero, h_and]
  simp

/-- When `align` is a power of two, `align.toNat ≤ 2^63`. -/
private theorem usize_le_pow63_of_pow2 (align : usize)
    (h : IsPowerOfTwoNat align.toNat) : align.toNat ≤ 2 ^ 63 := by
  obtain ⟨k, hk⟩ := h
  have h_lt : align.toNat < 2^64 := align.toNat_lt
  have hk64 : k < 64 := by
    rw [hk] at h_lt
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_lt
  rw [hk]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : k ≤ 63)

/-- Key Nat-level equivalence: for any `k ≤ 63`, `(size + 2^k - 1) / 2^k * 2^k ≤ 2^63 - 1`
    iff `size ≤ 2^63 - 2^k`. -/
private theorem rounds_up_fits_iff_le (size k : Nat) (hk : k ≤ 63) :
    (size + 2^k - 1) / 2^k * 2^k ≤ 2^63 - 1 ↔ size ≤ 2^63 - 2^k := by
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  have h_div_263 : 2^63 / 2^k = 2^(63 - k) := by
    rw [Nat.pow_div hk (by decide : 0 < 2)]
  have h_mul_back : 2^(63 - k) * 2^k = 2^63 := by
    rw [← Nat.pow_add]
    congr 1; omega
  have h_2k_le : 2^k ≤ 2^63 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  refine ⟨?_, ?_⟩
  · -- Forward: contrapositive
    intro h
    rcases Nat.lt_or_ge size (2^63 - 2^k + 1) with hgt | hgt
    · omega
    · -- hgt : 2^63 - 2^k + 1 ≤ size, i.e., size > 2^63 - 2^k
      exfalso
      have hbig : 2^63 ≤ size + 2^k - 1 := by omega
      have hdiv : 2^63 / 2^k ≤ (size + 2^k - 1) / 2^k :=
        Nat.div_le_div_right hbig
      rw [h_div_263] at hdiv
      have hmul : 2^(63 - k) * 2^k ≤ (size + 2^k - 1) / 2^k * 2^k :=
        Nat.mul_le_mul_right (2^k) hdiv
      rw [h_mul_back] at hmul
      omega
  · intro h
    have h1 : size + 2^k - 1 ≤ 2^63 - 1 := by omega
    have h2 : (size + 2^k - 1) / 2^k * 2^k ≤ size + 2^k - 1 := Nat.div_mul_le_self _ _
    omega

/-- When `align` is a power of two, `max_size_for_align align` returns
    `RustM.ok ((2^63 : usize) - align)`. -/
private theorem max_size_for_align_of_pow2 (align : usize)
    (h : IsPowerOfTwoNat align.toNat) :
    max_size_for_align align =
      RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  have h_align_le : align.toNat ≤ 2 ^ 63 := usize_le_pow63_of_pow2 align h
  have h_const : (9223372036854775808 : usize).toNat = 2 ^ 63 := by rfl
  have h_no_overflow : ¬ BitVec.usubOverflow (9223372036854775808 : usize).toBitVec align.toBitVec = true := by
    show ¬ USize64.subOverflow (9223372036854775808 : usize) align = true
    rw [USize64.subOverflow_iff]
    rw [h_const]
    omega
  show (if BitVec.usubOverflow (9223372036854775808 : usize).toBitVec align.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure ((9223372036854775808 : usize) - align))
       = _
  rw [if_neg h_no_overflow]
  rfl

/-- Failure-condition clause (alignment): when `align` is not a power of
    two, the function rejects regardless of `size`.

    Captures the property test `non_power_of_two_align_always_rejected`:
    `Alignment::new(align)` is `None` unless `align` is a power of two,
    so `is_size_align_valid(size, align) == false` for every `size`.
    The `align = 0` corner is subsumed (0 is not a power of two — the
    short-circuit `align != 0` guard in `is_power_of_two_usize` rejects it).
    A buggy implementation that accepted any odd or composite alignment,
    or that panicked on `align = 0`, would falsify this. -/
theorem rejects_non_power_of_two (size align : usize)
    (h : ¬ IsPowerOfTwoNat align.toNat) :
    is_size_align_valid size align = RustM.ok false := by
  sorry

/-- Equational form of `is_size_align_valid` under the power-of-two hypothesis:
    the function returns `true` iff `size ≤ 2^63 - align`. -/
private theorem is_size_align_valid_pow2_eq (size align : usize)
    (h_pow2 : IsPowerOfTwoNat align.toNat) :
    is_size_align_valid size align =
      RustM.ok (! decide (size > ((9223372036854775808 : usize) - align))) := by
  unfold is_size_align_valid
  rw [is_power_of_two_usize_of_pow2 align h_pow2,
      max_size_for_align_of_pow2 align h_pow2]
  -- Reduce remaining computation
  simp only [rust_primitives.hax.logical_op.not, rust_primitives.cmp.gt]
  by_cases hgt : decide (size > ((9223372036854775808 : usize) - align)) = true
  · simp [hgt]
  · simp only [Bool.not_eq_true] at hgt
    simp [hgt]

/-- Postcondition (accept): when `align` is a power of two and `size`
    rounded up to a multiple of `align` fits within `isize::MAX`, the
    function returns `true`.

    Captures the "true" half of `power_of_two_align_matches_round_up_contract`.
    A buggy implementation that rejected a valid `(size, align)` pair
    inside the rounded-up envelope (e.g. an off-by-one on the size
    threshold, or rejecting `size = 0`) would falsify this. -/
theorem accepts_when_pow2_and_fits (size align : usize)
    (h_pow2 : IsPowerOfTwoNat align.toNat)
    (h_fits : RoundsUpFits size.toNat align.toNat) :
    is_size_align_valid size align = RustM.ok true := by
  obtain ⟨k, hk⟩ := h_pow2
  have h_lt : align.toNat < 2^64 := align.toNat_lt
  have hk64 : k < 64 := by
    rw [hk] at h_lt
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_lt
  have hk63 : k ≤ 63 := by omega
  have h_align_le : align.toNat ≤ 2 ^ 63 :=
    usize_le_pow63_of_pow2 align ⟨k, hk⟩
  have h_const : (9223372036854775808 : usize).toNat = 2 ^ 63 := rfl
  have h_sub_toNat : ((9223372036854775808 : usize) - align).toNat
      = 2 ^ 63 - align.toNat := by
    rw [USize64.toNat_sub_of_le]
    · rw [h_const]
    · rw [USize64.le_iff_toNat_le, h_const]; exact h_align_le
  have h_size_le : size.toNat ≤ 2^63 - align.toNat := by
    have h_iff := (rounds_up_fits_iff_le size.toNat k hk63).mp
    unfold RoundsUpFits at h_fits
    rw [hk] at h_fits
    have := h_iff h_fits
    rw [hk]; exact this
  have h_not_gt :
      decide (size > ((9223372036854775808 : usize) - align)) = false := by
    rw [decide_eq_false_iff_not]
    intro hgt
    -- size > x means x < size
    have hgt' : ((9223372036854775808 : usize) - align).toNat < size.toNat := by
      have := (USize64.lt_iff_toNat_lt
                 (a := ((9223372036854775808 : usize) - align)) (b := size)).mp hgt
      exact this
    rw [h_sub_toNat] at hgt'
    omega
  rw [is_size_align_valid_pow2_eq size align ⟨k, hk⟩, h_not_gt]
  rfl

/-- Postcondition (reject): when `align` is a power of two but `size`
    rounded up to a multiple of `align` exceeds `isize::MAX`, the
    function returns `false`.

    Captures the "false" half of `power_of_two_align_matches_round_up_contract`.
    A buggy implementation that accepted `(size, align)` whose rounded-up
    layout would overflow `isize::MAX` (e.g. comparing against `usize::MAX`
    or skipping the size check) would falsify this. -/
theorem rejects_when_pow2_and_too_big (size align : usize)
    (h_pow2 : IsPowerOfTwoNat align.toNat)
    (h_too_big : ¬ RoundsUpFits size.toNat align.toNat) :
    is_size_align_valid size align = RustM.ok false := by
  sorry

/-- Totality / no-panic: for every `(size, align)` pair the function
    returns a boolean successfully — no panic, no overflow, no error.

    The short-circuit in `is_power_of_two_usize` guards the `x - 1`
    underflow at `x = 0`, and `max_size_for_align`'s `2^63 - align` is
    only evaluated when `align` is a power of two (hence `align ≤ 2^63`).
    Implicit in every property test (each `assert_eq!` presumes the
    function returns). A buggy implementation that ever panicked,
    failed, or overflowed would falsify this. -/
theorem is_size_align_valid_total (size align : usize) :
    ∃ b : Bool, is_size_align_valid size align = RustM.ok b := by
  sorry

end Is_size_align_valid_usizeObligations
