-- Companion obligations file for the `is_size_align_valid_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import is_size_align_valid_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Is_size_align_valid_usizeObligations

open is_size_align_valid_usize

/-! ## Numeric / bit-trick helper lemmas (pure, no monad) -/

/-- `(1 : usize)` has `toNat = 1`. -/
private theorem one_toNat : (1 : usize).toNat = 1 :=
  USize64.toNat_ofNat_of_lt (by decide)

/-- The literal `2^63` constant as a `usize` has `toNat = 9223372036854775808`. -/
private theorem big_toNat :
    ((9223372036854775808 : usize)).toNat = 9223372036854775808 :=
  USize64.toNat_ofNat_of_lt (by decide)

/-- An unsigned subtraction does not underflow whenever the subtrahend is
    `≤` the minuend (at the `Nat` level). -/
private theorem usub_false {x y : usize} (h : y.toNat ≤ x.toNat) :
    BitVec.usubOverflow x.toBitVec y.toBitVec = false := by
  simp only [BitVec.usubOverflow, USize64.toNat_toBitVec, decide_eq_false_iff_not,
             Nat.not_lt]
  exact h

/-- A `usize` that is not `0` has `toNat ≠ 0`. -/
private theorem toNat_ne_zero {n : usize} (h : n ≠ (0 : usize)) : n.toNat ≠ 0 := by
  intro hc
  apply h
  apply USize64.toNat_inj.mp
  rw [hc, USize64.toNat_zero]

/-- Bridge: the `usize` bitwise expression `align &&& (align - 1)` has the
    `Nat` value `align.toNat &&& (align.toNat - 1)` when `align ≠ 0`. -/
private theorem and_pred_toNat {align : usize} (h : align ≠ (0 : usize)) :
    (align &&& (align - 1)).toNat = align.toNat &&& (align.toNat - 1) := by
  have hne' : align.toNat ≠ 0 := toNat_ne_zero h
  have h1le : (1 : usize) ≤ align := by
    rw [USize64.le_iff_toNat_le, one_toNat]
    omega
  have hsub : (align - 1).toNat = align.toNat - 1 := by
    rw [USize64.toNat_sub_of_le align 1 h1le, one_toNat]
  -- unfold the USize64 AND to a BitVec AND, then push `toNat` inside.
  show (USize64.land align (align - 1)).toNat = align.toNat &&& (align.toNat - 1)
  simp only [USize64.land, USize64.toNat, BitVec.toNat_and]
  rw [show (align - 1).toBitVec.toNat = (align - 1).toNat from rfl, hsub]

/-- Core power-of-two characterisation, transported from
    `Nat.and_sub_one_eq_zero_iff_isPowerOfTwo`: for `align ≠ 0`,
    `align & (align - 1) = 0` exactly when `align.toNat` is a power of two. -/
private theorem pow2_iff (align : usize) (hne : align ≠ (0 : usize)) :
    (align &&& (align - 1)) = (0 : usize) ↔ ∃ k : Nat, align.toNat = 2 ^ k := by
  have hne' : align.toNat ≠ 0 := toNat_ne_zero hne
  have hand : (align &&& (align - 1)).toNat = align.toNat &&& (align.toNat - 1) :=
    and_pred_toNat hne
  constructor
  · intro h
    have hN : align.toNat &&& (align.toNat - 1) = 0 := by
      have := congrArg USize64.toNat h
      rw [hand, USize64.toNat_zero] at this
      exact this
    exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hne').mp hN
  · intro h
    have hpow : align.toNat.isPowerOfTwo := h
    have hN : align.toNat &&& (align.toNat - 1) = 0 :=
      (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hne').mpr hpow
    apply USize64.toNat_inj.mp
    rw [hand, USize64.toNat_zero]
    exact hN

/-- If `align.toNat = 2 ^ k` then `align.toNat ≤ 2 ^ 63` (since `align.toNat < 2^64`). -/
private theorem pow2_le {align : usize} {k : Nat} (h : align.toNat = 2 ^ k) :
    align.toNat ≤ 2 ^ 63 := by
  have hlt : align.toNat < 2 ^ 64 := USize64.toNat_lt align
  rw [h] at hlt ⊢
  have hk63 : k ≤ 63 := by
    by_contra hcon
    have h64 : 64 ≤ k := by omega
    have : (2:Nat) ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h64
    omega
  exact Nat.pow_le_pow_right (by decide) hk63

/-- The round-up arithmetic equivalence: for a power-of-two divisor
    `A = 2 ^ k` (`k ≤ 63`, so `A ∣ 2^63`),
    `⌈s / A⌉ * A ≤ 2^63 - 1` exactly when `s ≤ 2^63 - A`.

    This is the bridge between the implementation's subtraction-based
    comparison `size ≤ (2^63 - align)` and the documented round-up
    postcondition `next_multiple_of(size, align) ≤ isize::MAX`. -/
private theorem round_up_le_iff {s A q : Nat} (hA : 0 < A)
    (hq : 2 ^ 63 = A * q) :
    ((s + (A - 1)) / A * A ≤ 2 ^ 63 - 1) ↔ s ≤ 2 ^ 63 - A := by
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso; rw [h, Nat.mul_zero] at hq; exact (Nat.two_pow_pos 63).ne' hq
    · exact h
  have hAq : 0 < A * q := Nat.mul_pos hA hqpos
  have hAle : A ≤ 2 ^ 63 := by rw [hq]; exact Nat.le_mul_of_pos_right A hqpos
  set c := (s + (A - 1)) / A with hc
  have h1 : (c * A ≤ 2 ^ 63 - 1) ↔ c < q := by
    rw [hq]
    constructor
    · intro h
      have hlt : c * A < A * q := by omega
      have hlt' : c * A < q * A := by rw [Nat.mul_comm q A]; exact hlt
      exact (Nat.mul_lt_mul_right hA).mp hlt'
    · intro h
      have hlt' : c * A < q * A := (Nat.mul_lt_mul_right hA).mpr h
      have hlt : c * A < A * q := by rw [Nat.mul_comm A q]; exact hlt'
      omega
  have h2 : (c < q) ↔ s ≤ 2 ^ 63 - A := by
    rw [Nat.lt_iff_le_pred hqpos, hc, Nat.div_le_iff_le_mul_add_pred hA]
    have hmul : A * (q - 1) = 2 ^ 63 - A := by
      rw [Nat.mul_sub_one, ← hq]
    omega
  rw [h1, h2]

/-! ## Evaluation of the extracted `RustM` program -/

/-- `is_power_of_two_usize n` for `n ≠ 0`: the short-circuit guard `n != 0`
    is `true`, the subtraction `n - 1` does not underflow, and the result
    is the bit-trick boolean. -/
private theorem ipot_eval (n : usize) (hn : n ≠ (0 : usize)) :
    is_power_of_two_usize n
      = pure ((n != (0 : usize)) && ((n &&& (n - 1)) == (0 : usize))) := by
  have hn' : n.toNat ≠ 0 := toNat_ne_zero hn
  have h_no : BitVec.usubOverflow n.toBitVec (1 : usize).toBitVec = false := by
    apply usub_false
    rw [one_toNat]; omega
  simp only [is_power_of_two_usize, rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and, rust_primitives.ops.arith.Sub.sub]
  simp [h_no]

/-- `max_size_for_align align` when `align.toNat ≤ 2^63`: the subtraction
    `2^63 - align` does not underflow. -/
private theorem msfa_eval (align : usize) (hle : align.toNat ≤ 2 ^ 63) :
    max_size_for_align align = pure ((9223372036854775808 : usize) - align) := by
  have h_no : BitVec.usubOverflow ((9223372036854775808 : usize)).toBitVec align.toBitVec
              = false := by
    apply usub_false
    rw [big_toNat]
    have : (9223372036854775808 : Nat) = 2 ^ 63 := by norm_num
    omega
  simp only [max_size_for_align, rust_primitives.ops.arith.Sub.sub]
  simp [h_no]

/-- Evaluation of `is_size_align_valid` on a non-power-of-two, non-zero
    alignment: the bit-trick test fails, so the function rejects with
    `false` without ever evaluating `max_size_for_align`. -/
private theorem isav_eval_notpow2 (size align : usize) (hz : align ≠ (0 : usize))
    (hnp : (align &&& (align - 1)) ≠ (0 : usize)) :
    is_size_align_valid size align = RustM.ok false := by
  have hb2 : ((align &&& (align - 1)) == (0 : usize)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact hnp
  have hb1 : (align != (0 : usize)) = true := by
    simp only [bne_iff_ne, ne_eq]; exact hz
  simp only [is_size_align_valid, ipot_eval align hz, rust_primitives.hax.logical_op.not,
             rust_primitives.cmp.gt]
  simp [hb1, hb2]

/-- Evaluation of `is_size_align_valid` on a power-of-two alignment
    (`align ≠ 0`, `align & (align-1) = 0`, `align.toNat ≤ 2^63`): the
    bit-trick test passes, so the result is the size/round-up comparison. -/
private theorem isav_eval_pow2 (size align : usize) (hz : align ≠ (0 : usize))
    (hp : (align &&& (align - 1)) = (0 : usize)) (hle : align.toNat ≤ 2 ^ 63) :
    is_size_align_valid size align
      = (if size > ((9223372036854775808 : usize) - align)
         then RustM.ok false else RustM.ok true) := by
  have hb2 : ((align &&& (align - 1)) == (0 : usize)) = true := by
    simp only [beq_iff_eq]; exact hp
  have hb1 : (align != (0 : usize)) = true := by
    simp only [bne_iff_ne, ne_eq]; exact hz
  simp only [is_size_align_valid, ipot_eval align hz, msfa_eval align hle,
             rust_primitives.hax.logical_op.not, rust_primitives.cmp.gt]
  simp [hb1, hb2]

/-! ## Obligations -/

/-- Contract clause 1 (failure / precondition: invalid alignment is rejected).

    `Layout::from_size_align` requires `align` to be a power of two
    (`Alignment::new(align)` is `None` otherwise — including `align = 0`).
    Whenever `align` is **not** a power of two, `is_size_align_valid` must
    reject the input by returning `false`, *independently of* `size`.

    Captures the property test `non_power_of_two_align_always_rejected`
    and the unit test `rejects_non_power_of_two`. A "power of two" is the
    mathematical predicate `∃ k, align = 2^k`; `0` satisfies its negation.

    STUCK SUB-GOAL (only the `align = 0` instance): `is_size_align_valid
    size 0 = RustM.ok false`. Hax extracts Rust's short-circuit `&&` as the
    *non*-short-circuiting `rust_primitives.hax.logical_op.and`, and the
    `do`-block hoists `(← (align -? 1))` unconditionally. So for `align = 0`
    the extracted `is_power_of_two_usize 0` evaluates `0 -? 1`, which
    underflows to `RustM.fail .integerOverflow`; hence
    `is_size_align_valid size 0 = RustM.fail .integerOverflow ≠ RustM.ok
    false`. The clause is true of the *intended* Rust contract but false of
    the mechanically-extracted function at `align = 0`. The `align ≠ 0`
    case (the substantive content of the clause) is fully proved below.

    STRUCTURAL UNBLOCK: a Hax extraction fix that preserves Rust's
    short-circuit `&&` (lowering `a && b` to a guarded `if a then b else
    false` in `RustM` rather than `logical_op.and (← a) (← b)` with both
    operands force-sequenced) would make `is_power_of_two_usize 0 =
    RustM.ok false` and close this instance in one line. Not fixable
    Lean-side: editing the extracted module is out of scope, and no Lean
    lemma can change what `0 -? 1` evaluates to. -/
theorem is_size_align_valid_non_power_of_two_rejected
    (size align : usize) (h : ¬ ∃ k : Nat, align.toNat = 2 ^ k) :
    is_size_align_valid size align = RustM.ok false := by
  by_cases hz : align = (0 : usize)
  · -- align = 0: extraction artifact (lost short-circuit `&&`); the
    -- extracted function fails with `.integerOverflow`, contradicting the
    -- intended contract. Documented intractable sorry (see docstring).
    subst hz
    sorry
  · -- align ≠ 0 and not a power of two ⟹ bit-trick test ≠ 0 ⟹ ok false.
    have hnp : (align &&& (align - 1)) ≠ (0 : usize) := by
      intro hc
      exact h ((pow2_iff align hz).mp hc)
    exact isav_eval_notpow2 size align hz hnp

/-- Contract clause 2 (postcondition for valid alignment).

    For every power-of-two `align`, the result is exactly the documented
    property: `size` rounded up to the next multiple of `align` must not
    exceed `isize::MAX` (`= 2^63 - 1` on a 64-bit target). The round-up is
    expressed at the `Nat` level as `((size + (align - 1)) / align) * align`
    — exactly the overflow-safe `u128` oracle `fits_when_rounded_up` used
    by the Rust tests.

    Captures the property test `power_of_two_align_matches_round_up_contract`
    and the unit test `layout_round_up_to_align_edge_cases`. -/
theorem is_size_align_valid_power_of_two_round_up
    (size align : usize) (k : Nat) (h : align.toNat = 2 ^ k) :
    is_size_align_valid size align
      = RustM.ok (decide
          (((size.toNat + (align.toNat - 1)) / align.toNat) * align.toNat
            ≤ 2 ^ 63 - 1)) := by
  -- A power of two is non-zero.
  have hApos : 0 < align.toNat := by rw [h]; exact Nat.two_pow_pos k
  have hz : align ≠ (0 : usize) := by
    intro hc
    have : align.toNat = 0 := by rw [hc, USize64.toNat_zero]
    omega
  -- bit-trick test passes, bound for the second subtraction holds.
  have hp : (align &&& (align - 1)) = (0 : usize) :=
    (pow2_iff align hz).mpr ⟨k, h⟩
  have hle : align.toNat ≤ 2 ^ 63 := pow2_le h
  -- k ≤ 63 and the divisibility witness `2^63 = align.toNat * 2^(63-k)`.
  have hk63 : k ≤ 63 := by
    by_contra hcon
    have h64 : 64 ≤ k := by omega
    have hge : (2:Nat) ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h64
    have hlt : align.toNat < 2 ^ 64 := USize64.toNat_lt align
    rw [h] at hlt; omega
  have hq : 2 ^ 63 = align.toNat * 2 ^ (63 - k) := by
    rw [h, ← Nat.pow_add]
    congr 1
    omega
  -- evaluate the program to the size comparison
  rw [isav_eval_pow2 size align hz hp hle]
  -- bridge `(2^63 - align) : usize` to its `Nat` value
  have hmle : align ≤ (9223372036854775808 : usize) := by
    rw [USize64.le_iff_toNat_le, big_toNat]
    have : (9223372036854775808 : Nat) = 2 ^ 63 := by norm_num
    omega
  have hm : ((9223372036854775808 : usize) - align).toNat = 2 ^ 63 - align.toNat := by
    rw [USize64.toNat_sub_of_le _ _ hmle, big_toNat]
    norm_num
  -- relate the `usize` comparison `size > (2^63 - align)` to the round-up bound
  have hround : (((size.toNat + (align.toNat - 1)) / align.toNat) * align.toNat
                  ≤ 2 ^ 63 - 1)
                ↔ size.toNat ≤ 2 ^ 63 - align.toNat :=
    round_up_le_iff hApos hq
  by_cases hcmp : size > ((9223372036854775808 : usize) - align)
  · rw [if_pos hcmp]
    have hgt : 2 ^ 63 - align.toNat < size.toNat := by
      have hh := hcmp
      rw [gt_iff_lt, USize64.lt_iff_toNat_lt, hm] at hh
      exact hh
    have hnot : ¬ (((size.toNat + (align.toNat - 1)) / align.toNat) * align.toNat
                    ≤ 2 ^ 63 - 1) := by
      rw [hround]; omega
    rw [decide_eq_false hnot]
  · rw [if_neg hcmp]
    have hle2 : size.toNat ≤ 2 ^ 63 - align.toNat := by
      have hcmp' : ¬ (size > ((9223372036854775808 : usize) - align)) := hcmp
      rw [gt_iff_lt, USize64.lt_iff_toNat_lt, hm] at hcmp'
      omega
    have hyes : ((size.toNat + (align.toNat - 1)) / align.toNat) * align.toNat
                  ≤ 2 ^ 63 - 1 := by
      rw [hround]; exact hle2
    rw [decide_eq_true hyes]

/-- Documented no-panic / totality clause.

    The Rust source explicitly relies on the short-circuit `&&` so that
    `n - 1` "never underflows when `n == 0`", and `max_size_for_align`'s
    subtraction `2^63 - align` never underflows for a power-of-two `align`.
    Hence `is_size_align_valid` is a total `bool`-valued checker.

    STUCK SUB-GOAL (only the `align = 0` instance): `∃ v, is_size_align_valid
    size 0 = RustM.ok v`. As documented on
    `is_size_align_valid_non_power_of_two_rejected`, Hax lost Rust's
    short-circuit `&&`, so `is_size_align_valid size 0 = RustM.fail
    .integerOverflow`, which is not `RustM.ok v` for any `v`. The totality
    clause is true of the intended Rust function but false of the extracted
    model at `align = 0`. The `align ≠ 0` case is fully proved below.

    STRUCTURAL UNBLOCK: the same Hax extraction fix described on
    `is_size_align_valid_non_power_of_two_rejected` (preserve short-circuit
    `&&` as a guarded `if`) makes `is_size_align_valid size 0 = RustM.ok
    false`, discharging this instance. Not fixable Lean-side. -/
theorem is_size_align_valid_no_panic (size align : usize) :
    ∃ v : Bool, is_size_align_valid size align = RustM.ok v := by
  by_cases hz : align = (0 : usize)
  · -- align = 0: extraction artifact (lost short-circuit `&&`). Documented
    -- intractable sorry (see docstring).
    subst hz
    sorry
  · -- align ≠ 0: split on the bit-trick test.
    by_cases hp : (align &&& (align - 1)) = (0 : usize)
    · -- power of two ⟹ obligation 2 gives an explicit `RustM.ok` value.
      obtain ⟨k, hk⟩ := (pow2_iff align hz).mp hp
      exact ⟨_, is_size_align_valid_power_of_two_round_up size align k hk⟩
    · -- not a power of two ⟹ rejects with `false`.
      exact ⟨false, isav_eval_notpow2 size align hz hp⟩

end Is_size_align_valid_usizeObligations
