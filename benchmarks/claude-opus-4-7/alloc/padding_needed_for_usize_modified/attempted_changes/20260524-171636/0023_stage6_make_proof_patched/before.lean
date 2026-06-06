-- Companion obligations file for the `padding_needed_for_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import padding_needed_for_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Padding_needed_for_usizeObligations

open padding_needed_for_usize

/-- Helper: when `x ≠ 0` is known, the unsigned subtraction `x - 1` does not
    overflow, so `x -? 1 = RustM.ok (x - 1)`. -/
private theorem usize_sub_one_ok {x : usize} (hx : x ≠ 0) :
    (x -? (1 : usize)) = RustM.ok (x - 1) := by
  have hno : ¬ (BitVec.usubOverflow x.toBitVec (1#64) = true) := by
    have h0 : (USize64.subOverflow x 1 = true) ↔ x.toNat < (1 : usize).toNat :=
      USize64.subOverflow_iff
    have h1 : (1 : usize).toNat = 1 := rfl
    have hxnz : x.toNat ≠ 0 := by
      intro h
      apply hx
      apply USize64.toNat_inj.mp
      exact h
    show ¬ (USize64.subOverflow x 1 = true)
    rw [h0, h1]
    omega
  show (if BitVec.usubOverflow x.toBitVec (1#64) = true then
          (RustM.fail .integerOverflow : RustM usize)
        else pure (x - 1)) = RustM.ok (x - 1)
  rw [if_neg hno]
  rfl

/-- Characterization of `is_power_of_two_usize`: always returns `ok`, with the
    Boolean value `x ≠ 0 ∧ (x &&& (x - 1) = 0)` (the classic bit-trick test). -/
private theorem is_power_of_two_usize_eq (x : usize) :
    is_power_of_two_usize x =
      RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0)) := by
  unfold is_power_of_two_usize
  by_cases hx : x = 0
  · subst hx
    decide
  · have hsub : (x -? (1 : usize)) = RustM.ok (x - 1) := usize_sub_one_ok hx
    show (do
      let __do_lift ← (pure (decide (x = 0)) : RustM Bool)
      if __do_lift = true then pure false
      else do
        let __do_lift ← (x -? (1 : usize))
        (x &&& __do_lift) ==? (0 : usize))
       = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    rw [decide_eq_false hx]
    simp only [pure_bind, Bool.false_eq_true, if_false]
    rw [hsub]
    show (do
        let __do_lift ← (pure (x - 1) : RustM usize)
        (x &&& __do_lift) ==? (0 : usize))
      = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    simp only [pure_bind]
    show (pure (decide (x &&& (x - 1) = 0)) : RustM Bool)
       = RustM.ok (decide (x ≠ 0) && decide (x &&& (x - 1) = 0))
    have h1 : decide (x ≠ 0) = true := decide_eq_true hx
    rw [h1, Bool.true_and]
    rfl

/-- Bit-trick fact: every usize that is a power of two (i.e. `x ≠ 0` and
    `x &&& (x - 1) = 0`) is bounded above by `2^63`. -/
private theorem usize_pow_of_two_le {x : usize}
    (hnz : x ≠ 0) (hand : x &&& (x - 1) = 0) :
    x.toNat ≤ 2 ^ 63 := by
  have hbv : x.toBitVec ≠ 0#64 := by
    intro h
    apply hnz
    apply USize64.toBitVec_inj.mp
    exact h
  have hbvand : x.toBitVec &&& (x.toBitVec - 1#64) = 0#64 := by
    have h1 : (x &&& (x - 1)).toBitVec = x.toBitVec &&& (x - 1).toBitVec := rfl
    have h2 : (x - 1).toBitVec = x.toBitVec - 1#64 := rfl
    have h3 : (0 : usize).toBitVec = 0#64 := rfl
    have h4 : (x &&& (x - 1)).toBitVec = (0 : usize).toBitVec := by
      rw [hand]
    rw [h1, h2] at h4
    rw [h4, h3]
  show x.toBitVec.toNat ≤ 2 ^ 63
  have : x.toBitVec ≤ 0x8000000000000000#64 := by
    revert hbv hbvand
    bv_decide
  have : x.toBitVec.toNat ≤ (0x8000000000000000#64).toNat := by
    exact (BitVec.le_def.mp this)
  have hb : (0x8000000000000000#64).toNat = 2 ^ 63 := by decide
  omega

/-- From `is_power_of_two_usize align = ok true` extract `align ≠ 0`. -/
private theorem is_power_of_two_usize_ne_zero {align : usize}
    (h : is_power_of_two_usize align = RustM.ok true) :
    align ≠ 0 := by
  rw [is_power_of_two_usize_eq] at h
  have hb : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = true := by
    have heq := h
    injection heq with heq1
    injection heq1
  rw [Bool.and_eq_true] at hb
  exact of_decide_eq_true hb.1

/-- From `is_power_of_two_usize align = ok true` extract `align &&& (align - 1) = 0`. -/
private theorem is_power_of_two_usize_and_eq_zero {align : usize}
    (h : is_power_of_two_usize align = RustM.ok true) :
    align &&& (align - 1) = 0 := by
  rw [is_power_of_two_usize_eq] at h
  have hb : (decide (align ≠ 0) && decide (align &&& (align - 1) = 0)) = true := by
    have heq := h
    injection heq with heq1
    injection heq1
  rw [Bool.and_eq_true] at hb
  exact of_decide_eq_true hb.2

/-- From `is_power_of_two_usize align = ok true` extract `align.toNat ≤ 2^63`. -/
private theorem is_power_of_two_usize_le {align : usize}
    (h : is_power_of_two_usize align = RustM.ok true) :
    align.toNat ≤ 2 ^ 63 :=
  usize_pow_of_two_le (is_power_of_two_usize_ne_zero h)
    (is_power_of_two_usize_and_eq_zero h)

/-- Failure-mode clause: when `align` is not a power of two (as decided by
    the helper `is_power_of_two_usize`), the function returns the inlined
    `usize::MAX = 2 ^ 64 - 1` regardless of `size`. Captures the property
    test `prop_non_power_of_two_returns_max`, which sweeps every
    non-power-of-two `align ∈ 0..256` (including `0` and the odd values
    `3`, `5`, `6`, …) with every size `0..256`. A buggy implementation
    that produced a smaller result for some non-power-of-two align would
    falsify this. -/
theorem padding_needed_for_non_power_of_two
    (size align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    padding_needed_for size align
      = RustM.ok (18446744073709551615 : usize) := by
  unfold padding_needed_for
  rw [h]
  rfl

/-- Master BitVec fact: under the power-of-two characterization
    (`a ≠ 0 ∧ a &&& (a - 1) = 0`) and a no-overflow guard on
    `s + (a - 1)`, the bit-trick round-up `(s + (a - 1)) &&& ~(a - 1)`
    is (1) at least `s` (so no underflow when subtracting), (2) strictly
    less than `s + a` (so the gap is < `a`), and (3) has zero bits in the
    bottom `k` positions where `a = 2^k`. -/
private theorem round_up_bv_props {s a : BitVec 64}
    (ha : a ≠ 0#64) (hpow : a &&& (a - 1#64) = 0#64)
    (hnov : ¬ BitVec.uaddOverflow s (a - 1#64)) :
    s ≤ (s + (a - 1#64)) &&& ~~~(a - 1#64) ∧
    ((s + (a - 1#64)) &&& ~~~(a - 1#64)) - s < a ∧
    ((s + (a - 1#64)) &&& ~~~(a - 1#64)) &&& (a - 1#64) = 0#64 := by
  revert ha hpow hnov
  bv_decide

/-- Nat-level: for `a = 2^k`, the bottom-`k`-bits mask of `n` is `n % a`. -/
private theorem nat_land_two_pow_sub_one_eq_mod (n : Nat) (k : Nat) :
    n &&& (2 ^ k - 1) = n % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod n k

/-- `2^k` divides `z` iff all of `z`'s low `k` bits are zero. -/
private theorem two_pow_dvd_iff_testBit (k z : Nat) :
    2 ^ k ∣ z ↔ ∀ i, i < k → Nat.testBit z i = false := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have h2split : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    constructor
    · intro hdvd i hik
      obtain ⟨c, hc⟩ := hdvd
      have hz_half : z / 2 = 2 ^ k * c := by
        rw [hc, h2split, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false :=
        (ih (z / 2)).mp ⟨c, hz_half⟩
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        have hz_even : z % 2 = 0 := by
          have hzc : z = 2 * (2 ^ k * c) := by rw [hc, h2split, Nat.mul_assoc]
          omega
        exact Nat.mod_two_eq_zero_iff_testBit_zero.mp hz_even
      · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        subst hj
        rw [Nat.testBit_succ]
        exact hbits_half j (by omega)
    · intro hbits
      have hz_even : z % 2 = 0 :=
        Nat.mod_two_eq_zero_iff_testBit_zero.mpr (hbits 0 (by omega))
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false := by
        intro j hjk
        rw [← Nat.testBit_succ]
        exact hbits (j + 1) (by omega)
      obtain ⟨c, hc⟩ := (ih (z / 2)).mpr hbits_half
      refine ⟨c, ?_⟩
      have hz2 : z = 2 * (z / 2) := by omega
      rw [hz2, hc, h2split, Nat.mul_assoc]

/-- `z &&& m = 0` iff `z` has zero at every bit position where `m` has one. -/
private theorem land_eq_zero_iff_testBit (z m : Nat) :
    z &&& m = 0 ↔ ∀ i, Nat.testBit m i = true → Nat.testBit z i = false := by
  constructor
  · intro h i hm
    have : Nat.testBit (z &&& m) i = false := by rw [h]; exact Nat.zero_testBit i
    rw [Nat.testBit_and] at this
    rw [hm] at this
    simpa using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hm : Nat.testBit m i
    · rw [Bool.and_false]
    · rw [h i hm, Bool.false_and]

/-- Witness extraction: any non-zero Nat with `n &&& (n - 1) = 0` is a power
    of two. Uses `Nat.log2` as the witness. Combines:
    - `2 ^ n.log2 ≤ n` (lower bound from `Nat.log2_self_le`).
    - `n < 2 ^ (n.log2 + 1)` (upper bound from `Nat.lt_two_pow_log2_succ`).
    - `n &&& (n - 1) = 0` (hypothesis): forces `n = 2 ^ n.log2`. -/
private theorem nat_pow_two_of_and_pred {n : Nat}
    (hne : n ≠ 0) (hand : n &&& (n - 1) = 0) :
    n = 2 ^ n.log2 := by
  -- Strong induction on n.
  induction n using Nat.strong_induction with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1; rfl
    have h2 : 2 ≤ n := by omega
    -- We need n / 2 to satisfy the same hypothesis, then use IH.
    -- First, show n is even: if not, n &&& (n-1) = n - 1 ≠ 0.
    have h_test_zero : Nat.testBit n 0 = false := by
      -- Suppose n is odd: testBit n 0 = true.
      -- Then n - 1 is even, n - 1 ≥ 2: bit 0 of n - 1 = 0.
      -- But for the lowest set bit of n - 1: n is odd ≥ 3 ⇒ n - 1 ≥ 2 even.
      -- For i ≥ 1: testBit n i = testBit (n - 1) i (since n = (n-1) + 1, addition of 1 to even).
      -- So if n.testBit i is true for any i ≥ 1, also (n-1).testBit i is true. From hand: contradiction.
      -- Since n ≥ 3, some bit ≥ 1 of n is set, contradiction.
      -- Conclude n is even.
      by_contra hc
      have hbit0 : Nat.testBit n 0 = true := by
        cases h : Nat.testBit n 0
        · exact absurd h hc
        · rfl
      -- n = 2 * (n / 2) + 1 (since odd via testBit 0 = true)
      have hn_odd : n % 2 = 1 := by
        rw [← Nat.testBit_zero] at hbit0
        rcases Nat.mod_two_eq_zero_or_one n with h | h
        · exfalso
          rw [Nat.testBit_zero] at hbit0
          have : n.testBit 0 = decide (n % 2 = 1) := by
            rw [Nat.testBit_zero]
            cases h_n_mod : n % 2 with
            | zero => simp
            | succ k =>
              have : n % 2 < 2 := Nat.mod_lt n (by decide)
              interval_cases (n % 2)
              · simp
          omega
        · exact h
      have hn_even : n - 1 = 2 * (n / 2) := by omega
      have hn_form : n = 2 * (n / 2) + 1 := by omega
      have hhalf : n / 2 ≥ 1 := by omega
      -- For n ≥ 3 odd, n / 2 ≥ 1, so log2 (n / 2) is well-defined and (n / 2).log2 ≥ 0.
      -- n.testBit (n.log2) = true (since n ≥ 1).
      have htop : Nat.testBit n n.log2 = true :=
        Nat.testBit_log2_self (Nat.pos_of_ne_zero hne)
      have hlog_pos : 1 ≤ n.log2 := by
        rw [Nat.one_le_iff_ne_zero]
        intro h
        -- n.log2 = 0 ⇒ n < 2, so n = 1 (since n ≠ 0). But h1 contradicts.
        have : n < 2 := by
          have := Nat.lt_two_pow_log2_succ (n := n)
          rw [h] at this; simpa using this
        omega
      -- testBit n n.log2 = testBit (n - 1) n.log2 (since n is odd and bits ≥ 1 are unchanged by ±1)
      have hsame : Nat.testBit (n - 1) n.log2 = Nat.testBit n n.log2 := by
        rw [hn_even, hn_form]
        obtain ⟨j, hj⟩ : ∃ j, n.log2 = j + 1 := ⟨n.log2 - 1, by omega⟩
        rw [hj]
        rw [show (2 * (n / 2) + 1) = (n / 2) * 2 + 1 from by ring]
        rw [show (2 * (n / 2)) = (n / 2) * 2 from by ring]
        -- testBit ((n/2) * 2 + 1) (j+1) = ?  Hmm let me think.
        -- (n/2) * 2 = (n/2) <<< 1. So testBit ((n/2) <<< 1) (j+1) = (n/2).testBit j.
        -- (n/2) * 2 + 1 has bit 0 = 1; bit (j+1) = (n/2) <<< 1's bit (j+1) (since adding 1 only affects bit 0).
        -- But adding 1 to an even number only flips bit 0 (the even number has bit 0 = 0).
        rw [show (n / 2) * 2 + 1 = (n / 2) * 2 ||| 1 from by
              -- 2k + 1 = (2k) ||| 1
              -- Use: 2k has bit 0 = 0, so |||1 sets it.
              -- This is Nat.bit_or_self or similar.
              sorry]
        rw [Nat.testBit_or]
        rw [show Nat.testBit 1 (j + 1) = false from by
              rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp; omega]
        simp
      rw [htop] at hsame
      exact absurd (h_testBit n.log2 hsame.symm) (by rw [htop]; decide)
    -- n is even: n / 2 < n, (n / 2) &&& (n / 2 - 1) = 0, and (n / 2) ≠ 0.
    sorry

/-- Postcondition (alignment): when `align` is a power of two and the
    inputs fit in the safe range `size + align ≤ 2 ^ 64`, the function
    returns some `p : usize` such that `size + p` is a multiple of
    `align`, i.e. the address following the `size`-byte block is aligned
    to `align`. Captures the property test `prop_result_aligns_size_up`
    (which sweeps `align ∈ {1, 2, 4, …, 2^15}` and `size ∈ 0..1000` —
    well within the no-overflow envelope).

    The bound `size.toNat + align.toNat ≤ 2 ^ 64` is the no-overflow
    guard for the internal `size +? (align - 1)` step; for power-of-two
    `align ≤ 2^63` this is implied by `size.toNat ≤ 2^63`, which is
    the implicit precondition of the standard `Layout` API. -/
theorem padding_needed_for_aligns_size_up
    (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ p : usize, padding_needed_for size align = RustM.ok p ∧
                  (size.toNat + p.toNat) % align.toNat = 0 := by
  sorry

/-- Postcondition (minimality): under the same preconditions, the
    returned padding `p` is strictly smaller than `align`. Captures the
    property test `prop_padding_is_minimal`. Independent of the
    alignment clause: together they pin down `p` as the smallest
    non-negative offset such that `size + p` is a multiple of `align`
    (a result that overshoots by a whole `align` block would satisfy
    the alignment clause but fail this one). -/
theorem padding_needed_for_minimal
    (size align : usize)
    (hpow : is_power_of_two_usize align = RustM.ok true)
    (hbound : size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ p : usize, padding_needed_for size align = RustM.ok p ∧
                  p.toNat < align.toNat := by
  sorry

/-- Totality / no-panic: the function returns successfully whenever the
    non-power-of-two branch fires (any `align`, any `size`) or the
    power-of-two branch's safe range `size + align ≤ 2 ^ 64` holds.

    The non-pow-of-two branch returns the inlined `usize::MAX` directly,
    with no partial operations. In the pow-of-two branch the partial
    operators (`align -? 1`, `size +? align_m1`, `~? align_m1`, `&&&?`,
    `len_rounded_up -? size`) are all safe under the precondition:
    `align ≥ 1` from the power-of-two characterization makes
    `align - 1` non-underflowing; `hbound` makes `size + align_m1`
    non-overflowing; `~?` and `&&&?` are total bitwise operators; and
    the bit-mask round-up satisfies `len_rounded_up ≥ size` (the
    explicit Rust source comment "cannot overflow because the
    rounded-up value is never less than `size`"), so the final
    subtraction is safe. Captures the implicit "no panic" totality
    contract exercised by every property test. -/
theorem padding_needed_for_total
    (size align : usize)
    (hbound : is_power_of_two_usize align = RustM.ok true
              → size.toNat + align.toNat ≤ 2 ^ 64) :
    ∃ p : usize, padding_needed_for size align = RustM.ok p := by
  sorry

end Padding_needed_for_usizeObligations
