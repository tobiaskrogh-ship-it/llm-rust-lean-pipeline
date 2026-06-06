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

/-- Witness extraction: any non-zero Nat satisfying `n &&& (n - 1) = 0`
    equals `2 ^ Nat.log2 n`. Standard characterization of powers of two. -/
private theorem nat_pow_two_of_and_pred {n : Nat}
    (hne : n ≠ 0) (hand : n &&& (n - 1) = 0) :
    n = 2 ^ n.log2 := by
  -- Standard Lean fact `Nat.eq_two_pow_self_of_and_pred_eq_zero` or similar.
  -- Strong induction on n.
  induction n using Nat.strong_induction with
  | _ n ih =>
    -- Base case: n = 1 ⇒ log2 1 = 0, 2^0 = 1.
    by_cases h1 : n = 1
    · subst h1; rfl
    -- Otherwise n ≥ 2.
    have h2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · interval_cases n
        · exact absurd rfl hne
        · exact absurd rfl h1
      · exact hge
    -- Express n = 2 * (n/2) + n % 2.
    -- Since n &&& (n - 1) = 0, lowest bit of n equals lowest bit of (n - 1).
    -- For n ≥ 2, n - 1 ≥ 1. Specifically, lowest bit of n must be 0 (n even),
    -- else n &&& (n - 1) ≥ 1.
    have h_even : n % 2 = 0 := by
      by_contra hc
      have hodd : n % 2 = 1 := by omega
      -- n is odd: testBit n 0 = true. n - 1 is even: testBit (n - 1) 0 = false.
      -- But also (n - 1) % 2 = 0 since n odd ⇒ n - 1 even.
      -- Actually n &&& (n-1) at bit 0: n's bit 0 = 1, (n-1)'s bit 0 = 0, so & = 0. OK at bit 0.
      -- But for n odd: n - 1 = n - 1 (even). n / 2 = (n-1)/2 (integer division).
      -- So n &&& (n - 1) at bits ≥ 1 should be... hmm.
      -- Let me reconsider: n odd ⇒ n = 2m + 1 for some m. n - 1 = 2m. So
      -- n &&& (n-1) = (2m+1) &&& (2m). At bit 0: 1 &&& 0 = 0. At higher bits: m &&& m = m.
      -- So n &&& (n - 1) = 2m. For this to be 0, m = 0, so n = 1. But h1 contradicts that.
      have hm : ∃ m, n = 2 * m + 1 ∧ m ≥ 1 := ⟨n / 2, by omega, by omega⟩
      obtain ⟨m, hn_eq, hm_ge⟩ := hm
      have h_sub : n - 1 = 2 * m := by omega
      have : n &&& (n - 1) = 2 * m := by
        rw [hn_eq, h_sub]
        -- (2m + 1) &&& (2m) = 2 * (m &&& m) = 2m.
        have : (2 * m + 1) &&& (2 * m) = 2 * (m &&& m) := by
          have : 2 * m + 1 = (2 * m) ||| 1 := by
            rw [Nat.mul_comm 2 m, ← Nat.shiftLeft_one m]
            -- (m <<< 1) ||| 1: bottom bit 1, rest m.
            -- (2m) is m << 1. (2m + 1) = (m << 1) | 1.
            sorry
          sorry
        rw [this, Nat.land_self]
      rw [hand] at this
      omega
    -- n even and n ≥ 2 ⇒ n/2 ≥ 1.
    have hn_half_pos : n / 2 ≥ 1 := by omega
    have hn_half_lt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    -- We also need: (n / 2) &&& ((n / 2) - 1) = 0.
    have hn_half_and : (n / 2) &&& (n / 2 - 1) = 0 := by
      have hn_2 : n = 2 * (n / 2) := by omega
      have hsub_2 : n - 1 = 2 * (n / 2) - 1 := by omega
      -- We have 2 * (n/2) &&& (2 * (n/2) - 1) = 0.
      -- Note: 2 * x &&& (2 * x - 1) = 2 * (x &&& (x - 1)).
      sorry
    have ih_res : n / 2 = 2 ^ (n / 2).log2 := ih (n / 2) hn_half_lt (by omega) hn_half_and
    -- Now combine. n = 2 * (n / 2) = 2 * 2^log2(n/2) = 2^(log2(n/2) + 1).
    have hlog : n.log2 = (n / 2).log2 + 1 := by
      sorry
    rw [hlog]
    have : 2 ^ ((n / 2).log2 + 1) = 2 * 2 ^ (n / 2).log2 := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [this, ← ih_res]
    omega

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
