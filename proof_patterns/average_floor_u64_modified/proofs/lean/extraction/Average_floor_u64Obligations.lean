-- Companion obligations file for the `average_floor_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import average_floor_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Average_floor_u64Obligations

/-- Half-adder identity over `Nat`: for any `a b : Nat`,
    `2 * (a &&& b) + (a ^^^ b) = a + b`. Proved by strong induction on `a`,
    using the bit-decomposition `n = 2 * (n / 2) + n % 2` and the identities
    `(a &&& b) / 2 = (a/2) &&& (b/2)`, `(a &&& b) % 2 = (a%2) &&& (b%2)`,
    and analogously for `^^^`. The base case at one bit (residues in `{0, 1}`)
    is a finite case-check. -/
private theorem nat_half_adder (a b : Nat) :
    2 * (a &&& b) + (a ^^^ b) = a + b := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    by_cases h : a = 0
    · subst h
      simp [Nat.zero_and, Nat.zero_xor]
    · have h_pos : 0 < a := Nat.pos_of_ne_zero h
      have h_div_lt : a / 2 < a := Nat.div_lt_self h_pos (by decide)
      have ih_div : 2 * ((a / 2) &&& (b / 2)) + ((a / 2) ^^^ (b / 2))
                      = (a / 2) + (b / 2) := ih (a / 2) h_div_lt (b / 2)
      -- Bit decompositions of `a`, `b`, `a &&& b`, `a ^^^ b`.
      have h_a_decomp : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
      have h_b_decomp : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
      have h_and_div : (a &&& b) / 2 = (a / 2) &&& (b / 2) := Nat.and_div_two
      have h_and_mod : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
        have := @Nat.and_mod_two_pow a b 1
        simpa using this
      have h_and : a &&& b = 2 * ((a / 2) &&& (b / 2)) + ((a % 2) &&& (b % 2)) := by
        have hd : a &&& b = 2 * ((a &&& b) / 2) + (a &&& b) % 2 :=
          (Nat.div_add_mod (a &&& b) 2).symm
        rw [h_and_div, h_and_mod] at hd
        exact hd
      have h_xor_div : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := Nat.xor_div_two
      have h_xor_mod : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
        have := @Nat.xor_mod_two_pow a b 1
        simpa using this
      have h_xor : a ^^^ b = 2 * ((a / 2) ^^^ (b / 2)) + ((a % 2) ^^^ (b % 2)) := by
        have hd : a ^^^ b = 2 * ((a ^^^ b) / 2) + (a ^^^ b) % 2 :=
          (Nat.div_add_mod (a ^^^ b) 2).symm
        rw [h_xor_div, h_xor_mod] at hd
        exact hd
      -- Single-bit residual identity, by case analysis on `{0, 1}`.
      have h_a_mod_lt : a % 2 < 2 := Nat.mod_lt a (by decide)
      have h_b_mod_lt : b % 2 < 2 := Nat.mod_lt b (by decide)
      have h_res :
          2 * ((a % 2) &&& (b % 2)) + ((a % 2) ^^^ (b % 2)) = (a % 2) + (b % 2) := by
        have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide
      -- Combine.
      rw [h_and, h_xor]
      -- Goal: 2 * (2 * ((a/2) &&& (b/2)) + ((a%2) &&& (b%2)))
      --     + (2 * ((a/2) ^^^ (b/2)) + ((a%2) ^^^ (b%2)))
      --     = a + b
      -- Group differently and apply IH and h_res.
      have h_group :
          2 * (2 * ((a/2) &&& (b/2)) + ((a%2) &&& (b%2)))
            + (2 * ((a/2) ^^^ (b/2)) + ((a%2) ^^^ (b%2)))
          = 2 * (2 * ((a/2) &&& (b/2)) + ((a/2) ^^^ (b/2)))
              + (2 * ((a%2) &&& (b%2)) + ((a%2) ^^^ (b%2))) := by omega
      rw [h_group, ih_div, h_res]
      -- Goal: 2 * ((a/2) + (b/2)) + ((a%2) + (b%2)) = a + b
      omega

/-- Postcondition: `average_floor x y` returns `⌊(x + y) / 2⌋`, where the sum
    is taken over the integers (NOT modulo `2^64`). The reference value is
    computed via unbounded `Nat` addition (equivalently the `u128` reference
    used in the Rust tests `matches_floor_of_sum_over_two` and the proptest
    `prop_matches_floor_of_sum_over_two`). Encoding the right-hand side as
    `RustM.ok …` (rather than `RustM.fail …`) folds in the no-overflow
    guarantee: the bit-trick implementation must succeed even when
    `x.toNat + y.toNat > 2^64 - 1`.

    This single equational statement subsumes the specific-instance tests
    `bounded`, `overflow`, `doc_examples_unsigned`, and `agrees_with_source`
    (which is a sweep against the original `num-integer` implementation that
    satisfies the same algebraic identity). -/
theorem average_floor_postcondition (x y : u64) :
    average_floor_u64.average_floor x y =
      RustM.ok (UInt64.ofNat ((x.toNat + y.toNat) / 2)) := by
  -- Step 1: unfold the function and the underlying instances.
  simp only [average_floor_u64.average_floor, pure_bind,
             rust_primitives.ops.bit.Shr.shr,
             rust_primitives.ops.arith.Add.add]
  -- Step 2: the shift's bounds-check `0 ≤ (1 : Int32) && (1 : Int32) < 64`
  -- is `true` by computation, so the `if` collapses; the bind on `pure`
  -- collapses too. After this, `(1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64)`.
  simp only [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl,
             ↓reduceIte, pure_bind]
  -- Step 3: bridges between `UInt64` operations and their `Nat` counterparts.
  have h_x_lt : x.toNat < 2 ^ 64 := x.toNat_lt
  have h_y_lt : y.toNat < 2 ^ 64 := y.toNat_lt
  have h_sum_div_lt : (x.toNat + y.toNat) / 2 < 2 ^ 64 := by omega
  have h_one_eq : ((1 : Int32).toNatClampNeg.toUInt64) = (1 : UInt64) := rfl
  rw [h_one_eq]
  have h_and_toNat : (x &&& y).toNat = x.toNat &&& y.toNat := UInt64.toNat_and x y
  have h_xor_toNat : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := UInt64.toNat_xor x y
  have h_shr_toNat : ((x ^^^ y) >>> (1 : UInt64)).toNat = (x.toNat ^^^ y.toNat) / 2 := by
    rw [UInt64.toNat_shiftRight, h_xor_toNat,
        show (1 : UInt64).toNat = 1 from rfl, Nat.shiftRight_eq_div_pow]
  -- Half-adder identity at the Nat level applied to (x.toNat, y.toNat).
  have h_ha : 2 * (x.toNat &&& y.toNat) + (x.toNat ^^^ y.toNat) = x.toNat + y.toNat :=
    nat_half_adder x.toNat y.toNat
  -- Bound the no-overflow sum.
  have h_no_overflow_nat :
      (x &&& y).toNat + ((x ^^^ y) >>> (1 : UInt64)).toNat < 2 ^ 64 := by
    rw [h_and_toNat, h_shr_toNat]
    -- (x &&& y).toNat ≤ x.toNat (and ≤ y.toNat); xor / 2 ≤ (sum) / 2; etc.
    have h_xor_le : x.toNat ^^^ y.toNat ≤ x.toNat + y.toNat := by omega
    -- (a &&& b) ≤ a + b / 2 type inequalities; combine with the half-adder identity.
    omega
  -- Step 4: `BitVec.uaddOverflow ... = false` via Nat-level bound.
  have h_no_ovf_bv :
      BitVec.uaddOverflow (x &&& y).toBitVec ((x ^^^ y) >>> (1 : UInt64)).toBitVec = false := by
    cases h_eq : BitVec.uaddOverflow (x &&& y).toBitVec ((x ^^^ y) >>> (1 : UInt64)).toBitVec
    · rfl
    · exfalso
      have h_ovf : UInt64.addOverflow (x &&& y) ((x ^^^ y) >>> (1 : UInt64)) = true := h_eq
      rw [UInt64.addOverflow_iff] at h_ovf
      omega
  rw [if_neg (by rw [h_no_ovf_bv]; decide)]
  -- Step 5: equality of the value inside `RustM.ok`.
  apply congrArg RustM.ok
  -- Reduce to `toNat` equality.
  apply UInt64.toNat_inj.mp
  -- Compute both sides via `toNat`.
  rw [UInt64.toNat_add_of_lt h_no_overflow_nat]
  rw [h_and_toNat, h_shr_toNat]
  rw [UInt64.toNat_ofNat_of_lt' h_sum_div_lt]
  -- Goal: (x.toNat &&& y.toNat) + (x.toNat ^^^ y.toNat) / 2 = (x.toNat + y.toNat) / 2.
  -- Use the half-adder identity `2 * (a &&& b) + (a ^^^ b) = a + b`.
  omega

/-- Totality / no-panic: the Henry Gordon Dietz bit trick
    `(x & y) + ((x ^ y) >> 1)` provably never overflows, so for every pair of
    `u64` inputs the function returns a value (it never panics). This is the
    explicit "no failure mode" clause of the contract — separately documented
    in the Rust source ("the bit-trick implementation never overflows, even
    when `x + y > u64::MAX`"), independent of the postcondition's value. -/
theorem average_floor_total (x y : u64) :
    ∃ v : u64, average_floor_u64.average_floor x y = pure v := by
  refine ⟨UInt64.ofNat ((x.toNat + y.toNat) / 2), ?_⟩
  -- `pure` and `RustM.ok` agree on `RustM`.
  show average_floor_u64.average_floor x y
        = RustM.ok (UInt64.ofNat ((x.toNat + y.toNat) / 2))
  exact average_floor_postcondition x y

end Average_floor_u64Obligations
