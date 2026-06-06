-- Companion obligations file for the `average_ceil_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import average_ceil_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Average_ceil_u64Obligations

/-- Helper: discharge the Hoare triple via the `min_modified` pattern. -/
private theorem average_ceil_triple (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄ average_ceil_u64.average_ceil x y
    ⦃ ⇓ r => ⌜ r = (x ||| y) - ((x ^^^ y) >>> (1 : UInt64)) ⌝ ⦄ := by
  hax_mvcgen [average_ceil_u64.average_ceil]
  <;> bv_decide

/-- Helper: derive the equation form from the Hoare triple by case-analysis
    on the `RustM` result. `Triple_iff_BitVec` translates the triple into
    `(toBVRustM.ok && decide (val = expected)) = true`; the only `RustM`
    value with `toBVRustM.ok = true` is `.ok _`, so the equation follows. -/
private theorem average_ceil_unfold (x y : u64) :
    average_ceil_u64.average_ceil x y =
      RustM.ok ((x ||| y) - ((x ^^^ y) >>> (1 : UInt64))) := by
  have h := average_ceil_triple x y
  rw [RustM.Triple_iff_BitVec] at h
  -- Strip the trivially-true precondition (`!decide True = false`) and the
  -- outer `||`, then split the resulting boolean conjunction.
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  -- Case-split on the RustM value.
  cases hf : average_ceil_u64.average_ceil x y with
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

/-- No failure / totality: `average_ceil` never panics. The Dietz formula
    `(x | y) - ((x ^ y) >> 1)` avoids u64 overflow by construction — the
    bitwise OR is always ≥ the half-XOR — so no precondition is needed
    and the call is total on the entire `(u64, u64)` domain. The Rust
    source documents this explicitly: "no failure conditions (no panic,
    no error, no overflow)". -/
theorem average_ceil_no_failure (x y : u64) :
    ∃ v : u64, average_ceil_u64.average_ceil x y = RustM.ok v :=
  ⟨(x ||| y) - ((x ^^^ y) >>> (1 : UInt64)), average_ceil_unfold x y⟩

/-- The Dietz formula at the `BitVec 64` level matches the 65-bit lift
    of `(x + y + 1) / 2`. This is a pure bitvector fact (a fixed-width
    SAT problem at width 65), so `bv_decide` discharges it directly. -/
private theorem dietz_bv65 (a b : BitVec 64) :
    ((a.zeroExtend 65 + b.zeroExtend 65 + 1#65) >>> (1 : Nat)).truncate 64 =
      (a ||| b) - ((a ^^^ b) >>> (1 : Nat)) := by
  bv_decide

/-- Postcondition (functional correctness): for every pair of `u64`
    inputs, `average_ceil` returns ⌈(x + y) / 2⌉ computed in unbounded
    arithmetic. The unbounded ceiling is expressed at the `Nat` level as
    `(x.toNat + y.toNat + 1) / 2`, then cast back to `u64`. The maximum
    value of this Nat expression is `((2^64 - 1) + (2^64 - 1) + 1) / 2 =
    2^64 - 1`, which always fits in `u64`, so the cast is exact.

    This is the single semantic claim the Rust property test
    `postcondition_ceiling_average` certifies, with the `u128` oracle
    `((sum + 1) / 2) as u64`. -/
theorem average_ceil_postcondition (x y : u64) :
    average_ceil_u64.average_ceil x y =
      RustM.ok (UInt64.ofNat ((x.toNat + y.toNat + 1) / 2)) := by
  rw [average_ceil_unfold]
  congr 1
  -- Goal: (x ||| y) - ((x ^^^ y) >>> (1 : UInt64)) =
  --       UInt64.ofNat ((x.toNat + y.toNat + 1) / 2)
  -- Compare via `.toNat`.
  apply UInt64.toNat.inj
  -- LHS reductions: subtraction is genuine Nat-sub since Dietz inequality
  -- holds; bitwise ops and shift unfold to Nat-level operators.
  have hle : (x ^^^ y) >>> (1 : UInt64) ≤ x ||| y := by bv_decide
  rw [UInt64.toNat_sub_of_le _ _ hle,
      UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_xor,
      UInt64.toNat_ofNat']
  -- Reduce the shift amount: `(1 : UInt64).toNat % 64 = 1`.
  have h_shift : (1 : UInt64).toNat % 64 = 1 := rfl
  rw [h_shift]
  -- The result fits in 64 bits, so the outer mod is identity.
  have hbound : (x.toNat + y.toNat + 1) / 2 < 2 ^ 64 := by
    have hx := x.toNat_lt_size
    have hy := y.toNat_lt_size
    have hsize : (UInt64.size : Nat) = 2 ^ 64 := rfl
    rw [hsize] at hx hy
    omega
  rw [Nat.mod_eq_of_lt hbound]
  -- Now the Nat-level Dietz identity. Prove via the 65-bit BitVec lift.
  have hb := dietz_bv65 x.toBitVec y.toBitVec
  have hnat := congrArg BitVec.toNat hb
  -- Reduce the BitVec sub on RHS via the no-underflow lemma at width 64.
  have hle_bv : ((x.toBitVec ^^^ y.toBitVec) >>> (1 : Nat)) ≤ (x.toBitVec ||| y.toBitVec) := by
    bv_decide
  -- Simplify both sides of `hnat` via the BitVec.toNat simp set.
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
             BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  rw [BitVec.toNat_sub_of_le hle_bv] at hnat
  simp only [BitVec.toNat_or, BitVec.toNat_xor, BitVec.toNat_ushiftRight] at hnat
  -- Unify `x.toBitVec.toNat` and `UInt64.toNat x` (definitionally equal),
  -- so omega treats them as the same variable.
  have hxbv : x.toBitVec.toNat = UInt64.toNat x := rfl
  have hybv : y.toBitVec.toNat = UInt64.toNat y := rfl
  rw [hxbv, hybv] at hnat
  -- Tighten the bounds.
  have hx := x.toNat_lt_size
  have hy := y.toNat_lt_size
  have hsize : (UInt64.size : Nat) = 2 ^ 64 := rfl
  rw [hsize] at hx hy
  -- `Nat.shiftRight 1 = / 2`.
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one] at hnat ⊢
  -- All mods drop because `x.toNat + y.toNat + 1 < 2^65` and the result is
  -- < 2^64. omega closes the residual Dietz Nat identity.
  omega

end Average_ceil_u64Obligations
