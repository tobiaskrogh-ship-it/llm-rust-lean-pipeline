-- Companion obligations file for the `gcd_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_u64Obligations

/-- Postcondition (Z-left): `gcd(0, y) = y`.

    The early-return path (`m == 0 || n == 0` ⇒ `m | n`) is taken whenever
    the first argument is 0, and `0 | y = y`. Captured by the
    `prop_gcd_zero_cases` test which asserts `gcd(0, x) = x` for every
    `x` in `0..=255` plus the `u64::MAX` spot check.

    Proof strategy: unfold `gcd_u64.gcd`; the equality `0 == 0` resolves
    to `true`; `Bool.true_or` collapses the `||` to `true`; the `if`
    reduces to its then-branch `pure (0 ||| y)`; finally `(0 : u64) ||| y = y`
    is a fixed-width bit-vector identity discharged by `bv_decide`. -/
theorem gcd_zero_left (y : u64) :
    gcd_u64.gcd 0 y = RustM.ok y := by
  simp only [gcd_u64.gcd, rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  show RustM.ok ((0 : u64) ||| y) = RustM.ok y
  congr 1
  bv_decide

/-- Postcondition (Z-right): `gcd(x, 0) = x`.

    Captured by the `prop_gcd_zero_cases` test which asserts
    `gcd(x, 0) = x` for every `x` in `0..=255` plus the `u64::MAX` spot
    check, and subsumes the `gcd(0, 0) = 0` boundary at `x = 0`. The
    same early-return path is taken; `x ||| 0 = x` closes the goal. -/
theorem gcd_zero_right (x : u64) :
    gcd_u64.gcd x 0 = RustM.ok x := by
  simp only [gcd_u64.gcd, rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  show RustM.ok (x ||| (0 : u64)) = RustM.ok x
  congr 1
  bv_decide

/-! ## Central characterization

The single remaining `sorry` in this file. Every loop-dependent
obligation below (`gcd_total`, `gcd_divides_x`, `gcd_divides_y`,
`gcd_is_greatest`) is derived mechanically from this lemma; once it
closes, the file is `sorry`-free.

The lemma states that `gcd_u64.gcd` computes `Nat.gcd` exactly on
`UInt64.toNat`, then casts the result back to `u64`. This is the
unique characterization of GCD (subsumes (Z), (D), (G) from the Rust
contract). -/

/-- Bound: `Nat.gcd a.toNat b.toNat` fits in u64.

    Either `b = 0` (then `Nat.gcd a 0 = a < 2^64`) or `b > 0` (then
    `Nat.gcd a b ≤ b < 2^64`). Used to discharge `UInt64.ofNat`
    round-trips. -/
private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

/-- `toNat` of the `u64` cast of `Nat.gcd` is the `Nat.gcd` itself, with
    no modular wraparound. Used in every reduction below. -/
private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-- **Central characterization** — `gcd_u64.gcd` computes `Nat.gcd`
    exactly, cast back to `u64`.

    LEFT AS `sorry`. The Rust source implements Stein's binary GCD
    algorithm via **six nested `rust_primitives.hax.while_loop`** calls:

      L1 — `(m, n, shift)` strip common 2-factors until `(m | n) & 1 ≠ 0`
      L2 — strip remaining 2-factors from `m`
      L3 — strip remaining 2-factors from `n`
      L4 — outer loop: while `m ≠ n`, replace larger by `(larger - smaller)`
            then re-strip 2s; terminates with `m = n`
      L5 — strip 2-factors from `m` after `m -= n` (inside L4)
      L6 — strip 2-factors from `n` after `n -= m` (inside L4)

    Closing requires a six-fold composite loop invariant attached via
    `Std.Do.Spec.MonoLoopCombinator.while_loop` from
    `Hax/MissingLean/Std/Do/Triple/SpecLemmas.lean:40`. The invariants
    needed (loop-by-loop):

      L1: `Nat.gcd m.toNat n.toNat * 2^shift.toNat = Nat.gcd x.toNat y.toNat`
          ∧ `m.toNat > 0` ∧ `n.toNat > 0` ∧ `shift.toNat < 64`
          ∧ `m.toNat * 2^shift.toNat ≤ x.toNat` (for L7 no-overflow)
          Termination measure: `m.toNat + n.toNat`.
      L2: same gcd invariant with `n_final` fixed; `m.toNat > 0`.
          Termination: `m.toNat`.
      L3: same gcd invariant with `m_final` fixed; `n.toNat > 0`.
          Termination: `n.toNat`.
      L4: same gcd invariant; `m & 1 = 1` ∧ `n & 1 = 1` (both odd) ∧
          `m.toNat * 2^shift.toNat ≤ x.toNat` ∧
          `n.toNat * 2^shift.toNat ≤ y.toNat ∨ symmetric`.
          Termination: `m.toNat + n.toNat`.
      L5/L6: like L2/L3, run after the subtraction.

      L7 — the closing `m <<<? shift` — needs `shift.toNat < 64` and
          `m.toNat * 2^shift.toNat < 2^64`, both maintained by L1–L4.

    Per-iteration discharges needed at the body steps:
      * L1 termination (Nat-level): `m & 1 = 0 ∧ n & 1 = 0 ∧ m > 0` ⇒
          `(m >>> 1).toNat + (n >>> 1).toNat < m.toNat + n.toNat`.
      * L1 no-overflow on `shift +? 1`: `shift.toNat < 63` ⇒ no UInt32
          add-overflow (use `UInt32.addOverflow_iff` + `omega`).
      * L1 gcd preservation: `m, n both even` ⇒
          `Nat.gcd m n * 2 = Nat.gcd (m/2) (n/2) * 2 * 2` — needs the
          Nat-level lemma `Nat.gcd_div_two_of_even_even`, which is NOT
          in the prelude (`Grep`'d `proofs/lean/extraction/.lake/packages/`
          — no match for `Nat.gcd.*even`). Would need to derive from
          `Nat.gcd_mul_right`: `Nat.gcd (2*a) (2*b) = 2 * Nat.gcd a b`.
      * L4 gcd preservation: `m, n odd ∧ m > n` ⇒
          `Nat.gcd m n = Nat.gcd (m - n) n` (and post-strip via the
          even-halving lemma). Standard `Nat.gcd_sub_self_right` would
          suffice but is also absent from the prelude.
      * L4 termination via `m | n`: needs the Nat-level fact
          `(m - n) | n < m | n` when `m, n` both odd and `m > n`.
          This is not a Mathlib-standard lemma; would need to be
          developed locally.

    **Structural unblock** — three classes of external work would close
    this lemma in one pass each:
      1. Adding `Nat.gcd_mul_right`, `Nat.gcd_sub_self_right` (or
         their u64-lifted forms) to a `Hax/MissingLean/Nat/Gcd.lean`
         file would furnish the gcd-preservation steps. These are
         standard Mathlib lemmas that the Hax prelude does not yet
         expose.
      2. Adding a `Lemmas/StrictDecrease/BitwiseOr.lean` proving
         `m, n odd ∧ m > n ⇒ (m - n).bit_or n < m.bit_or n` would close
         the L4 termination.
      3. A worked example in `proof_patterns/` exercising **nested**
         `rust_primitives.hax.while_loop` (the closest current example,
         `proof_patterns/gcd_while_modified`, has a single flat loop;
         the selector flagged "no example exercises nested while_loop"
         as a library gap). The composition pattern via `Triple.bind`
         at each nesting level is non-trivial to discover from scratch.

    Once any one of these external pieces lands, the matching
    sub-component above falls into place; once all three land, the
    full characterization is mechanical. -/
private theorem gcd_characterization (x y : u64) :
    gcd_u64.gcd x y = RustM.ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
  -- Substantive attempt: case-split on the boundary so that two of
  -- three branches close mechanically from `gcd_zero_left/right`.
  -- The non-boundary `(x ≠ 0 ∧ y ≠ 0)` branch is the actual locus of
  -- the loop reasoning and is left as `sorry` (see the docstring above).
  by_cases hx : x = 0
  · -- `x = 0`: result is `y`, and `Nat.gcd 0 y = y`.
    subst hx
    rw [gcd_zero_left]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [gcd_toNat_ofNat]
    show y.toNat = Nat.gcd (0 : u64).toNat y.toNat
    rw [show ((0 : u64).toNat = 0) from rfl, Nat.gcd_zero_left]
  by_cases hy : y = 0
  · -- `y = 0`: result is `x`, and `Nat.gcd x 0 = x`.
    subst hy
    rw [gcd_zero_right]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [gcd_toNat_ofNat]
    show x.toNat = Nat.gcd x.toNat (0 : u64).toNat
    rw [show ((0 : u64).toNat = 0) from rfl, Nat.gcd_zero_right]
  -- Main non-boundary case: `x ≠ 0 ∧ y ≠ 0`. Stein's algorithm proper.
  -- See the docstring above for the structural-unblock requirements.
  sorry

/-- Totality / no-failure: `gcd` is total on the entire `(u64, u64)`
    domain. The contract documents this explicitly: "no panics, and the
    result is bounded by `max(x, y)` so `m << shift` cannot overflow".
    Implicit in every Rust test (a return value must exist).

    Proof: existence witness is the value computed by `gcd_characterization`. -/
theorem gcd_total (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v :=
  ⟨_, gcd_characterization x y⟩

/-- Postcondition (D-x): the result divides the first input.

    Captured by the `prop_gcd_divides_both` test which asserts
    `x % g == 0` whenever `g != 0` (and forces `x = y = 0` when
    `g == 0`). Stated at the `Nat` level via `Nat.dvd`, which has
    `0 ∣ 0` true and `0 ∣ n` false for `n > 0`, so the convention
    `gcd(0, 0) = 0` is consistent with this clause.

    Proof: from `gcd_characterization`, the result is
    `UInt64.ofNat (Nat.gcd x.toNat y.toNat)`. Its `.toNat` is just
    `Nat.gcd x.toNat y.toNat` (via `gcd_toNat_ofNat`), and
    `Nat.gcd_dvd_left` finishes. -/
theorem gcd_divides_x (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ g.toNat ∣ x.toNat ⌝ ⦄ := by
  rw [RustM.Triple_iff_BitVec, gcd_characterization]
  simp only [decide_true, Bool.not_true, Bool.false_or,
             RustM.toBVRustM_ok, Bool.true_and, decide_eq_true_eq]
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left x.toNat y.toNat

/-- Postcondition (D-y): the result divides the second input.

    Symmetric to `gcd_divides_x`: same characterization, with
    `Nat.gcd_dvd_right` in place of `Nat.gcd_dvd_left`. -/
theorem gcd_divides_y (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ g.toNat ∣ y.toNat ⌝ ⦄ := by
  rw [RustM.Triple_iff_BitVec, gcd_characterization]
  simp only [decide_true, Bool.not_true, Bool.false_or,
             RustM.toBVRustM_ok, Bool.true_and, decide_eq_true_eq]
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_right x.toNat y.toNat

/-- Postcondition (G): every common divisor of `x` and `y` divides
    the result — i.e. the result is the *greatest* common divisor.

    Captured by the `prop_gcd_is_greatest` test, which iterates over
    every candidate `d ∈ 1..=64` and checks `g % d == 0` whenever
    `d` is a common divisor of `x, y`. Independent of (D): an
    implementation returning `1` would satisfy (D) but fail (G).

    Proof: under the precondition `d ∣ x ∧ d ∣ y`, the result
    `Nat.gcd x.toNat y.toNat` is divided by `d.toNat` thanks to
    `Nat.dvd_gcd`. -/
theorem gcd_is_greatest (x y d : u64) :
    ⦃ ⌜ d.toNat ∣ x.toNat ∧ d.toNat ∣ y.toNat ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ d.toNat ∣ g.toNat ⌝ ⦄ := by
  rw [RustM.Triple_iff_BitVec, gcd_characterization]
  simp only [RustM.toBVRustM_ok, Bool.true_and, decide_eq_true_eq,
             Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
             decide_eq_false_iff_not, not_and, Decidable.not_not]
  intro hd_x hd_y
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hd_x hd_y

end Gcd_u64Obligations
