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

/-! ## Loop-dependent obligations

The remaining four obligations all depend on reasoning *through* the
six nested `rust_primitives.hax.while_loop` invocations that implement
Stein's binary GCD algorithm. The loops have `loop_decreases!` measures
in the Rust source (so termination extracts), but no `loop_invariant!`
clauses (the invariants needed — bitwise oddness predicates and lower
bounds on the loop variables — trip the Hax `pureP` synthesis at
extraction time, which is why the source-level note "The proof stage
will supply a Lean-side invariant via `Spec.MonoLoopCombinator.while_loop`"
appears at `src/lib.rs:34-36`).

Probing with `hax_mvcgen [gcd_u64.gcd]` on the trivial-postcondition
triple `⦃ True ⦄ gcd x y ⦃ ⇓ _ => True ⦄` reveals **ten** independent
verification conditions left open by the default trivial invariant
(see the proof of `gcd_total` below). They split into three families:

1. **Loop-counter overflow** — `vc1` requires the `shift : u32` counter
   not to wrap; this is true (it's bounded by `64`) but the trivial
   invariant `fun _ => True` doesn't carry the bound.
2. **Per-iteration shift termination** — `vc2, vc5, vc7, vc10, vc14`
   each require `(v >>> 1).toNat < v.toNat` under the precondition
   `v &&& 1 = 0`. Provable but needs the auxiliary fact `v ≠ 0` (a
   shift-right of `0` doesn't strictly decrease).
3. **Subtraction-no-underflow + post-subtraction OR-decrease** — `vc9,
   vc12, vc14, vc16` need `m > n → ¬ usubOverflow m n` (easy) plus
   `(m - n) ||| n < m ||| n` (the bitwise-OR strict-decrease fact, the
   real heart of Stein's termination argument — needs both operands odd
   so `m - n` is even, and a Nat-level `m | n ≥ m` argument).
4. **Final shift-left bound** — `vc17` requires `shift < 64` to discharge
   `m <<< shift`'s no-overflow check; again needs the loop-1 counter
   invariant.

Closing each obligation manually means supplying a six-fold composite
loop invariant via `Spec.MonoLoopCombinator.while_loop`, descending
through every `rust_primitives.hax.while_loop` and rebinding the state.
The library has no example exercising this — the selector explicitly
flagged this gap ("no example in the library uses `while_loop` or
`loop_decreases`"). The four obligations below are therefore left as
`sorry` with this technical reason; they are *not* removed or weakened.

The two equational obligations above (`gcd_zero_left`, `gcd_zero_right`)
fully cover the `prop_gcd_zero_cases` test. -/

/-- Totality / no-failure: `gcd` is total on the entire `(u64, u64)`
    domain. The contract documents this explicitly: "no panics, and the
    result is bounded by `max(x, y)` so `m << shift` cannot overflow".
    Implicit in every Rust test (a return value must exist).

    LEFT AS `sorry`: see the section comment above. The trivial Hoare
    triple `⦃ True ⦄ gcd x y ⦃ ⇓ _ => True ⦄` reduces — under
    `hax_mvcgen` — to ten residual VCs spread across the six nested
    `rust_primitives.hax.while_loop`s; closing them needs a hand-written
    composite loop invariant supplied via `Spec.MonoLoopCombinator.while_loop`.
    No reference example in the library exercises that pattern, so this
    obligation is left as `sorry` rather than being removed. -/
theorem gcd_total (x y : u64) :
    ∃ v : u64, gcd_u64.gcd x y = RustM.ok v := by
  sorry

/-- Postcondition (D-x): the result divides the first input.

    Captured by the `prop_gcd_divides_both` test which asserts
    `x % g == 0` whenever `g != 0` (and forces `x = y = 0` when
    `g == 0`). Stated at the `Nat` level via `Nat.dvd`, which has
    `0 ∣ 0` true and `0 ∣ n` false for `n > 0`, so the convention
    `gcd(0, 0) = 0` is consistent with this clause.

    LEFT AS `sorry`: requires a per-iteration divisibility invariant
    `Nat.gcd m_orig n_orig = Nat.gcd (m * 2^shift) (n * 2^shift)` to be
    propagated through every loop body, then specialised at exit
    (`m = n` ⇒ `Nat.gcd m_orig n_orig = m << shift`). The infrastructure
    for that (a do-bind-aware `Spec.MonoLoopCombinator.while_loop`
    pattern with a ternary state invariant) is not exercised by any
    reference example. -/
theorem gcd_divides_x (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ g.toNat ∣ x.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (D-y): the result divides the second input.

    Captured by the `prop_gcd_divides_both` test (same clause as
    `gcd_divides_x` but for `y`). Independent because an
    implementation could divide one input but not the other.

    LEFT AS `sorry`: same technical reason as `gcd_divides_x`. -/
theorem gcd_divides_y (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ g.toNat ∣ y.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (G): every common divisor of `x` and `y` divides
    the result — i.e. the result is the *greatest* common divisor.

    Captured by the `prop_gcd_is_greatest` test, which iterates over
    every candidate `d ∈ 1..=64` and checks `g % d == 0` whenever
    `d` is a common divisor of `x, y`. Independent of (D): an
    implementation returning `1` would satisfy (D) but fail (G).

    LEFT AS `sorry`: requires the same per-iteration `Nat.gcd`-invariant
    as `gcd_divides_x`/`gcd_divides_y`, plus a final step using
    `Nat.dvd_gcd`. Same library-coverage gap. -/
theorem gcd_is_greatest (x y d : u64) :
    ⦃ ⌜ d.toNat ∣ x.toNat ∧ d.toNat ∣ y.toNat ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ d.toNat ∣ g.toNat ⌝ ⦄ := by
  sorry

end Gcd_u64Obligations
