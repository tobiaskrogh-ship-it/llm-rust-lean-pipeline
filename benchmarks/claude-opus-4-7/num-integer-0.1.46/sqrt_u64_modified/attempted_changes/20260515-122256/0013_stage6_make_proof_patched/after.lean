-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import sqrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Sqrt_u64Obligations

open rust_primitives.hax (Tuple2)

/-! ## Helper infrastructure

The `sqrt` implementation composes three `while_loop`s:

  1. `log2 a` — a single loop computing `⌊log₂ a⌋`.
  2. Babylonian "descent" loop in `sqrt`: iterates while `x < xn`.
  3. Babylonian "polish" loop in `sqrt`: iterates while `x > xn`.

The canonical proof shape for each (from `while_example/README.md`) is the
two-stage Stage 1 (Hoare-triple) + Stage 2 (`RustM.Triple_iff_BitVec`) pattern.

The dominant blocker for the value/bound obligations below is a closed-form
spec for the *Newton iteration*: a proof that the Babylonian step
`xn := (a/x + x) / 2` is non-increasing once `x ≥ ⌈√a⌉` and converges to
`⌊√a⌋`. This requires a real-arithmetic argument (`(a/x + x)/2 ≥ √a` by
AM-GM, then a Nat-level descent). Mathlib provides `Nat.sqrt` with the
companion lemmas `Nat.sqrt_le_self`, `Nat.sqrt_lt_self`, `Nat.sq_sqrt_le`,
`Nat.lt_succ_sqrt`, etc. — but Mathlib is not imported in this project.

A bespoke `Nat.sqrt`-style lemma library in the obligations file is feasible
in principle (define `natSqrt n := ...` by strong recursion, prove the four
bound lemmas), but its scope is the size of a self-contained proof of square
root correctness — well outside one obligations-stage turn. The lemmas are
listed below by name in the structural unblocks; future passes that have
those lemmas available (or that import a `Nat.sqrt`-augmented prelude) close
the sorries mechanically. -/

/-! ### Log2 invariant (single-loop scaffolding) -/

/-- Strong invariant for the `log2` loop. `count.toNat ≤ 63` because `y > 1`
    implies `y.toNat ≥ 2`, hence `2 ^ count.toNat ≤ x₀.toNat / 2 < 2^63`. -/
private def log2Inv (x₀ : u64) (s : Tuple2 u32 u64) : Prop :=
  s._0.toNat ≤ 63 ∧ s._1.toNat = x₀.toNat / 2 ^ s._0.toNat

/-- Termination measure for the `log2` loop. -/
private def log2Term (s : Tuple2 u32 u64) : Nat := s._1.toNat

/-- A future-pass helper: log2 returns `⌊log₂ x⌋` for `x > 0`, and `0` for
    `x = 0`. The closed-form value lets `sqrt_four` and the doctests
    symbolically evaluate the initial-guess shift `1 << ((log2 a + 1) / 2)`.

    Stuck sub-goal: building the Hoare triple over the underlying
    `Loop.MonoLoopCombinator.while_loop` requires bridging `>>>?` to `/ 2`
    on `Nat` via `UInt64.toNat_shiftRight` (in `Init.Data.UInt.Bitwise`),
    discharging the no-shift-overflow predicate `0 ≤ (1 : i32) && (1 : i32) < 64`
    (true by `decide`), and showing `count + 1` does not overflow `u32` —
    which uses the loop-invariant bound `count.toNat ≤ 62` inside the body.
    Each step is standard but the chain is long.

    Structural unblock: a closed-form `log2_postcondition` proved via the
    canonical Stage 1 + Stage 2 pattern, parallel to
    `gcd_while_postcondition` in `proof_patterns/gcd_while_modified`. -/
private theorem log2_postcondition (x : u64) :
    sqrt_u64.log2 x = RustM.ok (UInt32.ofNat (Nat.log2 x.toNat)) := by
  sorry

/-! ### Newton iteration invariant (sqrt's two loops)

The Babylonian iteration converges to `⌊√a⌋`. A formal proof needs:

* `nat_sqrt_correct : ∀ n, (Nat.sqrt n) * (Nat.sqrt n) ≤ n ∧ n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1)`
* `babylonian_step_descent : ∀ a x, 0 < x → Nat.sqrt a + 1 ≤ x → (a / x + x) / 2 < x`
* `babylonian_step_floor : ∀ a x, 0 < x → x ≤ Nat.sqrt a → Nat.sqrt a ≤ (a / x + x) / 2`

`Nat.log2` and `Nat.sqrt` exist in core Lean (`Init.Data.Nat.Log2`,
`Init.Data.Nat.Sqrt`) and *do* satisfy the boundedness lemmas above
(e.g. `Nat.sqrt_lt'`, `Nat.sqrt_le'`). The blocker is bridging them to
the Hax partial-operator semantics on `u64` and combining two sequential
loops with a shared invariant on the intermediate state. -/

/-- Closed-form for `sqrt`: returns `⌊√x⌋` as a `u64`. Once proved, the
    individual obligations below derive from this in one or two lines.

    Stuck sub-goal: the two-loop convergence proof. After unfolding both
    `rust_primitives.hax.while_loop`s, we obtain a sequential composition
    of two `Loop.MonoLoopCombinator.while_loop`s on state `(x, xn)`.
    `Spec.MonoLoopCombinator.while_loop` gives us a triple per loop, but
    the intermediate state must be threaded — the post of loop 1 must
    imply the pre of loop 2. The natural strong invariant
    `Nat.sqrt a ≤ x` (carried from after loop 1) is preserved by loop 2's
    body via `babylonian_step_floor`, and loop 2 terminates via the measure
    `x.toNat` since `babylonian_step_descent` gives strict decrease while
    `x > xn`. Loop 1 terminates because `cond (xn, (a/xn + xn)/2) = false`
    after one iteration — i.e., the loop runs at most once.

    Structural unblock: a self-contained `Nat.sqrt` lemma library
    (`nat_sqrt_correct` and the two `babylonian_step_*` lemmas above) added
    to this file or the Hax prelude. With those, the Stage 1 triple is a
    routine application of `Spec.MonoLoopCombinator.while_loop` twice,
    and Stage 2 is the standard `RustM.Triple_iff_BitVec` discharge. -/
private theorem sqrt_postcondition (x : u64) :
    sqrt_u64.sqrt x = RustM.ok (UInt64.ofNat (Nat.sqrt x.toNat)) := by
  sorry

/-- Bridging fact: `Nat.sqrt x.toNat ≤ 2^32 - 1`, so the result fits in `u64`. -/
private theorem nat_sqrt_lt_2_32 (x : u64) : Nat.sqrt x.toNat < 2 ^ 32 := by
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  -- `Nat.sqrt x.toNat ≤ √(2^64 - 1) < 2^32`.
  have h1 : Nat.sqrt x.toNat ≤ Nat.sqrt (2 ^ 64 - 1) :=
    Nat.sqrt_le_sqrt (by omega)
  have h2 : Nat.sqrt (2 ^ 64 - 1) < 2 ^ 32 := by decide
  omega

private theorem nat_sqrt_lt_2_64 (x : u64) : Nat.sqrt x.toNat < 2 ^ 64 := by
  have := nat_sqrt_lt_2_32 x
  omega

private theorem sqrt_toNat_ofNat (x : u64) :
    (UInt64.ofNat (Nat.sqrt x.toNat)).toNat = Nat.sqrt x.toNat :=
  UInt64.toNat_ofNat_of_lt' (nat_sqrt_lt_2_64 x)

/-! ## Postcondition: lower bound (`r² ≤ x`)

Captures the property test `prop_sqrt_lower_bound`: for the returned root `r`,
`r.toNat * r.toNat ≤ x.toNat`. A buggy implementation that returns too large a
value (e.g. `x` itself, or `r + 1` for non-perfect squares) is caught here.

Stated at the `Nat` level: a correct result satisfies `r ≤ 2^32 - 1`, so
`r * r` fits in `u64`; phrasing the inequality over `Nat` avoids embedding
the `checked_mul` overflow guard from the Rust test. -/
theorem sqrt_lower_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r ∧ r.toNat * r.toNat ≤ x.toNat := by
  refine ⟨_, sqrt_postcondition x, ?_⟩
  rw [sqrt_toNat_ofNat]
  exact Nat.sqrt_le' x.toNat

/-! ## Postcondition: upper bound (`x < (r+1)²`)

Captures the property test `prop_sqrt_upper_bound`: for the returned root `r`,
`x.toNat < (r.toNat + 1) * (r.toNat + 1)`. Independent from the lower bound —
an implementation always returning `0` would pass the lower bound but fail
this one.

Stated at the `Nat` level: `(r.toNat + 1) * (r.toNat + 1)` is `Nat` arithmetic,
so the Rust test's "vacuous when `(r+1)²` overflows `u64`" caveat folds in
automatically — when `(r+1)²` exceeds `2^64`, `x.toNat < (r+1)²` still holds
since `x.toNat < 2^64`. -/
theorem sqrt_upper_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r
      ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  refine ⟨_, sqrt_postcondition x, ?_⟩
  rw [sqrt_toNat_ofNat]
  exact Nat.lt_succ_sqrt' x.toNat

/-! ## Totality / no panic

Explicit "no failure mode" clause from the Rust contract comment ("Failures:
none — the function never panics"). For every `u64` input, `sqrt` returns a
value successfully. -/
theorem sqrt_total (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v :=
  ⟨_, sqrt_postcondition x⟩

/-! ## Specific values: small inputs

Each line of `sqrt_small` becomes one theorem. These pin down the function on
the `a < 4` branch of the implementation, which is the boundary the Rust
source explicitly handles. -/

theorem sqrt_zero : sqrt_u64.sqrt 0 = RustM.ok 0 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_one : sqrt_u64.sqrt 1 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_two : sqrt_u64.sqrt 2 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_three : sqrt_u64.sqrt 3 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_four : sqrt_u64.sqrt 4 = RustM.ok 2 := by
  rw [sqrt_postcondition]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' (nat_sqrt_lt_2_64 4)]
  show Nat.sqrt 4 = 2
  decide

/-! ## Specific values: doctest

The doc-test `sqrt_doctest` asserts three identities at `x = 12345`. Each
becomes one theorem. -/

theorem sqrt_doctest_exact :
    sqrt_u64.sqrt (12345 * 12345 : u64) = RustM.ok (12345 : u64) := by
  sorry

theorem sqrt_doctest_plus_one :
    sqrt_u64.sqrt (12345 * 12345 + 1 : u64) = RustM.ok (12345 : u64) := by
  sorry

theorem sqrt_doctest_minus_one :
    sqrt_u64.sqrt (12345 * 12345 - 1 : u64) = RustM.ok (12344 : u64) := by
  sorry

end Sqrt_u64Obligations
