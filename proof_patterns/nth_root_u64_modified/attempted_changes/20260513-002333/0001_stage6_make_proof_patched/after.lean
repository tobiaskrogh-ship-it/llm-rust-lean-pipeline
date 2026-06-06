-- Companion obligations file for the `nth_root_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import nth_root_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Nth_root_u64Obligations

/-! ## Pure `Nat` helper lemmas for the Newton-iteration arguments.

These are the algebraic identities that an actual closed proof of the Newton-
sweep correctness would invoke at the terminus of the loop. They are stated
and proved here from core `Nat` lemmas so that a future pass closing
`sqrt_lower_bound` / `cbrt_lower_bound` / `nth_root_lower_bound` does not
have to rediscover them. -/

/-- Terminus of the descending square-root Newton sweep. If a positive `x`
satisfies `x ≤ (a/x + x)/2`, then `x² ≤ a`. This is the algebraic crux of
the lower-bound proof: it converts the loop-exit condition into the
postcondition without any reference to the loop machinery.

Proof outline:
  `x ≤ (a/x + x)/2 → 2x ≤ 2 · ((a/x + x)/2) ≤ a/x + x → x ≤ a/x →
   x*x ≤ x*(a/x) = (a/x)*x ≤ a`. -/
private lemma sqrt_terminus_lower (a x : Nat) (hx : 0 < x)
    (hle : x ≤ (a / x + x) / 2) : x * x ≤ a := by
  have hhalf : 2 * ((a / x + x) / 2) ≤ a / x + x := by
    have := Nat.div_mul_le_self (a / x + x) 2
    omega
  have h2x : 2 * x ≤ a / x + x := by
    have h1 : 2 * x ≤ 2 * ((a / x + x) / 2) := Nat.mul_le_mul_left 2 hle
    exact Nat.le_trans h1 hhalf
  have hax : x ≤ a / x := by omega
  have h_mul : x * x ≤ x * (a / x) := Nat.mul_le_mul_left x hax
  have h_div : (a / x) * x ≤ a := Nat.div_mul_le_self a x
  have : x * (a / x) ≤ a := by rw [Nat.mul_comm]; exact h_div
  exact Nat.le_trans h_mul this

/-- Terminus of the descending cube-root Newton sweep. If a positive `x`
satisfies `x ≤ (a/x² + 2x)/3`, then `x³ ≤ a`.

Proof outline:
  `3x ≤ a/x² + 2x → x ≤ a/x² → x³ = x · (x²) ≤ (a/x²)·x² ≤ a`. -/
private lemma cbrt_terminus_lower (a x : Nat) (hx : 0 < x)
    (hle : x ≤ (a / (x * x) + 2 * x) / 3) : x * x * x ≤ a := by
  have hxx_pos : 0 < x * x := Nat.mul_pos hx hx
  have hthird : 3 * ((a / (x * x) + 2 * x) / 3) ≤ a / (x * x) + 2 * x := by
    have := Nat.div_mul_le_self (a / (x * x) + 2 * x) 3
    omega
  have h3x : 3 * x ≤ a / (x * x) + 2 * x := by
    have h1 : 3 * x ≤ 3 * ((a / (x * x) + 2 * x) / 3) := Nat.mul_le_mul_left 3 hle
    exact Nat.le_trans h1 hthird
  have hxax : x ≤ a / (x * x) := by omega
  have h_mul : x * (x * x) ≤ (a / (x * x)) * (x * x) := Nat.mul_le_mul_right (x * x) hxax
  have h_div : (a / (x * x)) * (x * x) ≤ a := Nat.div_mul_le_self a (x * x)
  -- Rewrite `x * x * x = x * (x * x)`.
  calc x * x * x = x * (x * x) := by ring
    _ ≤ (a / (x * x)) * (x * x) := h_mul
    _ ≤ a := h_div

/-! ## Helper lemmas stating the *missing* infrastructure.

These are the lemmas a closed proof of the Newton-sweep upper bounds and of
`nth_root` would need. They are stated here so a future pass has the exact
shape it needs; their proofs are themselves left as `sorry` because they
encode the deeper Newton-monovariant argument that is uncovered by any
reference example in the proof-pattern library. -/

/-- Newton-monovariant for `sqrt`: if the descending sweep terminates at
`x` (i.e. `x ≤ xn` where `xn = (a/x + x)/2`) and was initialized above the
true root, then `(x+1)² > a` whenever `(x+1)²` fits in `u64`.

This is the deeper claim of the upper bound: termination of the descending
sweep lands at the largest `x` with `x² ≤ a`, i.e. exactly `⌊√a⌋`. The
proof requires showing that the loop body is strictly decreasing while
`x > √a`, which itself uses the inequality `(a/x + x)/2 < x ↔ x² > a` for
positive `x`. -/
private lemma sqrt_terminus_upper (a x : Nat) (hx : 0 < x)
    (hle : x ≤ (a / x + x) / 2)
    (h_init_above : ∀ y, y < x → ¬ (y ≤ (a / y + y) / 2 → y * y ≤ a → True))
    : (x + 1) * (x + 1) > a := by
  sorry

/-- Functional correctness of `checked_pow_u64`: when the result is
`Some k`, then `k.toNat = x.toNat ^ n.toNat` and `x.toNat ^ n.toNat <
2^64`; when the result is `None`, then `x.toNat ^ n.toNat ≥ 2^64`.

This is the standard correctness contract of a `checked_pow` operation.
The proof goes by induction on `n.toNat` using `Nat.strongRecOn` and
follows the `recursion_example` pattern, but applied to a `partial_fixpoint`
that returns an `Option`. -/
private lemma checked_pow_u64_correct (x : u64) (n : u32) :
    (∀ k, nth_root_u64.checked_pow_u64 x n
            = RustM.ok (core_models.option.Option.Some k)
          → k.toNat = x.toNat ^ n.toNat ∧ x.toNat ^ n.toNat < 2 ^ 64)
    ∧ (nth_root_u64.checked_pow_u64 x n
          = RustM.ok core_models.option.Option.None
          → 2 ^ 64 ≤ x.toNat ^ n.toNat) := by
  sorry

/-- Failure condition for `nth_root`: when `n == 0`, the function panics.

The Rust source documents this in its `# Panics` section ("Panics if `n == 0`"),
and the `zeroth_root` test exercises it. The implementation triggers the panic
via `1u64 / (n as u64)`, which on `n == 0` extracts to a `RustM` failure with
`Error.divisionByZero` (the `if y = 0 then .fail .divisionByZero` branch of the
`UInt64` division instance). -/
theorem nth_root_zero_panic (self_val : u64) :
    nth_root_u64.nth_root self_val 0 = RustM.fail .divisionByZero := by
  unfold nth_root_u64.nth_root
  rfl

/-- (LB) for `sqrt_u64`: `result² ≤ a`.

The truncated principal square root is by definition the largest `r` with
`r² ≤ a`. Captures the `prop_sqrt_lower_bound` property test (and the
positive-input branch of the generic `check` used in the `sqrt` test). The
`Nat`-level inequality automatically subsumes the proptest's "no overflow
of `r²`" check, since `r.toNat ^ 2 ≤ a.toNat < 2^64`.

NOTE (left as `sorry`): the proof requires inventing a loop invariant for
the descending Newton sweep `while x > xn { x := xn; xn := (a/x + x) >>> 1 }`,
manually applying `Spec.MonoLoopCombinator.while_loop` (the source-level
`loop_decreases!` only feeds Hax's termination check, not a Lean
invariant), and discharging the integer-Newton convergence argument
"`x ≤ (a/x + x)/2 ⇒ x² ≤ a`". None of the closed-proof reference examples
covers a `while_loop` extraction with a non-trivial postcondition; the
selector explicitly flagged this as an uncovered gap in the example
library. The branches `a == 0` (returns 0) and `1 ≤ a < 4` (returns 1)
discharge cleanly, but the full proof needs the loop-invariant machinery
described in the manual loop-spec section of the proof skill. -/
theorem sqrt_lower_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.sqrt_u64 a
    ⦃ ⇓ r => ⌜ r.toNat ^ 2 ≤ a.toNat ⌝ ⦄ := by
  sorry

/-- (UB) for `sqrt_u64`: `(result + 1)² > a` whenever `(r + 1)²` is
representable in `u64` (vacuous otherwise).

Captures the `prop_sqrt_upper_bound` property test. Together with the lower
bound, this pins down the truncated principal square root uniquely.

NOTE (left as `sorry`): proving the upper bound on the loop's exit value is
the deeper of the two Newton-iteration arguments. It requires that the
initial guess `x₀ := 1u64 << (log2(a)/2 + 1)` strictly exceeds `√a`, that
each Newton step `x ↦ (a/x + x)/2` is monotone non-increasing while
`x > √a`, and that termination at `x ≤ xn` implies `(x+1)² > a`. The
last claim — Newton's monovariant — is uncovered by the example library
(no closed proof traverses a `while_loop`), so the proof would have to
build the descending-fixpoint invariant from scratch and apply
`Spec.MonoLoopCombinator.while_loop` manually. -/
theorem sqrt_upper_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.sqrt_u64 a
    ⦃ ⇓ r => ⌜ (r.toNat + 1) ^ 2 < 2 ^ 64 → a.toNat < (r.toNat + 1) ^ 2 ⌝ ⦄ := by
  sorry

/-- (LB) for `cbrt_u64`: `result³ ≤ a`.

Captures the `prop_cbrt_lower_bound` property test (and the positive-input
branch of the generic `check` used in the `cbrt` test).

NOTE (left as `sorry`): same structural reason as `sqrt_lower_bound`,
plus an extra delegation: for `a ≤ u32::MAX` the body forwards to
`cbrt_u32`, which itself uses a Hacker's-Delight bit-trick `while`-loop
with a per-step branch. Proving `cbrt_u32`'s correctness pre-states the
loop invariant `0 ≤ y ∧ y² = y2 ∧ y³ ≤ a - x_residual_with_shifts`, which
again requires the manual `Spec.MonoLoopCombinator.while_loop` machinery
not exercised in any reference example. The `a > u32::MAX` branch then
runs the same descending Newton sweep as `sqrt_u64`, with the same
loop-invariant gap. -/
theorem cbrt_lower_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.cbrt_u64 a
    ⦃ ⇓ r => ⌜ r.toNat ^ 3 ≤ a.toNat ⌝ ⦄ := by
  sorry

/-- (UB) for `cbrt_u64`: `(result + 1)³ > a` whenever `(r + 1)³` is
representable in `u64` (vacuous otherwise).

Captures the `prop_cbrt_upper_bound` property test. Together with the lower
bound, this pins down the truncated principal cube root uniquely.

NOTE (left as `sorry`): combines the cbrt-via-cbrt_u32 delegation
challenge of `cbrt_lower_bound` with the Newton-monovariant argument of
`sqrt_upper_bound`. No reference example covers either piece; the proof
needs the same manual loop-invariant machinery applied twice (once to
the `cbrt_u32` Hacker's-Delight loop, once to the descending Newton
sweep). -/
theorem cbrt_upper_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.cbrt_u64 a
    ⦃ ⇓ r => ⌜ (r.toNat + 1) ^ 3 < 2 ^ 64 → a.toNat < (r.toNat + 1) ^ 3 ⌝ ⦄ := by
  sorry

/-- (LB) for `nth_root`: `result^n ≤ a` for any valid `n ≥ 1`.

Captures the `prop_nth_root_lower_bound` property test (which exercises
`n ∈ 1..=128`) and the generic `check` used in `nth_root_test` and `bit_size`.
The precondition `n ≥ 1` is mandatory: `n == 0` is the panic case, separately
covered by `nth_root_zero_panic`. The `Nat`-level inequality subsumes the
proptest's "no overflow of `r^n`" requirement, since
`r.toNat ^ n.toNat ≤ a.toNat < 2^64`.

NOTE (left as `sorry`): the body of `nth_root` cascades into
  - `n = 1, 2, 3` → `pure a`, `sqrt_u64 a`, `cbrt_u64 a`,
  - `64 ≤ n ∨ a < 1 << n` → `pure 0` or `pure 1`,
  - otherwise → a descending Newton sweep using the recursive
    `checked_pow_u64` (`partial_fixpoint`).

The first two cascades depend on `sqrt_u64`/`cbrt_u64`, whose own
contracts are not yet established; the third cascade calls
`checked_pow_u64`, which is defined via `partial_fixpoint`. None of the
reference examples uses `partial_fixpoint`, so unfolding/induction on
`checked_pow_u64` requires building from scratch. Closing this theorem
therefore depends on:
  (i) `sqrt_lower_bound` and `cbrt_lower_bound` (themselves left as
      `sorry` for the `while_loop` reasons above),
  (ii) a correctness lemma for `checked_pow_u64`
       `r.toNat ^ n.toNat = some k → k.toNat = r.toNat ^ n.toNat`, and
  (iii) a Newton-monovariant + loop-invariant argument for the
       generic-`n` descending sweep.

There is also an extraction quirk worth flagging: the extracted
`if 64 ≤ n || a < (1 << n)` evaluates `1u64 <<<? n` eagerly (the `||?`
bind does not short-circuit through the shift's well-formedness check),
so on `n = 64` the shift produces `RustM.fail .integerOverflow`. The
Hoare triple `⦃ … ⦄ … ⦃ ⇓ r => … ⌝ ⦄` is vacuously true on `n ≥ 64`
because the postcondition is a claim only about successful results, but
this means the theorem as stated does not capture the *Rust* function's
behaviour on `n = 64` (where the source would short-circuit and return
`1`). This is a known extraction-vs-source gap, not a proof bug, but it
makes the statement a weaker spec than it appears. -/
theorem nth_root_lower_bound (a : u64) (n : u32) :
    ⦃ ⌜ 1 ≤ n.toNat ⌝ ⦄
    nth_root_u64.nth_root a n
    ⦃ ⇓ r => ⌜ r.toNat ^ n.toNat ≤ a.toNat ⌝ ⦄ := by
  sorry

/-- (UB) for `nth_root`: `(result + 1)^n > a` whenever `(r + 1)^n` is
representable in `u64` (vacuous otherwise).

Captures the `prop_nth_root_upper_bound` property test. Together with the
lower bound and `n ≥ 1`, this pins down the truncated principal `n`-th root
uniquely.

NOTE (left as `sorry`): inherits all the obstructions of
`nth_root_lower_bound` plus the deeper Newton-monovariant argument of the
generic-`n` descending sweep, where the per-step recurrence is
`xn := (a/x^{n-1} + (n-1) x) / n`. Proving termination implies
`(x+1)^n > a` requires (a) reasoning about the arithmetic of integer
quotients and powers, and (b) a fixpoint-stability lemma about the
generic-`n` Newton iteration, neither of which is exercised by any
reference example. -/
theorem nth_root_upper_bound (a : u64) (n : u32) :
    ⦃ ⌜ 1 ≤ n.toNat ⌝ ⦄
    nth_root_u64.nth_root a n
    ⦃ ⇓ r =>
        ⌜ (r.toNat + 1) ^ n.toNat < 2 ^ 64 →
            a.toNat < (r.toNat + 1) ^ n.toNat ⌝ ⦄ := by
  sorry

end Nth_root_u64Obligations
