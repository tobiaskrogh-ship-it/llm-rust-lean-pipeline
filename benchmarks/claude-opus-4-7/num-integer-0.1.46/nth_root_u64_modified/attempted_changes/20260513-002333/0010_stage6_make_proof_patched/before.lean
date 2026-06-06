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
private theorem sqrt_terminus_lower (a x : Nat) (hx : 0 < x)
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
private theorem cbrt_terminus_lower (a x : Nat) (hx : 0 < x)
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
  -- Rewrite `x * x * x = x * (x * x)` using `Nat.mul_assoc`.
  have h_assoc : x * x * x = x * (x * x) := Nat.mul_assoc x x x
  rw [h_assoc]
  exact Nat.le_trans h_mul h_div

/-! ## Helper lemmas stating the *missing* infrastructure.

These are the lemmas a closed proof of the Newton-sweep upper bounds and of
`nth_root` would need. They are stated here so a future pass has the exact
shape it needs; their proofs are themselves left as `sorry` because they
encode the deeper Newton-monovariant argument that is uncovered by any
reference example in the proof-pattern library. -/

/-- Newton-step strict decrease above the root: when `x² > a` and `x > 0`,
the Newton step strictly decreases `x`. This is the *monovariant* of the
descending Newton sweep: while `x` is above the true square root, the
update `x ↦ (a/x + x)/2` produces a strictly smaller `x`. Contrapositive:
at the loop's exit (`x ≤ xn` ⟺ `(a/x + x)/2 ≥ x`), we must have `x² ≤ a`,
which combined with `x² ≤ a < (x+1)²` (the upper-bound claim) pins down
`x = ⌊√a⌋`.

Proof outline (not yet completed):
  `x² > a → a < x*x → a/x < x → a/x + x < 2x → (a/x + x)/2 < x`.
The middle step `a/x < x` from `a < x*x` uses `Nat.div_lt_iff_lt_mul`
(positive divisor); the final step `(a/x + x)/2 < x` from
`a/x + x < 2x = 2*x` uses `Nat.div_lt_iff_lt_mul` again on divisor 2. -/
private theorem sqrt_step_strict_decrease (a x : Nat) (hx : 0 < x)
    (h_above : x * x > a) : (a / x + x) / 2 < x := by
  -- Step 1: `a < x*x → a / x < x` (for `x > 0`).
  have h_div_lt : a / x < x := by
    rw [Nat.div_lt_iff_lt_mul hx]
    -- Goal: `a < x * x`.
    exact h_above
  -- Step 2: `a/x < x → a/x + x < 2 * x`.
  have h_sum_lt : a / x + x < 2 * x := by omega
  -- Step 3: `a/x + x < 2 * x → (a/x + x) / 2 < x`.
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
  -- Goal: `a / x + x < 2 * x`. omega closes from `h_sum_lt`.
  omega

/-- Functional correctness of `checked_pow_u64`: when the result is
`Some k`, then `k.toNat = x.toNat ^ n.toNat` and `x.toNat ^ n.toNat <
2^64`; when the result is `None`, then `x.toNat ^ n.toNat ≥ 2^64`.

This is the standard correctness contract of a `checked_pow` operation.
The proof goes by induction on `n.toNat` using `Nat.strongRecOn` and
follows the `recursion_example` pattern, but applied to a `partial_fixpoint`
that returns an `Option`. -/
private theorem checked_pow_u64_correct (x : u64) (n : u32) :
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
  -- Bridge to BitVec equational form (canonical Stage-2 conversion from
  -- `while_example/README.md`). After this rewrite the goal becomes a
  -- boolean claim about `(sqrt_u64 a).toBVRustM.ok` and the value.
  rw [RustM.Triple_iff_BitVec]
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
             decide_eq_true_eq]
  -- Stuck sub-goal: `(sqrt_u64 a).toBVRustM.ok = true ∧
  --                 (sqrt_u64 a).toBVRustM.val.toNat ^ 2 ≤ a.toNat`.
  -- The first conjunct (totality) requires showing the descending Newton
  -- loop terminates without panicking on `(a/x + x) >>> 1`; the second
  -- conjunct uses `sqrt_terminus_lower` once the loop's exit value is in
  -- hand. Both depend on a Hoare-triple about the underlying
  -- `Loop.MonoLoopCombinator.while_loop` with invariant
  -- `xn.toNat = (a.toNat / x.toNat + x.toNat) / 2 ∧ x.toNat > 0`, which
  -- is the structural-unblock named in this theorem's docstring.
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
  -- Canonical Stage-2 conversion. Reduces the triple to a boolean
  -- claim about `(sqrt_u64 a).toBVRustM`.
  rw [RustM.Triple_iff_BitVec]
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
             decide_eq_true_eq]
  -- Stuck sub-goal: the Newton-monovariant claim
  -- `(sqrt_u64 a).toBVRustM.val.toNat = ⌊√a.toNat⌋`. The lower bound
  -- (`sqrt_terminus_lower` above) gives `r² ≤ a`; the matching strict
  -- upper bound `(r+1)² > a` requires that the descending sweep was
  -- initialised from above the root and is strictly decreasing while
  -- `x > √a`. The structural-unblock named in this theorem's docstring
  -- is `sqrt_step_strict_decrease` (stated above as a private theorem
  -- with its own focused `sorry`).
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
  -- Canonical Stage-2 conversion.
  rw [RustM.Triple_iff_BitVec]
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
             decide_eq_true_eq]
  -- Stuck sub-goal splits in two cases:
  --   (i)  `a ≤ u32::MAX`: result is `cbrt_u32 a` lifted; the Hacker's-
  --        Delight bit-trick loop with invariant
  --        `y³ + bit-residual = a` requires a multi-variable loop
  --        invariant uncovered in the example library.
  --   (ii) `a > u32::MAX`: descending Newton sweep; terminus closes via
  --        `cbrt_terminus_lower` (proved above) once the loop's exit
  --        value `(x, xn)` is in hand.
  -- The structural-unblock is the same as for `sqrt_lower_bound`:
  -- a Hoare-triple about `Loop.MonoLoopCombinator.while_loop` with the
  -- Newton invariant `xn = (a/x² + 2x)/3`, plus a separately-verified
  -- `cbrt_u32` correctness contract for sub-case (i).
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
  rw [RustM.Triple_iff_BitVec]
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
             decide_eq_true_eq]
  -- Combines the cbrt-via-cbrt_u32 delegation of `cbrt_lower_bound`
  -- with the Newton-monovariant of `sqrt_upper_bound`. The structural-
  -- unblock is a `cbrt_terminus_upper` cousin of `sqrt_terminus_upper`
  -- (currently absent), plus a `cbrt_u32` upper-bound contract.
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
  rw [RustM.Triple_iff_BitVec]
  -- Stuck sub-goal: case-split on `n.toNat ∈ {1, 2, 3, ≥4}`.
  -- The `n = 2, 3` cases reduce to `sqrt_lower_bound` / `cbrt_lower_bound`
  -- (themselves uncovered). The `n ≥ 4` case is a generic-`n` descending
  -- Newton sweep that calls `checked_pow_u64` (partial_fixpoint).
  -- Structural unblocks: (a) `checked_pow_u64_correct` (stated above as
  -- a private theorem with its own sorry — would close via the
  -- `recursion_example` pattern adapted to `Option`), and (b) the
  -- generic-`n` analogues of `sqrt_terminus_lower` (provable: same
  -- argument with `x^{n-1}` in place of `x`).
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
  rw [RustM.Triple_iff_BitVec]
  -- Inherits all obstructions of `nth_root_lower_bound`. The deeper
  -- Newton-monovariant claim for the generic-`n` sweep requires a
  -- `nth_root_terminus_upper` lemma analogous to `sqrt_terminus_upper`
  -- (currently absent from the example library and from this file).
  sorry

end Nth_root_u64Obligations
