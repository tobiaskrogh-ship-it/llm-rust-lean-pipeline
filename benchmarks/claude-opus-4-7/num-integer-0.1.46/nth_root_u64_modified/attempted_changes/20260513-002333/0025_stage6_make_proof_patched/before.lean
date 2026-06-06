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

/-- Newton-step strict decrease above the cube root: when `x³ > a` and
`x > 0`, the cube-root Newton step strictly decreases `x`. Parallels
`sqrt_step_strict_decrease`.

Proof outline:
  `x³ > a → a < x³ → a/x² < x → a/x² + 2x < 3x → (a/x² + 2x)/3 < x`.
The `a/x² < x` step from `a < x³ = x*(x*x)` uses `Nat.div_lt_iff_lt_mul`
(positive divisor `x*x`). The final `< x` step uses
`Nat.div_lt_iff_lt_mul` again on divisor 3. -/
private theorem cbrt_step_strict_decrease (a x : Nat) (hx : 0 < x)
    (h_above : x * x * x > a) : (a / (x * x) + 2 * x) / 3 < x := by
  have hxx_pos : 0 < x * x := Nat.mul_pos hx hx
  -- `a < x*(x*x) → a / (x*x) < x`.
  have h_xxx : x * (x * x) = x * x * x := (Nat.mul_assoc x x x).symm
  have h_div_lt : a / (x * x) < x := by
    rw [Nat.div_lt_iff_lt_mul hxx_pos, h_xxx]
    -- Goal: `a < x * x * x`.
    exact h_above
  have h_sum_lt : a / (x * x) + 2 * x < 3 * x := by omega
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 3)]
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
  -- Strong induction on `n.toNat` (recursion_example pattern adapted to
  -- a `partial_fixpoint` that returns `Option`).
  induction hm : n.toNat using Nat.strongRecOn generalizing n with
  | _ m ih =>
    by_cases hn0 : n.toNat = 0
    · -- Base case: n.toNat = 0, so n = 0.
      have hn_eq : n = 0 := UInt32.toNat_inj.mp (by rw [hn0]; rfl)
      subst hn_eq
      -- After subst, hm : (0 : u32).toNat = m, so m = 0.
      have hm_zero : m = 0 := by
        have : (0 : u32).toNat = 0 := rfl
        omega
      subst hm_zero
      -- Compute: `checked_pow_u64 x 0 = RustM.ok (Some 1)`.
      have h_base : nth_root_u64.checked_pow_u64 x 0
                      = RustM.ok (core_models.option.Option.Some 1) := by
        unfold nth_root_u64.checked_pow_u64
        rfl
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [h_base] at hk
        -- hk: RustM.ok (Some 1) = RustM.ok (Some k).
        -- The Hax `RustM` is `ExceptT Error Option`, so `RustM.ok v`
        -- is `some (Except.ok v)`. Three nested constructors to strip.
        have hk1 : k = 1 := by
          injection hk with h1
          injection h1 with h2
          injection h2 with h3
          exact h3.symm
        subst hk1
        have h_pow : x.toNat ^ (0 : Nat) < 2 ^ 64 := by
          rw [Nat.pow_zero]; decide
        refine ⟨rfl, ?_⟩
        exact h_pow
      · intro hN
        rw [h_base] at hN
        -- hN: RustM.ok (Some 1) = RustM.ok None — contradiction.
        exfalso
        injection hN with h1
        injection h1 with h2
        cases h2
    · -- Step case: 1 ≤ n.toNat.
      -- Stuck sub-goal: applying the IH at `(n-1).toNat < n.toNat` to recover
      --   `checked_pow_u64 x (n-1) = RustM.ok (Some prev) →
      --     prev.toNat = x.toNat^(n-1).toNat ∧ x.toNat^(n-1).toNat < 2^64`
      -- requires peeling the recursive call out of the `match` inside the
      -- `partial_fixpoint` body. Each case of the inner `match` (None /
      -- Some prev with x=0 / Some prev with prev > MAX/x / Some prev else)
      -- needs its own arithmetic chain:
      --   • None branch: lift `2^64 ≤ x^(n-1)` to `2^64 ≤ x^n` via
      --     `Nat.pow_succ` and monotonicity of `*x`.
      --   • Some 0 (x = 0) branch: 0^n = 0 < 2^64.
      --   • Some prev with `prev > MAX/x` branch: derive `prev*x > MAX`
      --     via `UInt64.le_div_iff_mul_le` and `Nat.add_one_le_iff`.
      --   • Some prev else branch: `prev*x < 2^64`, hence
      --     `UInt64.mulOverflow` is false, and `(prev*x).toNat = x^n`.
      -- Structural unblock: an `unfold` form of `partial_fixpoint` that
      -- exposes one recursive step (analog of `factorial_step` in
      -- `factorial_modified`) would let each `match` branch close
      -- mechanically. Without it, the recursive call cannot be peeled
      -- from inside the `partial_fixpoint` body.
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
  -- Stage 2 conversion to equational form (per `while_example/README.md`).
  rw [RustM.Triple_iff_BitVec]
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
             decide_eq_true_eq]
  -- Case split on the cascade of guards inside `sqrt_u64`.
  by_cases ha0 : a = 0
  · -- a = 0 branch: returns pure 0; `0^2 = 0 ≤ 0` ✓
    subst ha0
    refine ⟨?_, ?_⟩
    · decide
    · decide
  · -- a ≠ 0 branch — the proof of the loop case requires constructing a
    -- Hoare triple about `Loop.MonoLoopCombinator.while_loop` with the
    -- Newton invariant. After `rw [RustM.Triple_iff_BitVec]` the goal is
    -- `(sqrt_u64 a).toBVRustM.ok ∧ ...^2 ≤ a.toNat`; reducing the
    -- `toBVRustM` projection past the descending Newton sweep requires
    -- the manual loop-spec invocation pattern from
    -- `while_example/README.md`, instantiated at
    -- `loopInv := λ (x, xn) ↦ xn.toNat = (a.toNat/x.toNat + x.toNat)/2 ∧
    --              0 < x.toNat ∧ a.toNat < (x.toNat + 1)^2`
    -- and discharged via `sqrt_terminus_lower` for the lower-bound conjunct.
    -- Structural unblock: a `sqrt_loop_triple` lemma about
    -- `Loop.MonoLoopCombinator.while_loop` over the (x, xn) state — the
    -- exact analog of `gcd_loop_triple` in `gcd_while_modified`.
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
  rw [RustM.Triple_iff_BitVec]
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
             decide_eq_true_eq]
  by_cases ha0 : a = 0
  · -- a = 0: returns 0; postcondition `1 < 2^64 → 0 < 1`. ✓
    subst ha0
    refine ⟨?_, ?_⟩
    · decide
    · decide
  · -- a ≠ 0: structural unblock = `sqrt_step_strict_decrease` (stated as
    -- private theorem above) composed via a Hoare-triple about the
    -- descending Newton loop. Without that triple, the `toBVRustM`
    -- projection cannot be reduced past the loop.
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
  rw [RustM.Triple_iff_BitVec]
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
             decide_eq_true_eq]
  by_cases ha0 : a = 0
  · -- a = 0: returns 0; `0^3 = 0 ≤ 0` ✓
    subst ha0
    refine ⟨?_, ?_⟩
    · decide
    · decide
  · -- a ≠ 0: three sub-branches inside `cbrt_u64`:
    --   (i)   1 ≤ a < 8: returns pure 1; need `1 ≤ a.toNat` (have from `a ≠ 0`)
    --   (ii)  8 ≤ a ≤ u32::MAX: delegates to `cbrt_u32`; needs `cbrt_u32`
    --         correctness contract (Hacker's-Delight bit-trick loop) —
    --         structural unblock = a separately-verified `cbrt_u32_lower`
    --         lemma using a 4-variable loop invariant.
    --   (iii) a > u32::MAX: descending Newton sweep; terminus closed by
    --         `cbrt_terminus_lower` (proved above) once the loop's exit
    --         value is in hand — structural unblock = `cbrt_loop_triple`
    --         (Hoare triple over `Loop.MonoLoopCombinator.while_loop`).
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
  by_cases ha0 : a = 0
  · -- a = 0: returns 0; postcondition `1 < 2^64 → 0 < 1` ✓
    subst ha0
    refine ⟨?_, ?_⟩
    · decide
    · decide
  · -- a ≠ 0: three sub-branches as in `cbrt_lower_bound`. Same structural
    -- unblocks: `cbrt_u32_upper` contract for branch (ii), and
    -- `cbrt_step_strict_decrease` + `cbrt_loop_triple` for branch (iii).
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
  -- Discharge the vacuous-precondition case (`n.toNat = 0`) explicitly.
  by_cases hn0 : n.toNat = 0
  · rw [show decide (1 ≤ n.toNat) = false from
        decide_eq_false (by omega : ¬ (1 ≤ n.toNat))]
    simp
  · -- 1 ≤ n.toNat. The cascade splits into:
    --   n = 1: `nth_root a 1 = pure a`, postcondition `a.toNat ≤ a.toNat` ✓
    --   n = 2: delegates to `sqrt_u64` (uses `sqrt_lower_bound`)
    --   n = 3: delegates to `cbrt_u64` (uses `cbrt_lower_bound`)
    --   n ≥ 64 ∨ a < 1<<n: `pure 0` or `pure 1`
    --   else: descending Newton sweep over `(x, xn)` using
    --         `checked_pow_u64` (partial_fixpoint).
    -- Stuck sub-goal: closing the cascade requires:
    --   (a) the helper `checked_pow_u64_correct` (separate private theorem
    --       above, also `sorry` — its proof is the `recursion_example`
    --       pattern adapted to `Option`);
    --   (b) the Hoare triple about `Loop.MonoLoopCombinator.while_loop`
    --       with the generic-`n` Newton invariant
    --       `xn = (a/x^{n-1} + (n-1)*x)/n ∧ 0 < x`;
    --   (c) the generic-`n` terminus lemma
    --       `x ≤ (a/x^{n-1} + (n-1)*x)/n → x^n ≤ a` (the natural
    --       generalisation of `sqrt_terminus_lower`).
    -- Without these helpers the `(nth_root a n).toBVRustM` projection
    -- cannot be reduced past the Newton loop.
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
  by_cases hn0 : n.toNat = 0
  · -- vacuous: precondition `1 ≤ 0` is false
    rw [show decide (1 ≤ n.toNat) = false from
        decide_eq_false (by omega : ¬ (1 ≤ n.toNat))]
    simp
  · -- 1 ≤ n.toNat. Inherits the same five cascade branches as
    -- `nth_root_lower_bound`. Stuck sub-goal: the upper-bound conjunct
    -- requires a *strict* Newton-monovariant argument
    -- (`x^n > a → (a/x^{n-1} + (n-1)*x)/n < x`) on top of the lower-bound
    -- infrastructure. Structural unblocks:
    --   (a) `checked_pow_u64_correct` (above);
    --   (b) the Hoare triple about the generic-`n` Newton loop;
    --   (c) a `nth_root_step_strict_decrease` lemma generalising
    --       `sqrt_step_strict_decrease` to arbitrary `n ≥ 2`.
    sorry

end Nth_root_u64Obligations
