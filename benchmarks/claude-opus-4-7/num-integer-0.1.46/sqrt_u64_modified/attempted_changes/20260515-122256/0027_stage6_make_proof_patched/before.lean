-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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
`⌊√a⌋`. Core Lean exposes `Nat.log2` (used by the implementation's helper) but
**not** `Nat.sqrt`; Mathlib's `Nat.sqrt`/`Nat.sqrt_le'`/`Nat.lt_succ_sqrt'`
would close the bound obligations in one line each, but Mathlib is not
imported in this project.

The proof scaffolding below uses an *existential* postcondition
(`sqrt_postcondition` returns a `u64 r` satisfying both bounds) and derives
the specific-value obligations by uniqueness: if `r² ≤ x < (r+1)²` and
`r'² ≤ x < (r'+1)²` then `r = r'`. This avoids defining a custom `natSqrt`
function while still mapping each per-test obligation to a one-line
derivation. -/

/-! ### Newton iteration invariant (sqrt's two loops)

The Babylonian iteration converges to `⌊√a⌋`. The two loops play asymmetric
roles:

* Loop 1 (`x < xn`): grows `x` from a possibly-undershot initial guess up to
  a point where `x * x ≥ a`. Terminates because a single step from a state
  with `x * x < a` puts `xn ≥ ⌈√a⌉`, after which the loop condition is false.
* Loop 2 (`x > xn`): shrinks `x` while `xn = (a/x + x)/2 < x`. The standard
  fact `(a/x + x)/2 < x ↔ a < x * x` (over `Nat`, dividing on the left)
  shows this loop exits exactly when `x * x ≤ a`, i.e. when `x ≤ ⌊√a⌋`. -/

/-- Babylonian-step strict-descent lemma. When `x` is strictly above the
    integer square root (`x * x > a`), one Newton step strictly decreases `x`.
    No `Nat.sqrt` needed — the bound `x * x > a` is the only hypothesis.

    Proof: from `x * x > a` and `0 < x`, `a / x < x` (since `(a / x) * x ≤ a`
    and `a < x * x`). Hence `a / x + x < 2 * x`, and dividing by 2 gives
    `(a / x + x) / 2 < x`. -/
private theorem babylonian_step_descent (a x : Nat) (hx_pos : 0 < x)
    (h_above : a < x * x) : (a / x + x) / 2 < x := by
  -- `a / x ≤ x - 1` from `a < x * x`.
  have h_div_le : a / x < x := by
    have h_mul : a / x * x ≤ a := Nat.div_mul_le_self a x
    rcases Nat.lt_or_ge (a / x) x with hlt | hge
    · exact hlt
    · -- a / x ≥ x: contradiction with a / x * x ≤ a < x * x.
      exfalso
      have : x * x ≤ a / x * x := Nat.mul_le_mul_right x hge
      omega
  -- Therefore a / x + x < 2 * x = x * 2.
  have h_sum : a / x + x < x * 2 := by omega
  -- Use Nat.div_lt_iff_lt_mul: (n / k < m ↔ n < m * k) when k > 0.
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
  exact h_sum

/-- Converse direction: when `x` is at or below the integer square root
    (`x * x ≤ a`), one Newton step is at least `x`. Equivalently, the loop-2
    condition `x > xn` is false exactly when `x ≤ ⌊√a⌋`.

    Proof: from `x * x ≤ a`, dividing by `x > 0` gives `x ≤ a / x`. Hence
    `2 * x ≤ a/x + x`, which by `Nat.le_div_iff_mul_le` (taking `k = 2`) is
    equivalent to `x ≤ (a/x + x) / 2`. -/
private theorem babylonian_step_at_floor (a x : Nat) (hx_pos : 0 < x)
    (h_at_or_below : x * x ≤ a) : x ≤ (a / x + x) / 2 := by
  -- x ≤ a / x  iff  x * x ≤ a  (via Nat.le_div_iff_mul_le on x > 0).
  have h_le_div : x ≤ a / x :=
    (Nat.le_div_iff_mul_le hx_pos).mpr h_at_or_below
  -- Hence x * 2 ≤ a / x + x.
  have h_sum_ge : x * 2 ≤ a / x + x := by omega
  -- And x ≤ (a / x + x) / 2 follows from x * 2 ≤ a / x + x.
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr h_sum_ge
-- (Used by the structural unblock above; this is the second key Newton
-- inequality. Together with `babylonian_step_descent` they encode the full
-- contract of the Newton step. The remaining ingredient for closing
-- `sqrt_postcondition` is the loop-level reasoning: a Stage-1+2 derivation
-- showing the two-loop pipeline preserves and ends at `⌊√a⌋`.)

/-- Closed-form for `sqrt`: there exists a `u64 r` satisfying both bounds,
    and that's the returned value. From this one private theorem every
    obligation below derives in one or two lines.

    Substantive proof attempt:
    * Case-splits on `x.toNat < 4` vs `x.toNat ≥ 4`.
    * Closes the small-input branch (x.toNat ∈ {0,1,2,3}) completely via
      `unfold sqrt + rfl + decide`. The `a < 4` arm of the implementation
      returns directly without invoking any loop, so these reduce by
      computation.
    * Leaves the Newton-iteration branch (x.toNat ≥ 4) as the lone `sorry`.

    The two Newton-step inequalities (`babylonian_step_descent`,
    `babylonian_step_at_floor` above) are proved unconditionally and ready to
    plug into the loop-level reasoning. The structural unblock is detailed
    inline at the `sorry` site below (item 1: a standalone `log2_postcondition`
    derivation; item 2: an initial-guess overflow lemma; item 3: the two-loop
    Hoare triple chaining post(loop1) ⇒ pre(loop2)). -/
private theorem sqrt_postcondition (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r
      ∧ r.toNat * r.toNat ≤ x.toNat
      ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  -- Case split on the `a < 4` branch.
  rcases Nat.lt_or_ge x.toNat 4 with h_lt | h_ge
  · -- Small input branch: enumerate {0, 1, 2, 3}.
    -- Each value closes by unfolding `sqrt` (the `a < 4` branch returns directly,
    -- never entering any loop) and `decide` for the squeeze bounds.
    have h_enum : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 := by omega
    rcases h_enum with h | h | h | h
    · have hx : x = 0 := UInt64.toNat_inj.mp h
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
    · have hx : x = 1 := UInt64.toNat_inj.mp h
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
    · have hx : x = 2 := UInt64.toNat_inj.mp h
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
    · have hx : x = 3 := UInt64.toNat_inj.mp h
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
  · -- Newton-iteration branch (`x.toNat ≥ 4`).
    -- Substantive proof attempt: derive the concrete Nat-level bounds on
    -- the initial guess (so we can plug them into the loop invariants),
    -- then identify the specific stuck sub-goal.
    have hx_lt : x.toNat < 2 ^ 64 := x.toNat_lt
    have hx_ne_zero : x.toNat ≠ 0 := by omega
    -- Bound on `Nat.log2 x.toNat` from core Lean's `Nat.log2_lt`.
    have h_log2_lt : Nat.log2 x.toNat < 64 :=
      (Nat.log2_lt hx_ne_zero).mpr hx_lt
    have h_log2_le : Nat.log2 x.toNat ≤ 63 := Nat.le_of_lt_succ h_log2_lt
    -- x.toNat ≥ 4 = 2^2, so `Nat.log2 x.toNat ≥ 2 ≥ 1`.
    have h_pow2_le : (2 : Nat) ^ 2 ≤ x.toNat := by
      change 4 ≤ x.toNat; exact h_ge
    have h_log2_ge : 2 ≤ Nat.log2 x.toNat :=
      (Nat.le_log2 hx_ne_zero).mpr h_pow2_le
    -- Initial-guess shift count: k = (log2 + 1) / 2.
    -- For log2 ∈ [2, 63], k ∈ [1, 32].
    set k : Nat := (Nat.log2 x.toNat + 1) / 2 with hk_def
    have h_k_le_32 : k ≤ 32 := by unfold_let k; omega
    have h_k_pos : 1 ≤ k := by unfold_let k; omega
    have h_k_le_63 : k ≤ 63 := by omega
    -- The initial guess `1 << k` is positive and ≤ 2^32 < 2^64.
    have h_init_guess_lt : (2 : Nat) ^ k ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by decide) h_k_le_32
    have h_init_guess_lt_2_64 : (2 : Nat) ^ k < 2 ^ 64 := by
      have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
      omega
    have h_init_guess_pos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos _
    -- So the first u64 shift `1 <<< k` evaluates to `UInt64.ofNat (2^k)`,
    -- and the resulting value is positive (so `a /? x` never divides by zero
    -- in the loop bodies).
    --
    -- ------------------------------------------------------------------
    -- At this point, to close the goal we would need:
    --
    --   (Step A) `log2_postcondition_aux` — a separately-proved equational
    --   form for `sqrt_u64.log2 x = RustM.ok (UInt32.ofNat (Nat.log2 x.toNat))`.
    --   Tractable: mirror `Gcd_whileObligations.gcd_while_postcondition`'s
    --   Stage-1+2 pattern with loop invariant
    --   `y.toNat = x.toNat / 2 ^ count.toNat ∧ count.toNat ≤ 63`
    --   and termination measure `y.toNat`. The shift-by-1 body is total
    --   (1 < 64), and `count + 1` cannot overflow `u32` (count ≤ 63 ≪ 2^32).
    --   ~80 lines.
    --
    --   (Step B) An evaluation lemma: after substituting Step A, the
    --   expression `1 <<<? ((log2 a +? 1) /? 2)` reduces to
    --   `pure (UInt64.ofNat (2^k))` using `h_init_guess_lt_2_64` (no shift
    --   overflow, `k < 64`) and `if_neg (by decide : (2:u32) ≠ 0)` (no
    --   division-by-zero). ~20 lines.
    --
    --   (Step C) Hoare triple for Loop 1 (the `x < xn` Babylonian descent).
    --   Invariant: `0 < x ∧ x.toNat ≤ 2^32 ∧ x.toNat * x.toNat ≤ a.toNat ∨
    --              (x.toNat * x.toNat > a.toNat ∧ xn.toNat * xn.toNat ≥ a.toNat)`.
    --   Loop body is `x := xn; xn := (a/x + x)/2`. The strict-decrease
    --   witness on entry (`x < xn`) is `2^32 - x.toNat` (Nat-level), since
    --   after the first iteration `xn * xn ≥ a`, hence `x` is monotonically
    --   non-decreasing only one step then halts. ~120 lines.
    --
    --   (Step D) Hoare triple for Loop 2 (the `x > xn` polish loop).
    --   Invariant: `0 < x ∧ x.toNat * x.toNat ≥ a.toNat`.
    --   Strict-decrease witness: `x.toNat` (via `babylonian_step_descent`).
    --   Exit: `¬(x > xn)` ↔ `x ≤ xn`, which by `babylonian_step_at_floor`
    --   implies `x.toNat * x.toNat ≤ a.toNat` — combined with the invariant,
    --   `x.toNat * x.toNat = a.toNat` for perfect squares, or `x = ⌊√a⌋`
    --   strictly between (x.toNat)^2 ≤ a < (x.toNat + 1)^2. ~100 lines.
    --
    --   (Step E) Bind chaining of Steps A–D and `RustM.Triple_iff_BitVec`
    --   convert to equation. ~40 lines.
    --
    -- Stuck sub-goal (specific): Step A is the immediate blocker — without
    -- it we cannot reduce `sqrt_u64.log2 x` past its `while_loop` and so
    -- cannot evaluate the initial guess to a concrete value, which means
    -- the loop-1 invariant in Step C has no concrete starting witness.
    --
    -- Even though this branch leaves a `sorry`, the Nat-level bounds
    -- derived above (`h_log2_le`, `h_k_le_32`, `h_init_guess_lt_2_64`,
    -- `h_init_guess_pos`) are exactly the side conditions the next
    -- attempt will need when applying `haxShiftLeft_u64_spec` and
    -- `Nat.div_lt_iff_lt_mul` to discharge the initial-guess overflow
    -- check and the partial division `a /? (1 << k)` in Step B.
    --
    -- Structural unblock: implement `log2_postcondition_aux` as a
    -- standalone `private theorem` mirroring `gcd_while_postcondition`.
    -- The remaining steps fall into place mechanically thereafter.
    sorry

/-! ### Uniqueness of the integer square root

`r² ≤ x < (r+1)²` characterises `r = ⌊√x⌋` uniquely. The uniqueness lemma
is a routine `Nat`-level case analysis dischargeable by `omega` plus a
monotonicity argument on squaring. -/

/-- If `r² ≤ x < (r+1)²` and `s² ≤ x < (s+1)²`, then `r = s`.
    Proof: WLOG `r ≤ s`. Then `r² ≤ s²` and `(s+1)² > x ≥ r²`, so `s ≥ r`.
    If `r < s`, then `s ≥ r + 1`, so `s² ≥ (r+1)² > x`, contradicting
    `s² ≤ x`. Hence `r = s`. -/
private theorem nat_sqrt_unique (x r s : Nat)
    (hr_le : r * r ≤ x) (hr_lt : x < (r + 1) * (r + 1))
    (hs_le : s * s ≤ x) (hs_lt : x < (s + 1) * (s + 1)) :
    r = s := by
  rcases Nat.lt_trichotomy r s with hlt | heq | hgt
  · -- r < s: s ≥ r + 1, so s² ≥ (r+1)² > x, contradicting s² ≤ x.
    exfalso
    have hge : r + 1 ≤ s := hlt
    have h_sq_le_sq : (r + 1) * (r + 1) ≤ s * s :=
      Nat.mul_le_mul hge hge
    omega
  · exact heq
  · -- r > s: r ≥ s + 1, so r² ≥ (s+1)² > x, contradicting r² ≤ x.
    exfalso
    have hge : s + 1 ≤ r := hgt
    have h_sq_le_sq : (s + 1) * (s + 1) ≤ r * r :=
      Nat.mul_le_mul hge hge
    omega

/-- Concrete uniqueness on `u64`: if both `r` and the supplied `target` satisfy
    the squeeze bounds at `x.toNat`, then `r = UInt64.ofNat target`. -/
private theorem sqrt_value_unique (x : u64) (target : Nat)
    (h_target_lt : target < 2 ^ 64)
    (h_le : target * target ≤ x.toNat)
    (h_lt : x.toNat < (target + 1) * (target + 1))
    (r : u64)
    (hr_le : r.toNat * r.toNat ≤ x.toNat)
    (hr_lt : x.toNat < (r.toNat + 1) * (r.toNat + 1)) :
    r = UInt64.ofNat target := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' h_target_lt]
  exact nat_sqrt_unique x.toNat r.toNat target hr_le hr_lt h_le h_lt

/-! ## Postcondition: lower bound (`r² ≤ x`)

Captures the property test `prop_sqrt_lower_bound`: for the returned root `r`,
`r.toNat * r.toNat ≤ x.toNat`. A buggy implementation that returns too large a
value (e.g. `x` itself, or `r + 1` for non-perfect squares) is caught here. -/
theorem sqrt_lower_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r ∧ r.toNat * r.toNat ≤ x.toNat := by
  obtain ⟨r, hsqrt, hle, _⟩ := sqrt_postcondition x
  exact ⟨r, hsqrt, hle⟩

/-! ## Postcondition: upper bound (`x < (r+1)²`) -/
theorem sqrt_upper_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r
      ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hsqrt, _, hlt⟩ := sqrt_postcondition x
  exact ⟨r, hsqrt, hlt⟩

/-! ## Totality / no panic -/
theorem sqrt_total (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  obtain ⟨r, hsqrt, _, _⟩ := sqrt_postcondition x
  exact ⟨r, hsqrt⟩

/-! ## Specific values: small inputs

The `a < 4` branch returns directly without entering any loop, so these four
close by `rfl` after unfolding `sqrt`. -/

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

/-- `x = 4` is the smallest input that enters the loop branch.
    Uniqueness of the squeeze bounds at `x = 4` pins `r = 2`. -/
theorem sqrt_four : sqrt_u64.sqrt 4 = RustM.ok 2 := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (4 : u64)
  rw [hsqrt]
  congr 1
  have h4 : (4 : u64).toNat = 4 := rfl
  rw [h4] at hle hlt
  exact sqrt_value_unique (4 : u64) 2 (by decide) (by decide) (by decide) r
    (by rw [h4]; exact hle) (by rw [h4]; exact hlt)

/-! ## Specific values: doctest

`x = 12345 * 12345`, `x = 12345 * 12345 + 1`, `x = 12345 * 12345 - 1`.
Each pins down the result via uniqueness of the squeeze bounds. -/

theorem sqrt_doctest_exact :
    sqrt_u64.sqrt (12345 * 12345 : u64) = RustM.ok (12345 : u64) := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (12345 * 12345 : u64)
  rw [hsqrt]
  congr 1
  have hx : (12345 * 12345 : u64).toNat = 12345 * 12345 := by decide
  rw [hx] at hle hlt
  exact sqrt_value_unique (12345 * 12345 : u64) 12345
    (by decide) (by decide) (by decide) r
    (by rw [hx]; exact hle) (by rw [hx]; exact hlt)

theorem sqrt_doctest_plus_one :
    sqrt_u64.sqrt (12345 * 12345 + 1 : u64) = RustM.ok (12345 : u64) := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (12345 * 12345 + 1 : u64)
  rw [hsqrt]
  congr 1
  have hx : (12345 * 12345 + 1 : u64).toNat = 12345 * 12345 + 1 := by decide
  rw [hx] at hle hlt
  exact sqrt_value_unique (12345 * 12345 + 1 : u64) 12345
    (by decide) (by decide) (by decide) r
    (by rw [hx]; exact hle) (by rw [hx]; exact hlt)

theorem sqrt_doctest_minus_one :
    sqrt_u64.sqrt (12345 * 12345 - 1 : u64) = RustM.ok (12344 : u64) := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (12345 * 12345 - 1 : u64)
  rw [hsqrt]
  congr 1
  have hx : (12345 * 12345 - 1 : u64).toNat = 12345 * 12345 - 1 := by decide
  rw [hx] at hle hlt
  exact sqrt_value_unique (12345 * 12345 - 1 : u64) 12344
    (by decide) (by decide) (by decide) r
    (by rw [hx]; exact hle) (by rw [hx]; exact hlt)

end Sqrt_u64Obligations
