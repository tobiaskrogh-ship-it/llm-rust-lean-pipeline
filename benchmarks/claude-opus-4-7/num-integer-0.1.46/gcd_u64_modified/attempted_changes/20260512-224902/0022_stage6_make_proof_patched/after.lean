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

/-! ## Nat-level helper lemmas for Stein's algorithm

These are the algebraic facts the loop body steps rely on. They are
purely about `Nat.gcd`; once proved, they transfer mechanically to the
u64 setting via `UInt64.toNat_sub_of_le'`, `UInt64.toNat_shiftRight`,
`UInt64.toNat_or`, and `UInt64.toNat_and` (all in the prelude). -/

/-- Both arguments even ⇒ pull out a factor of 2.

    `Nat.gcd_mul_left` is in the Lean stdlib (`Init.Data.Nat.Gcd`). -/
private theorem nat_gcd_two_mul_two_mul (a b : Nat) :
    Nat.gcd (2 * a) (2 * b) = 2 * Nat.gcd a b :=
  Nat.gcd_mul_left 2 a b

/-- Subtraction step: when `b ≤ a`, `gcd a b = gcd (a - b) b`.

    Direct two-side `dvd` argument via `Nat.dvd_sub` and `Nat.dvd_add`
    on the cancellation `(a - b) + b = a`. -/
private theorem nat_gcd_sub_left (a b : Nat) (h : b ≤ a) :
    Nat.gcd a b = Nat.gcd (a - b) b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.dvd_sub (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    · exact Nat.gcd_dvd_right a b
  · apply Nat.dvd_gcd
    · have h1 : Nat.gcd (a - b) b ∣ (a - b) := Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd (a - b) b ∣ b := Nat.gcd_dvd_right _ _
      have hsum : Nat.gcd (a - b) b ∣ ((a - b) + b) := Nat.dvd_add h1 h2
      rw [Nat.sub_add_cancel h] at hsum
      exact hsum
    · exact Nat.gcd_dvd_right _ _

/-! ### Euclid-style helpers

When `a` is even and `b` is odd, the factor 2 in `2 * a` does not
divide `b`, so halving the left argument preserves `Nat.gcd`. Proved
in two pieces below: a "local Euclid lemma" `nat_odd_dvd_two_mul`
that does the heavy lifting, then a wrapper. -/

/-- Local Euclid-lemma helper: an odd divisor of `2 * a` divides `a`.

    Direct proof: from `d ∣ 2 * a`, write `2 * a = d * q`. Since `d` is
    odd, `q` must be even. Write `q = 2 * q'`; cancel 2 to get
    `a = d * q'`. -/
private theorem nat_odd_dvd_two_mul (d a : Nat) (hd : d % 2 = 1)
    (h : d ∣ 2 * a) : d ∣ a := by
  obtain ⟨q, hq⟩ := h
  -- 2 * a = d * q.  Show q is even.
  have hq_even : q % 2 = 0 := by
    have hl : (2 * a) % 2 = 0 := by omega
    rw [hq] at hl
    have hmul : (d * q) % 2 = (d % 2 * (q % 2)) % 2 := Nat.mul_mod d q 2
    rw [hmul, hd, Nat.one_mul] at hl
    omega
  -- Now write q = 2 * q'.
  obtain ⟨q', hq'⟩ : ∃ q', q = 2 * q' := by
    refine ⟨q / 2, ?_⟩
    have := Nat.div_add_mod q 2
    omega
  refine ⟨q', ?_⟩
  -- From 2 * a = d * (2 * q') = 2 * (d * q'), cancel 2.
  have heq : 2 * a = 2 * (d * q') := by
    rw [hq, hq']
    rw [Nat.mul_left_comm]
  exact Nat.eq_of_mul_eq_mul_left (by decide : (0 : Nat) < 2) heq

/-- "One even, one odd" gcd reduction:
    `Nat.gcd (2 * a) b = Nat.gcd a b` when `b` is odd. -/
private theorem nat_gcd_two_mul_left_odd_right (a b : Nat) (hb : b % 2 = 1) :
    Nat.gcd (2 * a) b = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · -- gcd(2a, b) ∣ gcd(a, b).
    have hg_dvd_2a : Nat.gcd (2 * a) b ∣ 2 * a := Nat.gcd_dvd_left _ _
    have hg_dvd_b : Nat.gcd (2 * a) b ∣ b := Nat.gcd_dvd_right _ _
    have hg_odd : Nat.gcd (2 * a) b % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (Nat.gcd (2 * a) b) with he | ho
      · exfalso
        have h2_dvd : (2 : Nat) ∣ Nat.gcd (2 * a) b := by
          rw [Nat.dvd_iff_mod_eq_zero]; exact he
        have h2_dvd_b : (2 : Nat) ∣ b := Nat.dvd_trans h2_dvd hg_dvd_b
        rw [Nat.dvd_iff_mod_eq_zero] at h2_dvd_b
        omega
      · exact ho
    have hg_dvd_a : Nat.gcd (2 * a) b ∣ a :=
      nat_odd_dvd_two_mul _ _ hg_odd hg_dvd_2a
    exact Nat.dvd_gcd hg_dvd_a hg_dvd_b
  · -- gcd(a, b) ∣ gcd(2a, b).
    apply Nat.dvd_gcd
    · -- gcd(a, b) ∣ a, and a ∣ 2*a, so gcd(a, b) ∣ 2*a.
      exact Nat.dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_mul_left a 2)
    · exact Nat.gcd_dvd_right a b

/-- Strip-a-2 step on the left, when the right argument is odd. -/
private theorem nat_gcd_div_two_left_odd_right
    (m n : Nat) (hm : m % 2 = 0) (hn : n % 2 = 1) :
    Nat.gcd m n = Nat.gcd (m / 2) n := by
  have hm2 : 2 * (m / 2) = m := by
    have := Nat.div_add_mod m 2
    omega
  have h := nat_gcd_two_mul_left_odd_right (m / 2) n hn
  rw [hm2] at h
  exact h

/-- Both even ⇒ gcd halves down with a factor of 2 absorbed.
    Direct consequence of `nat_gcd_two_mul_two_mul` (= `Nat.gcd_mul_left`)
    once we write `m = 2 * (m / 2)` and similarly for `n`. -/
private theorem nat_gcd_div_two_both_even (m n : Nat)
    (hm : m % 2 = 0) (hn : n % 2 = 0) :
    Nat.gcd m n = 2 * Nat.gcd (m / 2) (n / 2) := by
  have hm2 : 2 * (m / 2) = m := by have := Nat.div_add_mod m 2; omega
  have hn2 : 2 * (n / 2) = n := by have := Nat.div_add_mod n 2; omega
  have h := nat_gcd_two_mul_two_mul (m / 2) (n / 2)
  rw [hm2, hn2] at h
  exact h

/-- Right-symmetric version of `nat_gcd_div_two_left_odd_right`:
    `Nat.gcd m n = Nat.gcd m (n / 2)` when `m` is odd and `n` is even.
    Uses `Nat.gcd_comm` to flip and reuse the left version. -/
private theorem nat_gcd_div_two_right_odd_left
    (m n : Nat) (hm : m % 2 = 1) (hn : n % 2 = 0) :
    Nat.gcd m n = Nat.gcd m (n / 2) := by
  rw [Nat.gcd_comm m n, Nat.gcd_comm m (n / 2)]
  exact nat_gcd_div_two_left_odd_right n m hn hm

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

/-! ## Nat-level body-step content (L1, L2/L3/L5/L6, L4)

These are the Nat-level *content* of each loop body's per-iteration
discharge. The u64-level Hoare-triple body step wraps each of these
under the no-overflow rewrites (`>>>?` is always-ok shift-right;
`-?` no-underflow via `UInt64.subOverflow_iff`; `+?` no-overflow via
`UInt32.addOverflow_iff`) — see e.g. `while_example`'s
`body_step_nat`. -/

/-- L1 body step (Nat level): when both `m, n` are even and `m > 0`,
    halving both decreases `m + n`, preserves positivity, and
    preserves `gcd m n * 2^shift` (after incrementing `shift` by 1
    on the LHS). -/
private theorem strip_common_two_step_nat
    (m n : Nat) (hm_pos : m > 0) (hn_pos : n > 0)
    (hm_even : m % 2 = 0) (hn_even : n % 2 = 0) :
    m / 2 + n / 2 < m + n ∧
    m / 2 > 0 ∧ n / 2 > 0 ∧
    2 * Nat.gcd (m / 2) (n / 2) = Nat.gcd m n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · exact (nat_gcd_div_two_both_even m n hm_even hn_even).symm

/-- L2/L3/L5/L6 body step (Nat level): when `m` is even and `n` is odd
    and `m > 0`, halving `m` decreases it, keeps it positive, and
    preserves `gcd m n`. -/
private theorem strip_two_step_nat
    (m n : Nat) (hm_pos : m > 0) (hm_even : m % 2 = 0)
    (hn_odd : n % 2 = 1) :
    m / 2 < m ∧ m / 2 > 0 ∧ Nat.gcd (m / 2) n = Nat.gcd m n := by
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · exact (nat_gcd_div_two_left_odd_right m n hm_even hn_odd).symm

/-- L4 body step (Nat level), `m > n` branch: when `m, n` both odd and
    `m > n > 0`, subtracting `n` from `m` gives an even positive result
    and preserves `gcd`. (The follow-up strip-2 substep is handled by
    `strip_two_step_nat` above, on the post-subtraction `m - n`.) -/
private theorem sub_step_nat_m_gt_n
    (m n : Nat) (hm_odd : m % 2 = 1) (hn_odd : n % 2 = 1)
    (hmn : m > n) (hn_pos : n > 0) :
    (m - n) > 0 ∧ (m - n) % 2 = 0 ∧
    Nat.gcd (m - n) n = Nat.gcd m n := by
  refine ⟨?_, ?_, ?_⟩
  · omega
  · -- odd - odd = even
    omega
  · exact (nat_gcd_sub_left m n (Nat.le_of_lt hmn)).symm

/-- L4 body step (Nat level), `n > m` branch: symmetric. -/
private theorem sub_step_nat_n_gt_m
    (m n : Nat) (hm_odd : m % 2 = 1) (hn_odd : n % 2 = 1)
    (hnm : n > m) (hm_pos : m > 0) :
    (n - m) > 0 ∧ (n - m) % 2 = 0 ∧
    Nat.gcd m (n - m) = Nat.gcd m n := by
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · -- gcd m (n - m) = gcd (n - m) m = gcd n m = gcd m n via comm.
    rw [Nat.gcd_comm m (n - m), Nat.gcd_comm m n]
    exact (nat_gcd_sub_left n m (Nat.le_of_lt hnm)).symm

/-- **Central characterization** — `gcd_u64.gcd` computes `Nat.gcd`
    exactly, cast back to `u64`.

    Partial proof leaves a single `sorry`. Work done in the proof body:
      * The two boundary cases (`x = 0`, `y = 0`) are closed via
        `gcd_zero_left`/`gcd_zero_right` and `Nat.gcd_zero_left`/`right`.
      * In the non-boundary case, `gcd_u64.gcd` is `unfold`ed and the
        early-return guard `(x == 0 || y == 0)` is reduced to `false`
        using `hx`, `hy`, leaving the else-branch (four sequential
        `rust_primitives.hax.while_loop` calls + final `m <<<? shift`)
        exposed.

    Nat-level **body-step** helpers, one per loop kind (all closed):
      * `strip_common_two_step_nat` — L1 body discharge content.
      * `strip_two_step_nat`        — L2/L3/L5/L6 body discharge content.
      * `sub_step_nat_m_gt_n`       — L4 body, `m > n` branch.
      * `sub_step_nat_n_gt_m`       — L4 body, `n > m` branch.
    Each bundles (termination decrease, positivity preserved, gcd
    preserved). Together these cover **every per-iteration
    discharge** any body step needs.
===
    Nat-level helpers developed above (all closed, no `sorry`):
      * `nat_gcd_sub_left` — `gcd a b = gcd (a-b) b` when `b ≤ a`.
      * `nat_gcd_two_mul_two_mul` — `gcd (2a) (2b) = 2 * gcd a b`.
      * `nat_gcd_two_mul_left_odd_right` and the convenience variants
        `nat_gcd_div_two_left_odd_right`, `nat_gcd_div_two_both_even`,
        `nat_gcd_div_two_right_odd_left` — all four "strip-a-2" gcd
        preservations.

    Nat-level **body-step** helpers, one per loop kind (all closed):
      * `strip_common_two_step_nat` — L1 body discharge content.
      * `strip_two_step_nat`        — L2/L3/L5/L6 body discharge content.
      * `sub_step_nat_m_gt_n`       — L4 body, `m > n` branch.
      * `sub_step_nat_n_gt_m`       — L4 body, `n > m` branch.
    Each bundles (termination decrease, positivity preserved, gcd
    preserved). Together these cover **every per-iteration
    discharge** any body step needs.
===
    Nat-level helpers developed above (all closed, no `sorry`):
      * `nat_gcd_sub_left` — `gcd a b = gcd (a-b) b` when `b ≤ a`.
      * `nat_gcd_two_mul_two_mul` — `gcd (2a) (2b) = 2 * gcd a b`.
      * `nat_gcd_two_mul_left_odd_right` and the convenience variants
        `nat_gcd_div_two_left_odd_right`, `nat_gcd_div_two_both_even`,
        `nat_gcd_div_two_right_odd_left` — all four "strip-a-2" gcd
        preservations.

    Nat-level **body-step** helpers, one per loop kind (all closed):
      * `strip_common_two_step_nat` — L1 body discharge content.
      * `strip_two_step_nat`        — L2/L3/L5/L6 body discharge content.
      * `sub_step_nat_m_gt_n`       — L4 body, `m > n` branch.
      * `sub_step_nat_n_gt_m`       — L4 body, `n > m` branch.
    Each bundles (termination decrease, positivity preserved, gcd
    preserved). Together these cover **every per-iteration
    discharge** any body step needs.
===
    Nat-level **body-step** helpers, one per loop kind (all closed):
      * `strip_common_two_step_nat` — L1 body discharge content.
      * `strip_two_step_nat`        — L2/L3/L5/L6 body discharge content.
      * `sub_step_nat_m_gt_n`       — L4 body, `m > n` branch.
      * `sub_step_nat_n_gt_m`       — L4 body, `n > m` branch.
    Each bundles (termination decrease, positivity preserved, gcd
    preserved). Together these cover **every per-iteration
    discharge** any body step needs.
===
    Nat-level helpers developed above (all closed, no `sorry`):
      * `nat_gcd_sub_left` — `gcd a b = gcd (a-b) b` when `b ≤ a`.
      * `nat_gcd_two_mul_two_mul` — `gcd (2a) (2b) = 2 * gcd a b`.
      * `nat_gcd_two_mul_left_odd_right` and the convenience variants
        `nat_gcd_div_two_left_odd_right`, `nat_gcd_div_two_both_even`,
        `nat_gcd_div_two_right_odd_left` — all four "strip-a-2" gcd
        preservations.

    Nat-level **body-step** helpers, one per loop kind (all closed):
      * `strip_common_two_step_nat` — L1 body discharge content.
      * `strip_two_step_nat`        — L2/L3/L5/L6 body discharge content.
      * `sub_step_nat_m_gt_n`       — L4 body, `m > n` branch.
      * `sub_step_nat_n_gt_m`       — L4 body, `n > m` branch.
    Each bundles (termination decrease, positivity preserved, gcd
    preserved). Together these cover **every per-iteration
    discharge** any body step needs.

    Stuck sub-goal: the equation
    ```
      ( do let shift := 0
           let ⟨m,n,shift⟩ ← while_loop L1 …    -- strip common 2s
           let m ← while_loop L2 …              -- strip 2s from m
           let n ← while_loop L3 …              -- strip 2s from n
           let ⟨m,n⟩ ← while_loop L4 …          -- outer, nests L5/L6
           m <<<? shift )
      = RustM.ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat))
    ```
    on six **nested** `rust_primitives.hax.while_loop` calls. Each
    loop's partial-fixpoint definition does not reduce past one
    iteration; the standard discharge (cf. the `while_example` README)
    is two-stage: build a Hoare triple via `Spec.MonoLoopCombinator.while_loop`
    with a strong invariant + termination measure, then convert to the
    equation via `RustM.Triple_iff_BitVec` and a `RustM`-case-split.
    Applying that pattern here means writing six body-step lemmas
    (one per loop) and composing them with five `Triple.bind` links —
    roughly 250-350 lines of tactic code that no current
    `proof_patterns/` example demonstrates (the closest is
    `proof_patterns/gcd_while_modified`, which has a single flat
    loop).

    **Structural unblock** (what would close this lemma in one pass):
      1. A worked example in `proof_patterns/` exercising **nested**
         `rust_primitives.hax.while_loop` — currently flagged by the
         selector as a library gap. The composition pattern at each
         nesting level (especially L4 → L5/L6 inside the body) is
         non-trivial to discover from scratch and ought to be
         documented once and reused.
      2. A separately-verified bitwise-OR strict-decrease helper:
         `m, n odd ∧ m > n → ((m - n) >>> k) ||| n < m ||| n`
         (for the smallest `k ≥ 1` that makes the LHS odd). This is
         the natural termination measure for L4 — the current
         workaround would use `m.toNat + n.toNat` instead, but the
         Rust source carries `loop_decreases!(m | n)`, so the
         extracted shape requires matching the `m | n` measure.
      3. Once (1) and (2) land, the gcd-preservation steps in every
         body discharge are mechanically supplied by the
         `nat_gcd_*` helpers above; the proof reduces to algebra over
         `UInt64.toNat`-bridge lemmas (all in the prelude). -/
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
  -- Substantive attempt: unfold gcd_u64.gcd, reduce the boolean
  -- early-return guard using `hx : x ≠ 0` and `hy : y ≠ 0`, and
  -- expose the inner do-block containing the four sequential
  -- `rust_primitives.hax.while_loop` calls.
  have hxb : (x == (0 : u64)) = false := by simp [hx]
  have hyb : (y == (0 : u64)) = false := by simp [hy]
  simp only [gcd_u64.gcd, rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, hxb, hyb, Bool.or_self]
  -- After this we should have the else-branch exposed: the four
  -- sequential while_loop calls and the final `m <<<? shift`.
  --
  -- Stuck sub-goal — the loop chain. Proving the equation requires
  -- a Hoare-triple-then-equation conversion via `RustM.Triple_iff_BitVec`
  -- for the full 6-nested-loop algorithm, with invariants and
  -- termination measures supplied for each loop. The Nat-level helpers
  -- developed above (nat_gcd_two_mul_two_mul, nat_gcd_sub_left,
  -- nat_gcd_div_two_left_odd_right, nat_gcd_div_two_both_even,
  -- nat_gcd_div_two_right_odd_left) furnish every gcd-preservation
  -- step in the body discharges; the remaining work is:
  --   (i)   build a 6-layer composite Hoare triple using
  --         `Std.Do.Spec.MonoLoopCombinator.while_loop` for each loop;
  --   (ii)  thread the loop-termination measures through the
  --         `Triple.bind` composition between loops;
  --   (iii) prove no-overflow for `m <<<? shift` at the end using the
  --         invariant `m.toNat * 2^shift.toNat ≤ x.toNat` maintained
  --         since L1.
  -- These pieces are mechanical given the helpers but writing all
  -- six body steps is ~300 lines of tactic code; deferred. See the
  -- structural-unblock list in the theorem's outer docstring.
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
  rw [gcd_characterization]
  -- Goal: ⦃True⦄ RustM.ok (UInt64.ofNat (Nat.gcd x y)) ⦃⇓ g => g ∣ x⦄
  -- `RustM.ok v` is defeq to `pure v`; apply Triple.pure.
  refine Triple.pure _ ?_
  intro _
  -- Expose the underlying Prop after PostCond.noThrow unfolds.
  show (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ∣ x.toNat
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left x.toNat y.toNat

/-- Postcondition (D-y): the result divides the second input.

    Symmetric to `gcd_divides_x`: same characterization, with
    `Nat.gcd_dvd_right` in place of `Nat.gcd_dvd_left`. -/
theorem gcd_divides_y (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_u64.gcd x y
    ⦃ ⇓ g => ⌜ g.toNat ∣ y.toNat ⌝ ⦄ := by
  rw [gcd_characterization]
  refine Triple.pure _ ?_
  intro _
  show (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ∣ y.toNat
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
  rw [gcd_characterization]
  refine Triple.pure _ ?_
  rintro ⟨hx, hy⟩
  show d.toNat ∣ (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hx hy

end Gcd_u64Obligations
