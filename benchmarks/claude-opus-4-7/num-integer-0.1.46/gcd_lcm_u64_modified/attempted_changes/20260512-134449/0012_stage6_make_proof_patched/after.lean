-- Companion obligations file for the `gcd_lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_lcm_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_lcm_u64Obligations

open rust_primitives.hax (Tuple2)

/-! ## Zero-input edge cases

Property test `zero_input_edge_cases` in the Rust source pins three values:
`gcd_lcm(0, 0) = (0, 0)`, `gcd_lcm(x, 0) = (x, 0)`, `gcd_lcm(0, y) = (y, 0)`.
None of the three can fail (no multiplication overflow possible since one
factor of the product is always zero), so each is stated equationally. -/

/-- `gcd_lcm(0, 0) = (0, 0)`. Hits the explicit `if x == 0 && y == 0` branch
    in the Rust source. -/
theorem gcd_lcm_zero_zero :
    gcd_lcm_u64.gcd_lcm 0 0 = RustM.ok ⟨0, 0⟩ := by
  decide

/-- `gcd_lcm(x, 0) = (x, 0)` for every `x`. Generic branch: `gcd(x, 0) = x`
    and `l = x * (0 / x) = 0`. -/
theorem gcd_lcm_y_zero (x : u64) :
    gcd_lcm_u64.gcd_lcm x 0 = RustM.ok ⟨x, 0⟩ := by
  by_cases hx : x = 0
  · subst hx; decide
  · unfold gcd_lcm_u64.gcd_lcm gcd_lcm_u64.gcd
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               rust_primitives.hax.logical_op.or,
               rust_primitives.ops.arith.Mul.mul,
               rust_primitives.ops.arith.Div.div,
               pure_bind,
               beq_self_eq_true, Bool.and_true, Bool.or_true]
    have hxbeq : (x == (0 : u64)) = false := by
      apply (Bool.eq_false_iff).mpr; intro h
      apply hx; exact (beq_iff_eq.mp h)
    simp only [hxbeq, Bool.false_eq_true, ↓reduceIte]
    have hxor : (x ||| (0 : u64)) = x := by
      apply UInt64.toBitVec_inj.mp; simp
    have hzdivx : ((0 : u64) / x) = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div]; simp
    have h_no_mul_ovf : BitVec.umulOverflow x.toBitVec ((0 : u64).toBitVec) = false := by
      simp [BitVec.umulOverflow]
    simp only [hxor, hzdivx, if_neg hx, pure_bind, h_no_mul_ovf,
               Bool.false_eq_true, ↓reduceIte, UInt64.mul_zero]
    rfl

/-- `gcd_lcm(0, y) = (y, 0)` for every `y`. Generic branch: `gcd(0, y) = y`
    and `l = 0 * (y / y) = 0`. -/
theorem gcd_lcm_x_zero (y : u64) :
    gcd_lcm_u64.gcd_lcm 0 y = RustM.ok ⟨y, 0⟩ := by
  by_cases hy : y = 0
  · subst hy; decide
  · unfold gcd_lcm_u64.gcd_lcm gcd_lcm_u64.gcd
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               rust_primitives.hax.logical_op.or,
               rust_primitives.ops.arith.Mul.mul,
               rust_primitives.ops.arith.Div.div,
               pure_bind,
               beq_self_eq_true, Bool.true_and,
               Bool.true_or]
    have hybeq : (y == (0 : u64)) = false := by
      apply (Bool.eq_false_iff).mpr; intro h
      apply hy; exact (beq_iff_eq.mp h)
    simp only [hybeq, Bool.false_eq_true, ↓reduceIte]
    have hyor : ((0 : u64) ||| y) = y := by
      apply UInt64.toBitVec_inj.mp; simp
    have hydivy : (y / y) = 1 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div]
      have hy_pos : 0 < y.toNat := by
        rcases Nat.eq_zero_or_pos y.toNat with h | h
        · exfalso; apply hy; apply UInt64.toNat_inj.mp; rw [h]; rfl
        · exact h
      rw [Nat.div_self hy_pos]
      rfl
    have h_no_mul_ovf : BitVec.umulOverflow ((0 : u64).toBitVec) (1 : BitVec 64) = false := by
      simp [BitVec.umulOverflow]
    simp only [hyor, hydivy, if_neg hy, pure_bind]
    rw [show ((1 : u64).toBitVec = (1 : BitVec 64)) from rfl]
    simp only [h_no_mul_ovf, Bool.false_eq_true, ↓reduceIte, UInt64.zero_mul]
    rfl

/-! ## Postconditions on a successful result

`gcd_lcm` can fail with `integerOverflow` when `lcm(x, y) > u64::MAX`, so the
divisibility / greatness / product-identity clauses are stated as hypotheses
on a successful outcome `RustM.ok ⟨g, l⟩` rather than as existentials (which
would force totality). Each clause matches one property test in the source. -/

/-- Property test `gcd_is_a_common_divisor`, divisor side `x`. When the
    function succeeds with result `⟨g, l⟩`, the gcd component divides `x`.

    Sorry justification: This requires proving the inner Stein's-algorithm
    `gcd` function is correct, i.e. `gcd x y = RustM.ok (UInt64.ofNat
    (Nat.gcd x.toNat y.toNat))`. Stein's correctness proof has three layers:

    1. **`trailing_zeros_u64` postcondition**: the inner while-loop counts the
       low zero bits of `y`, requiring a loop invariant
       `y₀.toNat = (y.toNat) * 2^count ∧ y ≠ 0` and termination by
       `y.toNat`. Two-stage `while_loop`-spec + `Triple_iff_BitVec` (canonical
       pattern from `while_example/README.md`).
    2. **Outer `gcd` loop invariant**: after the initial `m >>= tz(m)` /
       `n >>= tz(n)` strips, both are odd, and the loop preserves
       `Nat.gcd m.toNat n.toNat = Nat.gcd x_odd.toNat y_odd.toNat`. The
       step uses `Nat.gcd_rec`/`Nat.gcd_sub_self` plus the bit-trick that
       `(m - n) >>= tz(m - n)` peels a power of two whose gcd contribution
       is trivial. Termination: `max m.toNat n.toNat` strictly decreases.
    3. **Final assembly**: `gcd x y = (m_final) * 2^shift` where `shift =
       tz(x | y)` and `m_final = gcd(x_odd, y_odd)`; combine with
       `Nat.gcd_mul_left` to recover `Nat.gcd x.toNat y.toNat`.

    The divisibility clause `g.toNat ∣ x.toNat` then follows from
    `Nat.gcd_dvd_left`. The proof would parallel `gcd_while_postcondition` in
    `proof_patterns/gcd_while_modified` but with three nested loops instead
    of one, and is beyond the scope of a single proof stage. -/
theorem gcd_lcm_gcd_divides_x (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat ∣ x.toNat := by
  sorry

/-- Property test `gcd_is_a_common_divisor`, divisor side `y`. When the
    function succeeds with result `⟨g, l⟩`, the gcd component divides `y`.

    Sorry justification: Same Stein's-algorithm correctness chain as
    `gcd_lcm_gcd_divides_x`; once `gcd x y = ok (UInt64.ofNat (Nat.gcd ...))`
    is established, this clause closes by `Nat.gcd_dvd_right`. -/
theorem gcd_lcm_gcd_divides_y (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat ∣ y.toNat := by
  sorry

/-- Property test `gcd_is_the_greatest_common_divisor`. Independent from the
    divisibility clauses: a buggy impl returning `1` would divide both inputs
    but fail this. When the function succeeds with result `⟨g, l⟩`, every
    common divisor of `x` and `y` divides `g`.

    Sorry justification: Same Stein's-algorithm correctness chain; once
    `gcd x y = ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat))` is established,
    this clause closes by `Nat.dvd_gcd hdx hdy`. -/
theorem gcd_lcm_gcd_greatest (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩)
    (d : Nat) (hdx : d ∣ x.toNat) (hdy : d ∣ y.toNat) :
    d ∣ g.toNat := by
  sorry

/-- Property test `gcd_times_lcm_equals_x_times_y`. When the function succeeds
    with result `⟨g, l⟩`, the algebraic identity `g * l = x * y` holds at the
    `Nat` level. Together with `gcd_lcm_gcd_greatest`, this uniquely fixes the
    lcm component.

    Sorry justification: Beyond the Stein's-algorithm chain (which gives
    `g = Nat.gcd x.toNat y.toNat`), this needs the multiplication branch of
    `gcd_lcm`'s success post: `l.toNat = x.toNat * (y.toNat / g.toNat)`,
    which requires (i) a no-overflow side-condition `x.toNat * (y.toNat /
    g.toNat) < 2^64` derived from the *absence* of `integerOverflow` in `h`,
    and (ii) the arithmetic identity `g * (x * (y / g)) = x * y` when `g ∣
    y`. The selector flagged "no example covers multiplication-overflow as
    a conditional failure" — adapting `average_floor_u64_modified`'s
    `BitVec.uaddOverflow` machinery to `BitVec.umulOverflow` is the missing
    piece. -/
theorem gcd_lcm_product (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat * l.toNat = x.toNat * y.toNat := by
  sorry

/-! ## Failure condition

Documented in the Rust source ("panics on overflow when lcm(x, y) > u64::MAX
(debug mode)"). The property tests intentionally use small input ranges that
stay inside `u64`, so no test directly triggers this; the clause comes from
the source documentation. -/

/-- Failure mode: when `lcm(x, y)` does not fit in `u64`, the function fails
    with `integerOverflow`. (`Nat.lcm 0 _ = Nat.lcm _ 0 = 0 < 2^64`, so the
    hypothesis automatically rules out the zero edge cases handled above.)

    Sorry justification: This needs both directions of the Stein's-algorithm
    chain plus the overflow analysis:

    1. **`gcd x y = ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat))`** — same
       three-layer correctness proof outlined in `gcd_lcm_gcd_divides_x`.
    2. **`y /? g` succeeds with `y.toNat / g.toNat`** — requires `g ≠ 0`,
       which follows from `¬(x = 0 ∧ y = 0)` (the else-branch guard) and
       the lemma `Nat.gcd_ne_zero_of_or` (gcd of two not-both-zero is
       non-zero). The selector flagged "no example covers division-by-zero
       discharged from a prior branch guard."
    3. **`x *? (y /? g)` fails with `integerOverflow`** — needs
       `BitVec.umulOverflow x.toBitVec (y / g).toBitVec = true`, equivalent
       to `x.toNat * (y.toNat / g.toNat) ≥ 2^64`. The hypothesis `2^64 ≤
       Nat.lcm x y` plus the identity `Nat.lcm x y = x * y / Nat.gcd x y =
       x * (y / Nat.gcd x y)` (when `gcd ∣ y`) gives exactly this. The
       selector flagged "no example covers multiplication-overflow as a
       conditional failure" — this is the dual of `average_floor`'s
       no-overflow argument, swapping `BitVec.uaddOverflow` for
       `BitVec.umulOverflow` and the direction of the inequality.

    All three layers are technically standard once the Stein's-correctness
    foundation is in place, but the cumulative proof effort (≈ 3 nested
    while-loop spec proofs + supporting arithmetic) exceeds what a single
    proof stage can produce. -/
theorem gcd_lcm_overflow_failure (x y : u64)
    (h : 2 ^ 64 ≤ Nat.lcm x.toNat y.toNat) :
    gcd_lcm_u64.gcd_lcm x y = RustM.fail .integerOverflow := by
  sorry

end Gcd_lcm_u64Obligations
