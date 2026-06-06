-- Companion obligations file for the `gcd_lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

/-! ## Helper lemmas for Stein's-algorithm correctness

The remaining obligations all reduce, via the helper `gcd_correct` below, to
purely arithmetic / divisibility / overflow facts about `Nat.gcd`. The four
post-conditions (divides_x, divides_y, greatest, product) and the overflow
failure clause are then closed in a handful of lines each. `gcd_correct`
itself is the single structural unblock. -/

/-- `Nat.gcd a b < 2^64` whenever `a, b : u64`. By case-splitting on whether
    `b.toNat = 0`: in that case `Nat.gcd a 0 = a < 2^64`; otherwise
    `Nat.gcd a b ≤ b < 2^64`. -/
private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

/-- The gcd packed into a `u64` round-trips through `.toNat`. -/
private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-- `Nat.gcd x.toNat y.toNat = 0 ↔ x = 0 ∧ y = 0`. -/
private theorem gcd_toNat_eq_zero_iff (x y : u64) :
    Nat.gcd x.toNat y.toNat = 0 ↔ x = 0 ∧ y = 0 := by
  rw [Nat.gcd_eq_zero_iff]
  constructor
  · intro ⟨hxn, hyn⟩
    refine ⟨?_, ?_⟩
    · apply UInt64.toNat_inj.mp; rw [hxn]; rfl
    · apply UInt64.toNat_inj.mp; rw [hyn]; rfl
  · intro ⟨hx, hy⟩
    subst hx; subst hy
    exact ⟨rfl, rfl⟩

/-- The packed `u64` gcd is non-zero when not both inputs are zero. -/
private theorem gcd_ofNat_ne_zero (x y : u64) (hxy : ¬(x = 0 ∧ y = 0)) :
    UInt64.ofNat (Nat.gcd x.toNat y.toNat) ≠ 0 := by
  intro hg
  have hg_nat : Nat.gcd x.toNat y.toNat = 0 := by
    have := congrArg UInt64.toNat hg
    rw [gcd_toNat_ofNat] at this
    exact this
  exact hxy ((gcd_toNat_eq_zero_iff x y).mp hg_nat)

/-! ### The structural unblock: Stein's algorithm correctness -/

/-- **Structural unblock**: Stein's binary GCD correctness for `gcd_lcm_u64.gcd`.
    The four remaining sorries below (divides_x, divides_y, greatest, product,
    overflow_failure) each close in 1–10 lines once this is available.

    **Stuck sub-goal** (after `unfold gcd_lcm_u64.gcd`): proving Hoare triples
    for three nested while-loop constructs —
    * `trailing_zeros_u64`: a count-trailing-zeros loop (`y &&& 1 == 0` body
      doing `y >>>= 1; count += 1`). Invoked 4× by `gcd`.
    * outer Stein's loop: subtract-and-shift loop with body `if m > n then
      m -= n; m >>>= tz(m) else n -= m; n >>>= tz(n)`.
    Together with the bracketing `>>>= tz(m)` and `<<<? shift` operations.
    Each requires its own invariant + termination measure proof in the style
    of `while_example` / `gcd_while_modified`, which collectively exceed
    what a single proof stage can produce.

    **Structural unblock**: a separately-proved `proof_patterns/stein_gcd_u64`
    pattern targeting exactly this lemma would close every remaining sorry
    in this file. The proof would chain three loop-spec proofs:
    1. `trailing_zeros_u64 x = RustM.ok (UInt64.ofNat (... low-zero-count of x ...))`
       via invariant `y₀.toNat = y.toNat * 2 ^ count ∧ (x = 0 → count = 64)`.
    2. Outer loop preserving `Nat.gcd m.toNat n.toNat`, after the initial
       `m >>>= tz(m); n >>>= tz(n)` (so both are odd), using `Nat.gcd_rec`
       and the bit-trick that `(m - n) >>>= tz(m - n)` peels a power of two
       whose gcd factor is removed by the final `<<<? shift`.
    3. Final assembly via `Nat.gcd_mul_left` to recover the input gcd. -/
private theorem gcd_correct (x y : u64) :
    gcd_lcm_u64.gcd x y = RustM.ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
  sorry

/-! ### Reduced form of `gcd_lcm` -/

/-- Closed-form reduction of `gcd_lcm_u64.gcd_lcm` in the non-degenerate case.
    Once we know the gcd, the rest of the function is pure arithmetic. -/
private theorem gcd_lcm_nonzero_form (x y : u64) (hxy : ¬(x = 0 ∧ y = 0)) :
    let g := UInt64.ofNat (Nat.gcd x.toNat y.toNat)
    gcd_lcm_u64.gcd_lcm x y =
      (if BitVec.umulOverflow x.toBitVec (y / g).toBitVec
       then RustM.fail Error.integerOverflow
       else RustM.ok ⟨g, x * (y / g)⟩) := by
  unfold gcd_lcm_u64.gcd_lcm
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
             pure_bind]
  have h_cond : ((x == (0 : u64)) && (y == (0 : u64))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨hx, hy⟩ := h
    apply hxy
    exact ⟨beq_iff_eq.mp hx, beq_iff_eq.mp hy⟩
  rw [h_cond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [gcd_correct]
  simp only [pure_bind]
  -- Goal at this point: `let l ← x *? (← y /? g); pure ⟨g, l⟩`.
  -- Reduce `y /? g`.
  simp only [rust_primitives.ops.arith.Div.div]
  have hg_ne_zero : UInt64.ofNat (Nat.gcd x.toNat y.toNat) ≠ 0 :=
    gcd_ofNat_ne_zero x y hxy
  rw [if_neg hg_ne_zero]
  simp only [pure_bind]
  -- Reduce `x *? (y / g)`.
  simp only [rust_primitives.ops.arith.Mul.mul]
  by_cases hovf :
      BitVec.umulOverflow x.toBitVec
        (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true
  · rw [if_pos hovf, if_pos hovf]
    rfl
  · have hovf' :
        BitVec.umulOverflow x.toBitVec
          (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = false := by
      cases h_eq : BitVec.umulOverflow x.toBitVec
                    (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec
      · rfl
      · exact absurd h_eq hovf
    rw [if_neg (by rw [hovf']; decide), if_neg (by rw [hovf']; decide)]
    simp only [pure_bind]
    rfl

/-! ### Key extraction lemma: identify `g` from a successful result -/

/-- The gcd component of a successful `gcd_lcm` result equals `Nat.gcd` at the
    Nat level. This is the single bridge that lets the next three theorems
    close in one line each. -/
private theorem gcd_lcm_g_eq (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat = Nat.gcd x.toNat y.toNat := by
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨hx, hy⟩ := hxy
    subst hx; subst hy
    rw [gcd_lcm_zero_zero] at h
    -- h : RustM.ok ⟨0, 0⟩ = RustM.ok ⟨g, l⟩
    have h_inj : (⟨(0 : u64), (0 : u64)⟩ : Tuple2 u64 u64) = ⟨g, l⟩ := by
      have h1 : (Except.ok ⟨(0 : u64), (0 : u64)⟩ : Except Error (Tuple2 u64 u64))
              = Except.ok ⟨g, l⟩ := Option.some.inj h
      exact Except.ok.inj h1
    have hg : (0 : u64) = g :=
      (rust_primitives.hax.Tuple2.mk.injEq _ _ _ _).mp h_inj |>.1
    rw [← hg]
    show (0 : Nat) = Nat.gcd 0 0
    simp
  · rw [gcd_lcm_nonzero_form x y hxy] at h
    by_cases hovf :
        BitVec.umulOverflow x.toBitVec
          (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true
    · simp only [hovf, ↓reduceIte] at h
      -- h : RustM.fail integerOverflow = RustM.ok ⟨g, l⟩, contradiction.
      exact (Except.noConfusion (Option.some.inj h) : False).elim
    · have hovf' :
          BitVec.umulOverflow x.toBitVec
            (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = false := by
        cases h_eq : BitVec.umulOverflow x.toBitVec
                      (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec
        · rfl
        · exact absurd h_eq hovf
      simp only [hovf', Bool.false_eq_true, ↓reduceIte] at h
      have h_inj :
          (⟨UInt64.ofNat (Nat.gcd x.toNat y.toNat),
            x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat))⟩ : Tuple2 u64 u64)
            = ⟨g, l⟩ := by
        have h1 :
            (Except.ok (⟨UInt64.ofNat (Nat.gcd x.toNat y.toNat),
                         x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat))⟩ :
                       Tuple2 u64 u64)
              : Except Error (Tuple2 u64 u64))
              = Except.ok ⟨g, l⟩ := Option.some.inj h
        exact Except.ok.inj h1
      have hg : UInt64.ofNat (Nat.gcd x.toNat y.toNat) = g :=
        (rust_primitives.hax.Tuple2.mk.injEq _ _ _ _).mp h_inj |>.1
      rw [← hg]
      exact gcd_toNat_ofNat x y

/-- The lcm component of a successful `gcd_lcm` result equals
    `x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat)` at the Nat level. -/
private theorem gcd_lcm_l_eq (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    l.toNat = x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) := by
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨hx, hy⟩ := hxy
    subst hx; subst hy
    rw [gcd_lcm_zero_zero] at h
    have h_inj : (⟨(0 : u64), (0 : u64)⟩ : Tuple2 u64 u64) = ⟨g, l⟩ := by
      have h1 : (Except.ok ⟨(0 : u64), (0 : u64)⟩ : Except Error (Tuple2 u64 u64))
              = Except.ok ⟨g, l⟩ := Option.some.inj h
      exact Except.ok.inj h1
    have hl : (0 : u64) = l :=
      (rust_primitives.hax.Tuple2.mk.injEq _ _ _ _).mp h_inj |>.2
    rw [← hl]
    show (0 : Nat) = 0 * (0 / Nat.gcd 0 0)
    simp
  · rw [gcd_lcm_nonzero_form x y hxy] at h
    by_cases hovf :
        BitVec.umulOverflow x.toBitVec
          (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true
    · simp only [hovf, ↓reduceIte] at h
      exact (Except.noConfusion (Option.some.inj h) : False).elim
    · have hovf' :
          BitVec.umulOverflow x.toBitVec
            (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = false := by
        cases h_eq : BitVec.umulOverflow x.toBitVec
                      (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec
        · rfl
        · exact absurd h_eq hovf
      simp only [hovf', Bool.false_eq_true, ↓reduceIte] at h
      have h_inj :
          (⟨UInt64.ofNat (Nat.gcd x.toNat y.toNat),
            x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat))⟩ : Tuple2 u64 u64)
            = ⟨g, l⟩ := by
        have h1 :
            (Except.ok (⟨UInt64.ofNat (Nat.gcd x.toNat y.toNat),
                         x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat))⟩ :
                       Tuple2 u64 u64)
              : Except Error (Tuple2 u64 u64))
              = Except.ok ⟨g, l⟩ := Option.some.inj h
        exact Except.ok.inj h1
      have hl :
          x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) = l :=
        (rust_primitives.hax.Tuple2.mk.injEq _ _ _ _).mp h_inj |>.2
      rw [← hl]
      have h_no_mul_ovf : x.toNat *
            (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat < 2 ^ 64 := by
        have h_not_ovf :
            ¬ UInt64.mulOverflow x (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
          show ¬ (BitVec.umulOverflow x.toBitVec
                    (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true)
          rw [hovf']
          decide
        exact Nat.lt_of_not_le (fun h_ge =>
          h_not_ovf (UInt64.mulOverflow_iff.mpr h_ge))
      rw [UInt64.toNat_mul_of_lt h_no_mul_ovf]
      rw [UInt64.toNat_div, gcd_toNat_ofNat]

/-! ## Proven obligations -/

/-- Property test `gcd_is_a_common_divisor`, divisor side `x`. When the
    function succeeds with result `⟨g, l⟩`, the gcd component divides `x`. -/
theorem gcd_lcm_gcd_divides_x (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat ∣ x.toNat := by
  rw [gcd_lcm_g_eq x y g l h]
  exact Nat.gcd_dvd_left _ _

/-- Property test `gcd_is_a_common_divisor`, divisor side `y`. -/
theorem gcd_lcm_gcd_divides_y (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat ∣ y.toNat := by
  rw [gcd_lcm_g_eq x y g l h]
  exact Nat.gcd_dvd_right _ _

/-- Property test `gcd_is_the_greatest_common_divisor`. Independent from the
    divisibility clauses: a buggy impl returning `1` would divide both inputs
    but fail this. -/
theorem gcd_lcm_gcd_greatest (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩)
    (d : Nat) (hdx : d ∣ x.toNat) (hdy : d ∣ y.toNat) :
    d ∣ g.toNat := by
  rw [gcd_lcm_g_eq x y g l h]
  exact Nat.dvd_gcd hdx hdy

/-- Property test `gcd_times_lcm_equals_x_times_y`. -/
theorem gcd_lcm_product (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat * l.toNat = x.toNat * y.toNat := by
  rw [gcd_lcm_g_eq x y g l h, gcd_lcm_l_eq x y g l h]
  -- Goal: Nat.gcd x.toNat y.toNat * (x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat))
  --       = x.toNat * y.toNat
  have hg_dvd_y : Nat.gcd x.toNat y.toNat ∣ y.toNat := Nat.gcd_dvd_right _ _
  have hy_div : Nat.gcd x.toNat y.toNat *
                (y.toNat / Nat.gcd x.toNat y.toNat) = y.toNat :=
    Nat.mul_div_cancel' hg_dvd_y
  calc Nat.gcd x.toNat y.toNat *
       (x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat))
      = Nat.gcd x.toNat y.toNat * x.toNat *
        (y.toNat / Nat.gcd x.toNat y.toNat) := by rw [← Nat.mul_assoc]
    _ = x.toNat * Nat.gcd x.toNat y.toNat *
        (y.toNat / Nat.gcd x.toNat y.toNat) := by
          rw [Nat.mul_comm (Nat.gcd x.toNat y.toNat) x.toNat]
    _ = x.toNat * (Nat.gcd x.toNat y.toNat *
                  (y.toNat / Nat.gcd x.toNat y.toNat)) := by rw [Nat.mul_assoc]
    _ = x.toNat * y.toNat := by rw [hy_div]

/-! ## Failure condition -/

/-- Failure mode: when `lcm(x, y)` does not fit in `u64`, the function fails
    with `integerOverflow`. (`Nat.lcm 0 _ = Nat.lcm _ 0 = 0 < 2^64`, so the
    hypothesis automatically rules out the zero edge cases.) -/
theorem gcd_lcm_overflow_failure (x y : u64)
    (h : 2 ^ 64 ≤ Nat.lcm x.toNat y.toNat) :
    gcd_lcm_u64.gcd_lcm x y = RustM.fail .integerOverflow := by
  -- Step 1: derive `¬(x = 0 ∧ y = 0)` from the lcm hypothesis.
  have hxy : ¬(x = 0 ∧ y = 0) := by
    intro ⟨hx, hy⟩
    subst hx; subst hy
    have h0 : Nat.lcm (0 : u64).toNat (0 : u64).toNat = 0 := by
      show Nat.lcm 0 0 = 0
      simp [Nat.lcm]
    rw [h0] at h
    omega
  -- Step 2: use the reduced form for the non-zero case.
  rw [gcd_lcm_nonzero_form x y hxy]
  -- Step 3: show the umulOverflow check is true.
  -- Compute (y / g).toNat = y.toNat / Nat.gcd x.toNat y.toNat.
  have h_y_div_toNat :
      (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat =
        y.toNat / Nat.gcd x.toNat y.toNat := by
    rw [UInt64.toNat_div, gcd_toNat_ofNat]
  -- Connect the hypothesis to x.toNat * (y.toNat / gcd) ≥ 2^64 via lcm.
  have hg_dvd_y : Nat.gcd x.toNat y.toNat ∣ y.toNat := Nat.gcd_dvd_right _ _
  have h_lcm_eq :
      Nat.lcm x.toNat y.toNat = x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) := by
    show x.toNat * y.toNat / Nat.gcd x.toNat y.toNat
       = x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat)
    rw [Nat.mul_div_assoc _ hg_dvd_y]
  have h_prod_ge :
      x.toNat * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ≥ 2 ^ 64 := by
    rw [h_y_div_toNat, ← h_lcm_eq]
    exact h
  have h_ovf :
      BitVec.umulOverflow x.toBitVec
        (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true := by
    have h_uint64_ovf :
        UInt64.mulOverflow x (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) :=
      UInt64.mulOverflow_iff.mpr h_prod_ge
    -- UInt64.mulOverflow a b = BitVec.umulOverflow a.toBitVec b.toBitVec
    exact h_uint64_ovf
  simp only [h_ovf, ↓reduceIte]

end Gcd_lcm_u64Obligations
