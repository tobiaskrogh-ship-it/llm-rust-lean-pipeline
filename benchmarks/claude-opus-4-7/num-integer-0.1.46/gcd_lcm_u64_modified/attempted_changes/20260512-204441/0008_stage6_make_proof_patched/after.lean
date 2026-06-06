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

/-! ## Zero-input edge cases -/

/-- `gcd_lcm(0, 0) = (0, 0)`. -/
theorem gcd_lcm_zero_zero :
    gcd_lcm_u64.gcd_lcm 0 0 = RustM.ok ⟨0, 0⟩ := by
  decide

/-- `gcd_lcm(x, 0) = (x, 0)` for every `x`. -/
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

/-- `gcd_lcm(0, y) = (y, 0)` for every `y`. -/
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

/-! ## Helper lemmas (pure arithmetic, no monadic plumbing) -/

/-- `Nat.gcd a.toNat b.toNat < 2^64` for `a b : u64`. -/
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

/-- `RustM.fail e = RustM.ok v` is impossible. Definitionally these are
    `some (.error e)` and `some (.ok v)`, distinct constructors of `Except`. -/
private theorem rustM_fail_ne_ok {α : Type} (e : Error) (v : α)
    (h : RustM.fail e = RustM.ok v) : False := by
  have h' : (some (Except.error e) : Option (Except Error α))
          = some (Except.ok v) := h
  injection h' with h''
  injection h''

/-- `RustM.ok v >>= f = f v` definitionally. Phrased as a simp-amenable lemma
    so that the `bind` on `RustM.ok` reduces in the monadic-reduction proofs. -/
@[simp]
private theorem rustM_ok_bind {α β : Type} (v : α) (f : α → RustM β) :
    (RustM.ok v >>= f : RustM β) = f v := rfl

/-- `RustM.fail e >>= f = RustM.fail e`. Failure propagates through bind. -/
@[simp]
private theorem rustM_fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e >>= f : RustM β) = RustM.fail e := rfl

/-! ## Structural unblocks -/

/-- **Structural unblock #1**: Stein's binary GCD correctness for
    `gcd_lcm_u64.gcd`.

    **Stuck sub-goal** (after `unfold gcd_lcm_u64.gcd`): proving Hoare triples
    for three nested while-loop constructs — `trailing_zeros_u64` (a count-
    trailing-zeros loop, invoked 4× by `gcd`) and the outer Stein's loop
    (subtract-and-shift). Each requires its own invariant + termination
    measure proof in the style of `while_example` / `gcd_while_modified`.

    **Structural unblock**: a separately-proved `proof_patterns/stein_gcd_u64`
    pattern targeting exactly this lemma would close every remaining sorry
    in this file. The proof would chain three loop-spec proofs:
    1. `trailing_zeros_u64 x = RustM.ok (UInt64.ofNat ⟨count of low zero bits⟩)`
       via invariant `y.toNat * 2 ^ count = x.toNat ∧ y ≠ 0 → bit0 y = false`.
    2. Outer loop preserving `Nat.gcd m.toNat n.toNat`, after initial
       `m >>>= tz(m); n >>>= tz(n)` (so both odd), via `Nat.gcd_rec` and the
       bit-trick that `(m - n) >>>= tz(m - n)` peels a power of two whose
       gcd factor is removed by the final `<<<? shift`.
    3. Final assembly via `Nat.gcd_mul_left`. -/
private theorem gcd_correct (x y : u64) :
    gcd_lcm_u64.gcd x y = RustM.ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
  sorry

/-- **Structural unblock #2**: closed-form reduction of `gcd_lcm_u64.gcd_lcm`
    in the non-degenerate case.

    **Stuck sub-goal** (after `unfold gcd_lcm_u64.gcd_lcm; simp only [...]`):
    the `simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
    pure_bind]` step reports "made no progress" — `simp only` for the `def`s
    `rust_primitives.cmp.eq` / `rust_primitives.hax.logical_op.and` does not
    unfold them here, likely because the post-`unfold` term places them under
    metavariable-laden `bind` calls whose monadic structure isn't normalized
    enough for the rewrite rules to fire. The working proofs for the
    zero-edge cases (`gcd_lcm_y_zero`, `gcd_lcm_x_zero`) use the same simp
    set but also unfold `gcd_lcm_u64.gcd`, which substitutes concrete values
    into the inner if and lets the cascading rewrites fire. In the general
    non-zero case we must NOT unfold `gcd` (we need `gcd_correct` to
    substitute it), so the simp chain stalls.

    **Structural unblock**: a generic `Hax.RustM.reduce_do_block` tactic
    or simp normal-form for monadic Rust code (turning a `do … if ←
    (cond1 &&? cond2) then … else …` into a top-level `if (cond1 && cond2)
    then … else …`) would close this in one step. Alternatively, manually
    `delta`-reducing `rust_primitives.cmp.eq`, `rust_primitives.hax.logical_op.and`,
    `rust_primitives.ops.arith.Div.div`, `rust_primitives.ops.arith.Mul.mul`
    using `Lean.Meta.delta` API and chaining `bind_pure_comp` /
    `pure_bind` correctly would work; this requires more tactic-engineering
    than a single proof stage delivers. -/
private theorem gcd_lcm_nonzero_form (x y : u64) (hxy : ¬(x = 0 ∧ y = 0)) :
    gcd_lcm_u64.gcd_lcm x y =
      (if BitVec.umulOverflow x.toBitVec
            (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec
       then RustM.fail Error.integerOverflow
       else RustM.ok ⟨UInt64.ofNat (Nat.gcd x.toNat y.toNat),
                       x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat))⟩) := by
  unfold gcd_lcm_u64.gcd_lcm
  -- Reduce the boolean condition: `(x == 0) && (y == 0) = false` from hxy.
  have h_cond_false : ((x == (0 : u64)) && (y == (0 : u64))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨hx, hy⟩ := h
    exact hxy ⟨beq_iff_eq.mp hx, beq_iff_eq.mp hy⟩
  have hg_ne_zero : UInt64.ofNat (Nat.gcd x.toNat y.toNat) ≠ 0 := by
    intro hg
    have hg_nat : Nat.gcd x.toNat y.toNat = 0 := by
      have := congrArg UInt64.toNat hg
      rw [gcd_toNat_ofNat] at this
      exact this
    exact hxy ((gcd_toNat_eq_zero_iff x y).mp hg_nat)
  -- Unified simp pass: unfold all operators, apply gcd_correct, run the
  -- `RustM.ok` / `RustM.fail` bind reductions, collapse the conditional on
  -- `g = 0`, and push the remaining bind through the umulOverflow if.
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
             rust_primitives.ops.arith.Div.div,
             rust_primitives.ops.arith.Mul.mul,
             pure_bind, rustM_ok_bind, rustM_fail_bind, h_cond_false,
             Bool.false_eq_true, ↓reduceIte,
             gcd_correct, if_neg hg_ne_zero]
  -- Goal: `do let l ← if … then fail else pure (x * (y / g)); pure ⟨g, l⟩
  --       = if … then fail else RustM.ok ⟨g, x * (y / g)⟩`. Case-split.
  by_cases hovf :
      BitVec.umulOverflow x.toBitVec
        (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true
  · rw [if_pos hovf, if_pos hovf]
    rfl
  · -- ¬(umulOverflow = true) means umulOverflow = false.
    have hovf_false :
        BitVec.umulOverflow x.toBitVec
          (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = false := by
      cases h_eq : BitVec.umulOverflow x.toBitVec
                    (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec
      · rfl
      · exact absurd h_eq hovf
    rw [if_neg (by rw [hovf_false]; decide),
        if_neg (by rw [hovf_false]; decide)]
    rfl

/-! ### Key extraction lemmas: identify `g` and `l` from a successful result -/

/-- The gcd component of a successful `gcd_lcm` result equals `Nat.gcd` at the
    Nat level. Closed using `gcd_lcm_nonzero_form` (structural-unblock #2) +
    `gcd_correct` (structural-unblock #1). -/
private theorem gcd_lcm_g_eq (x y g l : u64)
    (h : gcd_lcm_u64.gcd_lcm x y = RustM.ok ⟨g, l⟩) :
    g.toNat = Nat.gcd x.toNat y.toNat := by
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨hx, hy⟩ := hxy
    subst hx; subst hy
    rw [gcd_lcm_zero_zero] at h
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
      exact (rustM_fail_ne_ok _ _ h).elim
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
      exact (rustM_fail_ne_ok _ _ h).elim
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
      have h_not_ovf :
          ¬ UInt64.mulOverflow x (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
        show ¬ (BitVec.umulOverflow x.toBitVec
                  (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true)
        rw [hovf']
        decide
      have h_no_mul_ovf : x.toNat *
            (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat < 2 ^ 64 :=
        Nat.lt_of_not_le (fun h_ge => h_not_ovf (UInt64.mulOverflow_iff.mpr h_ge))
      rw [UInt64.toNat_mul_of_lt h_no_mul_ovf]
      rw [UInt64.toNat_div, gcd_toNat_ofNat]

/-! ## Proven obligations

All five user-facing obligations close in 1–5 lines using the helpers above.
The remaining `sorry`s are exclusively in the two structural-unblock helpers
`gcd_correct` and `gcd_lcm_nonzero_form`. -/

/-- Property test `gcd_is_a_common_divisor`, divisor side `x`. -/
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

/-- Property test `gcd_is_the_greatest_common_divisor`. -/
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
    with `integerOverflow`. -/
theorem gcd_lcm_overflow_failure (x y : u64)
    (h : 2 ^ 64 ≤ Nat.lcm x.toNat y.toNat) :
    gcd_lcm_u64.gcd_lcm x y = RustM.fail .integerOverflow := by
  -- Derive `¬(x = 0 ∧ y = 0)` from the lcm hypothesis.
  have hxy : ¬(x = 0 ∧ y = 0) := by
    intro ⟨hx, hy⟩
    subst hx; subst hy
    have h0 : Nat.lcm (0 : u64).toNat (0 : u64).toNat = 0 := by
      show Nat.lcm 0 0 = 0
      simp [Nat.lcm]
    rw [h0] at h
    omega
  rw [gcd_lcm_nonzero_form x y hxy]
  -- Show the multiplication overflows.
  have h_y_div_toNat :
      (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat =
        y.toNat / Nat.gcd x.toNat y.toNat := by
    rw [UInt64.toNat_div, gcd_toNat_ofNat]
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
    exact h_uint64_ovf
  simp only [h_ovf, ↓reduceIte]

end Gcd_lcm_u64Obligations
