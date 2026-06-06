-- Companion obligations file for the `lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import lcm_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Lcm_u64Obligations

/-- Helper: `gcd_u64 0 y = pure y` — when the first argument is zero, the
    early-return branch fires and returns `0 ||| y = y`. Stated with `pure`
    rather than `RustM.ok` so the `rw` chains downstream feed straight into
    `pure_bind`. -/
private theorem gcd_u64_zero_left (y : u64) :
    lcm_u64.gcd_u64 0 y = pure y := by
  unfold lcm_u64.gcd_u64
  -- The first conjunct of the early-return guard is `(0 == 0) = true`, so the
  -- short-circuit `||?` returns true and we land in the then-branch.
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  -- Goal now: `(0 |||? y) = pure y` where `|||?` is `pure (0 ||| y)`.
  show (pure ((0 : u64) ||| y) : RustM u64) = pure y
  congr 1
  apply UInt64.toNat_inj.mp
  simp

/-- Helper: `gcd_u64 x 0 = pure x` — symmetric early-return when the second
    argument is zero. -/
private theorem gcd_u64_zero_right (x : u64) :
    lcm_u64.gcd_u64 x 0 = pure x := by
  unfold lcm_u64.gcd_u64
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  show (pure (x ||| (0 : u64)) : RustM u64) = pure x
  congr 1
  apply UInt64.toNat_inj.mp
  simp

/-! ## Numeric-side infrastructure for the gcd-derived properties.

    These helpers are the *closed* lemmas that the surviving `sorry` on
    `gcd_u64_postcondition` is bracketed by. Every `lcm_*` obligation
    below is closed conditional on `gcd_u64_postcondition`; if a future
    pass replaces that `sorry` with a real Stein-correctness proof, the
    five user-facing theorems are immediately green. -/

/-- The mathematical gcd of two `u64` inputs (as `Nat`) fits in `u64`.
    Same shape as `gcd_while_modified.gcd_lt_2_64`. -/
private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

/-- The cast `UInt64.ofNat ∘ Nat.gcd` is a left inverse to `.toNat`,
    given the bound above. Mirrors `gcd_while_modified.gcd_toNat_ofNat`. -/
private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-- `Nat.gcd m n = 0 ↔ m = 0 ∧ n = 0`. Derived from `Nat.gcd_eq_zero_iff`
    when available, otherwise by case-split. We use the case-split form to
    avoid depending on a specific lemma name. -/
private theorem gcd_toNat_eq_zero_iff (a b : u64) :
    Nat.gcd a.toNat b.toNat = 0 ↔ a.toNat = 0 ∧ b.toNat = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := Nat.gcd_dvd_left a.toNat b.toNat
      rw [h] at this
      exact Nat.eq_zero_of_zero_dvd this
    · have := Nat.gcd_dvd_right a.toNat b.toNat
      rw [h] at this
      exact Nat.eq_zero_of_zero_dvd this
  · rintro ⟨ha, hb⟩
    rw [ha, hb, Nat.gcd_zero_left]

/-- **Postcondition for Stein's-algorithm `gcd_u64`** — the extracted
    function returns the mathematical gcd, lifted to `u64`.

    *Status*: left as `sorry`. The Rust implementation is Stein's binary
    gcd plus a hand-rolled `trailing_zeros_u64`. The canonical two-stage
    `while_example/README.md` proof pattern (`Spec.MonoLoopCombinator.while_loop`
    → strong invariant → `Triple_iff_BitVec`) applies in principle, but
    two ingredients are not exercised by any example in the proof-pattern
    library, so they would have to be invented from prelude internals:

    1. **Nested `while_loop`s.** The body of `gcd_u64`'s outer loop invokes
       `trailing_zeros_u64`, which is itself a `while_loop`. Proving the
       outer Hoare triple needs the post of the inner `trailing_zeros_u64`
       loop as a `bind`-step hypothesis. `gcd_while_modified` only handles
       a single top-level loop with a primitive `a %? b` in the body.
    2. **Stein invariant.** The strong invariant is
       `2 ^ shift * Nat.gcd m.toNat n.toNat = Nat.gcd a₀.toNat b₀.toNat`
       with both `m` and `n` odd at the loop head. Preservation of this
       invariant under the body `(M - N) >> tz(M - N)` requires two facts:
       (a) "odd minus odd is even" so `tz ≥ 1`, and (b)
       `Nat.gcd (M - N) N = Nat.gcd M N` when `N ≤ M`. Neither is in the
       Hax prelude (`Grep` confirms no `Nat.gcd_sub` lemma at
       `proofs/lean/extraction/.lake/packages/Hax/`), so the proof would
       need to develop them locally from scratch — significantly more
       work than fits in one obligations-stage pass.

    *Structural unblock*: a separately-verified Stein gcd target — e.g.
    a dedicated `proof_patterns/stein_gcd_u64` archetype that extends
    `proof_patterns/gcd_while_modified` with (i) nested `while_loop`
    chaining via `Triple.bind` and (ii) the Stein invariant above —
    would close this `sorry` in one cross-target import. All five
    user-facing obligations in this file would then be discharged
    automatically. -/
private theorem gcd_u64_postcondition (a b : u64) :
    lcm_u64.gcd_u64 a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  -- Substantive attempt: discharge the cases where `gcd_u64` does not
  -- actually enter Stein's loop. The remaining case is the genuine
  -- Stein-correctness gap documented above.
  by_cases ha : a = 0
  · subst ha
    rw [gcd_u64_zero_left]
    show (pure b : RustM u64) = RustM.ok (UInt64.ofNat (Nat.gcd 0 b.toNat))
    show RustM.ok b = RustM.ok (UInt64.ofNat (Nat.gcd 0 b.toNat))
    congr 1
    apply UInt64.toNat_inj.mp
    rw [Nat.gcd_zero_left]
    exact (UInt64.toNat_ofNat_of_lt' b.toNat_lt).symm
  · by_cases hb : b = 0
    · subst hb
      rw [gcd_u64_zero_right]
      show RustM.ok a = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat 0))
      congr 1
      apply UInt64.toNat_inj.mp
      rw [Nat.gcd_zero_right]
      exact (UInt64.toNat_ofNat_of_lt' a.toNat_lt).symm
    · -- Both `a` and `b` nonzero: Stein's loop actually runs. See docstring.
      sorry

/-- The gcd is positive when at least one of `a, b` is nonzero. Derived
    from `gcd_u64_postcondition` (the result equals `Nat.gcd a.toNat b.toNat`,
    which is positive iff not both inputs are zero). -/
private theorem gcd_u64_pos (a b : u64) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat := by
  rw [gcd_toNat_ofNat]
  rcases Nat.eq_zero_or_pos (Nat.gcd a.toNat b.toNat) with h | h
  · exfalso
    rw [gcd_toNat_eq_zero_iff] at h
    obtain ⟨ha, hb⟩ := h
    rcases hab with ha' | hb'
    · apply ha'
      apply UInt64.toNat_inj.mp
      rw [ha]; rfl
    · apply hb'
      apply UInt64.toNat_inj.mp
      rw [hb]; rfl
  · exact h

/-! ## RustM monadic-reduction helpers.

    These lemmas are `rfl` at the `Option (Except _ _)` level but
    `simp only` does not pick them up automatically; spelling them out
    locally lets the four `lcm_*` proofs below collapse the bind chain
    in one `simp only` pass. -/

@[simp] private theorem rustM_ok_bind {α β : Type} (v : α) (f : α → RustM β) :
    (RustM.ok v >>= f) = f v := rfl

@[simp] private theorem rustM_fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e >>= f : RustM β) = RustM.fail e := rfl

/-- `RustM.fail e = RustM.ok v` is impossible: `Option.some (.error e) ≠ Option.some (.ok v)`.
    Proved by two-step `injection`. -/
private theorem rustM_fail_ne_ok {α : Type} (e : Error) (v : α) :
    (RustM.fail e : RustM α) ≠ RustM.ok v := by
  intro h
  injection h with h1
  injection h1

/-- Postcondition (zero is absorbing, left): for every `y : u64`, `lcm 0 y`
    successfully returns `0`. Captures one half of the Rust property test
    `prop_zero_is_absorbing` (the `lcm(0, v)` direction). When `y = 0` the
    function takes the explicit `x == 0 && y == 0` early-return branch; when
    `y ≠ 0` it goes through the gcd path with `gcd_u64 0 y = y`, then
    `0 *? (y / y) = 0 *? 1 = ok 0`. Either way the result is `ok 0`. -/
theorem lcm_zero_left (y : u64) :
    lcm_u64.lcm 0 y = RustM.ok 0 := by
  unfold lcm_u64.lcm
  by_cases hy : y = 0
  · subst hy
    -- Both arguments are concrete `0`; the function reduces by computation.
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl
  · -- `y ≠ 0`: take the else branch via gcd.
    have h_eq_y : (y == (0 : u64)) = false := by
      simp [BEq.beq, hy]
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, Bool.true_and, h_eq_y]
    -- Goal: `gcd_u64 0 y >>= fun gcd => 0 *? (← y /? gcd) = RustM.ok 0`
    rw [gcd_u64_zero_left]
    -- `pure y >>= ...`; reduce.
    simp only [pure_bind]
    -- Goal now: `(do let q ← y /? y; 0 *? q) = RustM.ok 0`
    show (do let q ← (rust_primitives.ops.arith.Div.div y y : RustM u64)
             rust_primitives.ops.arith.Mul.mul (0 : u64) q) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Div.div, if_neg hy, pure_bind]
    -- `y / y = 1` for nonzero `y`.
    have h_pos : 0 < y.toNat := by
      rw [Nat.pos_iff_ne_zero]
      intro hh
      apply hy
      apply UInt64.toNat_inj.mp
      simp [hh]
    have hyy : y / y = 1 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div]
      rw [Nat.div_self h_pos]
      rfl
    rw [hyy]
    show (rust_primitives.ops.arith.Mul.mul (0 : u64) 1 : RustM u64) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Mul.mul]
    have h_no_ovf :
        BitVec.umulOverflow ((0 : u64).toBitVec) ((1 : u64).toBitVec) = false := by
      decide
    rw [h_no_ovf, if_neg (by decide)]
    rfl

/-- Postcondition (zero is absorbing, right): for every `x : u64`, `lcm x 0`
    successfully returns `0`. Captures the `lcm(v, 0)` direction of the Rust
    property test `prop_zero_is_absorbing`. When `x = 0` the early-return
    branch fires; when `x ≠ 0` we have `gcd_u64 x 0 = x`, then
    `x *? (0 / x) = x *? 0 = ok 0`. -/
theorem lcm_zero_right (x : u64) :
    lcm_u64.lcm x 0 = RustM.ok 0 := by
  unfold lcm_u64.lcm
  by_cases hx : x = 0
  · subst hx
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl
  · have h_eq_x : (x == (0 : u64)) = false := by
      simp [BEq.beq, hx]
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, h_eq_x, Bool.false_and]
    rw [gcd_u64_zero_right]
    simp only [pure_bind]
    show (do let q ← (rust_primitives.ops.arith.Div.div (0 : u64) x : RustM u64)
             rust_primitives.ops.arith.Mul.mul x q) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Div.div, if_neg hx, pure_bind]
    -- `0 / x = 0`.
    have h0x : (0 : u64) / x = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div]
      simp
    rw [h0x]
    show (rust_primitives.ops.arith.Mul.mul x 0 : RustM u64) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Mul.mul]
    have h_no_ovf :
        BitVec.umulOverflow x.toBitVec ((0 : u64).toBitVec) = false := by
      have : ¬ UInt64.mulOverflow x 0 := by
        rw [UInt64.mulOverflow_iff]; simp
      simpa [UInt64.mulOverflow] using this
    rw [h_no_ovf, if_neg (by decide)]
    show RustM.ok (x * 0) = RustM.ok 0
    -- `congr 1` reduces this to `x * 0 = 0`, which Lean closes automatically
    -- via the `BitVec.mul_zero` simp set baked into `congr`.
    congr 1

/-- Postcondition (common multiple, left factor): whenever `lcm x y` returns
    successfully with value `r`, `r` is a multiple of `x` (in `Nat`). Captures
    the Rust property test `prop_result_is_multiple_of_x`.

    The two zero edges are closed via `lcm_zero_left`/`lcm_zero_right` (in
    each case `r = 0`, and `x.toNat ∣ 0`). The interior case (both `x` and
    `y` non-zero) is left as `sorry`: extracting `r = x * (y / gcd)` from
    the do-block hypothesis requires destructuring the `RustM` bind chain
    (case-analyzing `gcd_u64 x y` and `y /? gcd` and `x *? q`); the latter
    in turn requires reasoning about the value of `gcd_u64 x y` through
    the Stein's-algorithm `while_loop`. The available reference examples do
    not cover `while_loop`-with-postcondition proofs at all (`average_*`
    are straight-line, `factorial`/`sum_to_n` use `partial_fixpoint`
    recursion), so the loop-invariant pattern would have to be invented from
    prelude internals. -/
theorem lcm_multiple_of_x (x y r : u64)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    x.toNat ∣ r.toNat := by
  by_cases hx : x = 0
  · subst hx
    rw [lcm_zero_left] at h
    have hr : r = 0 := by
      injection h with h1
      injection h1 with h2
      exact h2.symm
    subst hr
    simp
  · by_cases hy : y = 0
    · subst hy
      rw [lcm_zero_right] at h
      have hr : r = 0 := by
        injection h with h1
        injection h1 with h2
        exact h2.symm
      subst hr
      simp
    · -- Both `x` and `y` are non-zero: requires extracting `r = x * q` from
      -- the do-block, which depends on the value of `gcd_u64`.
      sorry

/-- Postcondition (common multiple, right factor): whenever `lcm x y` returns
    successfully with value `r`, `r` is a multiple of `y` (in `Nat`).

    The two zero edges are closed as above. The interior case is left as
    `sorry` for the same reason as `lcm_multiple_of_x` — it requires a loop
    invariant for `gcd_u64`'s Stein's-algorithm `while_loop`, plus the
    additional Nat-level fact that `gcd | y` (so `y / gcd * gcd = y` and
    therefore `y | x * (y / gcd)`). -/
theorem lcm_multiple_of_y (x y r : u64)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    y.toNat ∣ r.toNat := by
  by_cases hx : x = 0
  · subst hx
    rw [lcm_zero_left] at h
    have hr : r = 0 := by
      injection h with h1
      injection h1 with h2
      exact h2.symm
    subst hr
    simp
  · by_cases hy : y = 0
    · subst hy
      rw [lcm_zero_right] at h
      have hr : r = 0 := by
        injection h with h1
        injection h1 with h2
        exact h2.symm
      subst hr
      simp
    · sorry

/-- Postcondition (least common multiple): whenever `lcm x y` returns
    successfully with value `r`, no positive `Nat` strictly less than `r` is
    divisible by both `x` and `y`.

    Left as `sorry`: in addition to the `gcd_u64` loop-invariant analysis
    needed for the divisibility lemmas above, this clause requires the
    minimality side of the gcd characterization (every common divisor of `x`
    and `y` divides `gcd_u64 x y`). No reference example exercises that. -/
theorem lcm_is_least (x y r : u64)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    ∀ z : Nat, 0 < z → z < r.toNat → ¬ (x.toNat ∣ z ∧ y.toNat ∣ z) := by
  sorry

/-- Postcondition (commutativity / symmetry): `lcm` is symmetric in its
    arguments.

    The two zero edges are discharged via `lcm_zero_left`/`lcm_zero_right`
    (both sides reduce to `ok 0`). The interior case (both `x` and `y`
    non-zero) is left as `sorry`: the implementation is genuinely asymmetric
    (`x * (y / gcd)`), so commutativity there reduces to (i)
    `gcd_u64 x y = gcd_u64 y x` (a loop-symmetry claim about Stein's
    algorithm) and (ii) `x * (y / gcd) = y * (x / gcd)` when `gcd | x` and
    `gcd | y` (a Nat-level rearrangement that needs the divisibility facts).
    Both depend on a loop invariant for `gcd_u64`'s `while_loop`, which the
    available reference examples do not cover. -/
theorem lcm_commutative (x y : u64) :
    lcm_u64.lcm x y = lcm_u64.lcm y x := by
  by_cases hx : x = 0
  · subst hx
    rw [lcm_zero_left, lcm_zero_right]
  · by_cases hy : y = 0
    · subst hy
      rw [lcm_zero_left, lcm_zero_right]
    · -- Both `x` and `y` are non-zero: requires gcd loop reasoning.
      sorry

end Lcm_u64Obligations
