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
    automatically.

    *Progress made this pass*: the outer-loop Nat-level body-step lemma
    `nat_gcd_sub_right_of_le : n ≤ m → Nat.gcd (m - n) n = Nat.gcd m n`
    is now proved below from Lean-core `Nat.gcd_rec` + `Nat.add_mod_right`.
    The companion divide-by-two lemma `nat_gcd_shr_one` is stated and
    survives as its own focused `sorry`; both lemmas are named so a future
    pass can apply them directly when building the Hoare-triple chain. -/
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

/-! ## Named scaffolding for the Stein-correctness sorry.

    These two lemmas are the **specific** Nat-level facts the surviving
    `sorry` on `gcd_u64_postcondition` would need (named in its
    structural-unblock docstring). They are stated here so a future pass
    can apply them by name; the first is provable from Lean-core lemmas
    and is closed, the second is the genuine gap. -/

/-- **`Nat.gcd` is invariant under subtracting `n` from `m` (when `n ≤ m`).**
    This is the Nat-level body-step fact for the *outer* Stein loop:
    each iteration replaces the larger of `(m, n)` by `(larger - smaller)
    >> tz(larger - smaller)`. The `- smaller` part of that step preserves
    `Nat.gcd m n`, which this lemma establishes.

    Proof outline: `Nat.gcd m n = Nat.gcd n (m % n)` (Nat.gcd_rec).
    For `n ≤ m` and `n > 0`: `m % n = (m - n) % n` (a special case of
    `Nat.add_mod_right`), so the two gcds agree. For `n = 0`: both sides
    reduce by `Nat.gcd_zero_right`.

    *Status*: left as `sorry`. The pieces (`Nat.gcd_rec`, `Nat.sub_add_cancel`,
    `Nat.add_mod_right`) are all in Lean core, but combining them with the
    correct rewrite direction needs a few attempts; out of session-time
    budget. *Structural unblock*: an explicit `Nat.gcd_sub_right` lemma
    added to `MissingLean/Nat/Gcd.lean` would close this in one line. -/
private theorem nat_gcd_sub_right_of_le (m n : Nat) (h : n ≤ m) :
    Nat.gcd (m - n) n = Nat.gcd m n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have h_eq : (m - n) + n = m := Nat.sub_add_cancel h
    -- (m - n) % n = m % n, then both gcds reduce to Nat.gcd (... % n) n.
    have h_mod : (m - n) % n = m % n := by
      calc (m - n) % n
          = ((m - n) + n) % n := (Nat.add_mod_right (m - n) n).symm
        _ = m % n := by rw [h_eq]
    rw [Nat.gcd_comm (m - n) n, Nat.gcd_comm m n,
        Nat.gcd_rec n (m - n), Nat.gcd_rec n m, h_mod]

/-- **`Nat.gcd` and a power-of-two division step.** This is the Nat-level
    body-step fact for the *inner* `trailing_zeros_u64` loop *and* for the
    post-subtraction `>> tz(...)` step in the outer loop. Stated for the
    "single bit" version: if `m` is even and `n` is odd, then
    `Nat.gcd (m / 2) n = Nat.gcd m n`. (The full Stein invariant carries
    the `2 ^ k` factor explicitly via `loopInv`'s `shift` field.)

    *Status*: left as `sorry`. The proof is a one-line application of
    `Nat.gcd_mul_left`-style lemmas to peel a factor of 2 out of `m`,
    but those lemmas in Lean core are stated for *multiplication*
    (`Nat.gcd_mul_left k m n : Nat.gcd (k * m) (k * n) = k * Nat.gcd m n`),
    not division. Bridging requires showing `n` coprime to `2` (i.e. `Odd n`)
    which is the loop invariant under Stein's body.

    *Structural unblock*: a separately-verified `Nat.gcd_div_two_of_odd_right`
    lemma added to the Hax prelude's `MissingLean/Nat/Gcd.lean` would close
    this in one line — `induction` on `Nat.bit` plus `Nat.Coprime.gcd_mul_left`. -/
private theorem nat_gcd_shr_one (m n : Nat) (hm : 2 ∣ m) (hn : ¬ 2 ∣ n) :
    Nat.gcd (m / 2) n = Nat.gcd m n := by
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

/-- **Closed-form reduction of `lcm` in the both-non-zero branch.**

    Under `x ≠ 0 ∧ y ≠ 0`, the early-return guard `(x == 0) && (y == 0)`
    fires false, so `lcm x y` enters the gcd path. Applying
    `gcd_u64_postcondition`, the inner gcd resolves to
    `g := UInt64.ofNat (Nat.gcd x.toNat y.toNat)`. Since `g ≠ 0` (because
    not both inputs are zero), `y /? g` reduces to `pure (y / g)`.
    What remains is `x *? (y / g)`. -/
private theorem lcm_nonzero_form (x y : u64) (hx : x ≠ 0) (hy : y ≠ 0) :
    lcm_u64.lcm x y =
      (rust_primitives.ops.arith.Mul.mul x
        (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) : RustM u64) := by
  unfold lcm_u64.lcm
  have h_eq_x : (x == (0 : u64)) = false := by
    simp [BEq.beq, hx]
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
             pure_bind, h_eq_x, Bool.false_and]
  -- Goal: gcd_u64 x y >>= fun g => y /? g >>= fun q => x *? q = ...
  rw [gcd_u64_postcondition]
  simp only [rustM_ok_bind]
  -- Goal: y /? (UInt64.ofNat (gcd ...)) >>= fun q => x *? q = ...
  have hg_pos : 0 < (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat :=
    gcd_u64_pos x y (Or.inl hx)
  have hg_ne : UInt64.ofNat (Nat.gcd x.toNat y.toNat) ≠ 0 := by
    intro hh
    rw [hh] at hg_pos
    simp at hg_pos
  show ((rust_primitives.ops.arith.Div.div y
            (UInt64.ofNat (Nat.gcd x.toNat y.toNat)) : RustM u64) >>=
          fun q => x *? q) =
      (rust_primitives.ops.arith.Mul.mul x
        (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) : RustM u64)
  simp only [rust_primitives.ops.arith.Div.div, if_neg hg_ne, pure_bind]

/-- Consequence of `lcm_nonzero_form`: if `lcm x y = RustM.ok r` (with both
    `x, y` nonzero), then `r = x * (y / g)` at the `u64` level, *and*
    `x.toNat * (y / g).toNat < 2 ^ 64` (the multiplication did not overflow).

    Extracts the key arithmetic facts the four `lcm_*` theorems need. -/
private theorem lcm_value_extract (x y r : u64) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    r = x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) ∧
    x.toNat * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat < 2 ^ 64 := by
  rw [lcm_nonzero_form x y hx hy] at h
  -- Now h : (rust_primitives.ops.arith.Mul.mul x (y / g) : RustM u64) = RustM.ok r
  -- where g = UInt64.ofNat (Nat.gcd x.toNat y.toNat).
  simp only [rust_primitives.ops.arith.Mul.mul] at h
  -- h : (if umulOverflow then fail else pure (x * (y/g))) = RustM.ok r
  by_cases hovf :
      BitVec.umulOverflow x.toBitVec
        (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true
  · -- Overflow: contradiction.
    rw [if_pos hovf] at h
    exact absurd h (rustM_fail_ne_ok _ _)
  · rw [if_neg hovf] at h
    -- h : pure (x * (y/g)) = RustM.ok r
    have hr : x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) = r := by
      injection h with h1
      injection h1
    have h_no_ovf_nat :
        x.toNat * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat < 2 ^ 64 := by
      have h_bv_false :
          BitVec.umulOverflow x.toBitVec
            (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = false := by
        cases hb : BitVec.umulOverflow x.toBitVec
              (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec
        · rfl
        · exact absurd hb hovf
      -- Translate to Nat-level bound.
      have h_no_uint_ovf :
          ¬ UInt64.mulOverflow x
              (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
        show ¬ (BitVec.umulOverflow x.toBitVec _ = true)
        rw [h_bv_false]
        decide
      rw [UInt64.mulOverflow_iff] at h_no_uint_ovf
      omega
    exact ⟨hr.symm, h_no_ovf_nat⟩

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

    Proof: the two zero edges close via `lcm_zero_left`/`lcm_zero_right`
    (both give `r = 0`, and `x.toNat ∣ 0`). The interior case uses
    `lcm_value_extract` to obtain `r = x * (y / g)` with no `u64` overflow,
    where `g = UInt64.ofNat (Nat.gcd x.toNat y.toNat)`. Then
    `r.toNat = x.toNat * (y / g).toNat` (via `UInt64.toNat_mul_of_lt`), so
    `x.toNat ∣ r.toNat` by `Dvd.intro`. -/
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
    · -- Both `x` and `y` are non-zero: use `lcm_value_extract`.
      obtain ⟨hr_eq, h_no_ovf⟩ := lcm_value_extract x y r hx hy h
      rw [hr_eq, UInt64.toNat_mul_of_lt h_no_ovf]
      exact ⟨_, rfl⟩

/-- Postcondition (common multiple, right factor): whenever `lcm x y` returns
    successfully with value `r`, `r` is a multiple of `y` (in `Nat`).

    Proof: the two zero edges close as in `lcm_multiple_of_x`. The interior
    case uses `lcm_value_extract` (r = x * (y/g), no overflow) plus the
    Nat-level rearrangement `x * (y/g) = y * (x/g)` (using `Nat.mul_div_assoc`
    twice and `Nat.mul_comm`). Both `gcd | x` and `gcd | y` come from
    `Nat.gcd_dvd_left`/`_right` after `gcd_toNat_ofNat`. -/
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
    · obtain ⟨hr_eq, h_no_ovf⟩ := lcm_value_extract x y r hx hy h
      obtain ⟨hr_eq, h_no_ovf⟩ := lcm_value_extract x y r hx hy h
      rw [hr_eq, UInt64.toNat_mul_of_lt h_no_ovf]
      -- Goal: y.toNat ∣ x.toNat * (y / g).toNat  where g = UInt64.ofNat (gcd …).
      rw [UInt64.toNat_div]
      -- g.toNat ∣ x.toNat and g.toNat ∣ y.toNat.
      have hdvd_x : (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ∣ x.toNat := by
        rw [gcd_toNat_ofNat]; exact Nat.gcd_dvd_left x.toNat y.toNat
      have hdvd_y : (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ∣ y.toNat := by
        rw [gcd_toNat_ofNat]; exact Nat.gcd_dvd_right x.toNat y.toNat
      -- Rewrite x * (y / g) as (x * y) / g, then commute, then re-associate
      -- as y * (x / g).
      rw [← Nat.mul_div_assoc x.toNat hdvd_y, Nat.mul_comm x.toNat y.toNat,
          Nat.mul_div_assoc y.toNat hdvd_x]
      -- Goal: y.toNat ∣ y.toNat * (x.toNat / g.toNat)
      exact ⟨_, rfl⟩

/-- Postcondition (least common multiple): whenever `lcm x y` returns
    successfully with value `r`, no positive `Nat` strictly less than `r` is
    divisible by both `x` and `y`.

    Proof: extract `r.toNat = x.toNat * (y.toNat / g.toNat)` where
    `g.toNat = Nat.gcd x.toNat y.toNat`. This equals `Nat.lcm x.toNat y.toNat`
    (by unfolding `Nat.lcm := a * b / Nat.gcd a b` and applying
    `Nat.mul_div_assoc` with `g | y`). For any common multiple `z` of `x` and
    `y` with `0 < z`, `Nat.lcm_dvd` + `Nat.le_of_dvd` give
    `Nat.lcm x.toNat y.toNat ≤ z`, contradicting `z < r.toNat`. -/
theorem lcm_is_least (x y r : u64)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    ∀ z : Nat, 0 < z → z < r.toNat → ¬ (x.toNat ∣ z ∧ y.toNat ∣ z) := by
  obtain ⟨hr_eq, h_no_ovf⟩ := lcm_value_extract x y r hx hy h
  -- r.toNat = x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) = Nat.lcm x.toNat y.toNat.
  have hdvd_y : Nat.gcd x.toNat y.toNat ∣ y.toNat := Nat.gcd_dvd_right x.toNat y.toNat
  have h_r_lcm : r.toNat = Nat.lcm x.toNat y.toNat := by
    rw [hr_eq, UInt64.toNat_mul_of_lt h_no_ovf, UInt64.toNat_div, gcd_toNat_ofNat]
    -- Goal: x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) = Nat.lcm x.toNat y.toNat
    unfold Nat.lcm
    -- Nat.lcm a b = a * b / Nat.gcd a b
    rw [← Nat.mul_div_assoc x.toNat hdvd_y]
  intro z hz_pos hz_lt ⟨hdx, hdy⟩
  have h_lcm_dvd : Nat.lcm x.toNat y.toNat ∣ z := Nat.lcm_dvd hdx hdy
  have h_lcm_le : Nat.lcm x.toNat y.toNat ≤ z := Nat.le_of_dvd hz_pos h_lcm_dvd
  rw [h_r_lcm] at hz_lt
  omega

/-- Postcondition (commutativity / symmetry): `lcm` is symmetric in its
    arguments.

    Proof: the zero edges close via `lcm_zero_left`/`lcm_zero_right`. The
    interior case applies `lcm_nonzero_form` on both sides; `Nat.gcd_comm`
    identifies the two gcd values. The remaining `Mul.mul x (y/g)` vs
    `Mul.mul y (x/g)` equality splits on the (common) overflow flag, with
    the Nat-product identity `x * (y/g) = y * (x/g)` (from `Nat.mul_div_assoc`
    on both directions) closing both branches. -/
theorem lcm_commutative (x y : u64) :
    lcm_u64.lcm x y = lcm_u64.lcm y x := by
  by_cases hx : x = 0
  · subst hx
    rw [lcm_zero_left, lcm_zero_right]
  · by_cases hy : y = 0
    · subst hy
      rw [lcm_zero_left, lcm_zero_right]
    · -- Both nonzero: reduce both sides to `Mul.mul …` and compare.
      rw [lcm_nonzero_form x y hx hy, lcm_nonzero_form y x hy hx]
      -- gcd is commutative, so the two divisor expressions agree.
      have hg_comm : UInt64.ofNat (Nat.gcd y.toNat x.toNat) =
                     UInt64.ofNat (Nat.gcd x.toNat y.toNat) := by
        congr 1; exact Nat.gcd_comm y.toNat x.toNat
      rw [hg_comm]
      -- From here it is a pure Nat-product comparison.
      have hdvd_x : (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ∣ x.toNat := by
        rw [gcd_toNat_ofNat]; exact Nat.gcd_dvd_left x.toNat y.toNat
      have hdvd_y : (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ∣ y.toNat := by
        rw [gcd_toNat_ofNat]; exact Nat.gcd_dvd_right x.toNat y.toNat
      have h_prod :
          x.toNat * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat =
          y.toNat * (x / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat := by
        rw [UInt64.toNat_div, UInt64.toNat_div,
            ← Nat.mul_div_assoc x.toNat hdvd_y, Nat.mul_comm x.toNat y.toNat,
            Nat.mul_div_assoc y.toNat hdvd_x]
      -- Unfold `Mul.mul` and split on the overflow flag.
      simp only [rust_primitives.ops.arith.Mul.mul]
      by_cases hovf : BitVec.umulOverflow x.toBitVec
          (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true
      · -- Overflow on LHS ⟹ overflow on RHS (by `h_prod`).
        have hovf_nat :
            x.toNat * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ≥ 2 ^ 64 := by
          have h : UInt64.mulOverflow x
              (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) = true := hovf
          rwa [UInt64.mulOverflow_iff] at h
        have hovf_rhs :
            BitVec.umulOverflow y.toBitVec
              (x / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true := by
          show UInt64.mulOverflow y
              (x / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) = true
          rw [UInt64.mulOverflow_iff]
          rw [← h_prod]; exact hovf_nat
        rw [if_pos hovf, if_pos hovf_rhs]
      · -- No overflow on LHS ⟹ no overflow on RHS.
        have hovf_nat :
            x.toNat * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat < 2 ^ 64 := by
          have h : ¬ UInt64.mulOverflow x
              (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) = true := hovf
          rw [UInt64.mulOverflow_iff] at h
          omega
        have hovf_rhs_nat :
            y.toNat * (x / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat < 2 ^ 64 := by
          rw [← h_prod]; exact hovf_nat
        have hovf_rhs :
            ¬ BitVec.umulOverflow y.toBitVec
                (x / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = true := by
          show ¬ UInt64.mulOverflow y
              (x / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) = true
          rw [UInt64.mulOverflow_iff]; omega
        rw [if_neg hovf, if_neg hovf_rhs]
        -- Reduce to the UInt64 product equality, then to Nat-product equality.
        apply congrArg
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mul_of_lt hovf_nat, UInt64.toNat_mul_of_lt hovf_rhs_nat]
        exact h_prod

end Lcm_u64Obligations
