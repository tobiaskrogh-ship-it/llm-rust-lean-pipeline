-- Companion obligations file for the `gcd_stein_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_stein_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_stein_u64Obligations

/-! ## Nat-bridge helpers

The `Nat.gcd` of two `u64`s is bounded by the inputs and so fits in a `u64`.
Mirrors the helper from `gcd_while_modified` / `gcd_recursive_modified`. -/

/-- `RustM.ok`-headed bind reduction (`RustM.ok` is `pure` for `RustM`). -/
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-! ## Closed-form postcondition

The function reduces to `Nat.gcd` on the `toNat` projections of its inputs.
This is the master statement: every other contract clause below is a
projection of it.

### Status of this `sorry` and structural unblock

**Stuck sub-goal.** Closing this requires three interlocking pieces of
Nat-level Stein-algorithm correctness, none of which the prelude provides
and none of which a single `omega`/`grind`/`simp` discharges:

(1) **Inner trailing-zeros spec** for `gcd_stein_u64.trailing_zeros_u64`. The
    full machinery from `proof_patterns/trailing_zeros_u64_modified`
    (`tzInv`, `tzBody`, `tzLoop`, body-step, two-stage triple, master
    existential) must be re-instantiated against the local copy inside the
    `gcd_stein_u64` namespace. ~300 lines of mechanical port.

(2) **Recursive loop closed form** for `gcd_stein_loop`. This is a
    `partial_fixpoint` recursion with two arms (`m > n` / `m < n`),
    each calling `trailing_zeros_u64` on the difference and recursing.
    Strong induction on the Nat measure `m.toNat + n.toNat` (each iteration
    strictly decreases since `(m - n) >>> tz(m - n) ≤ m - n < m`), with the
    side invariant that `m`, `n` remain odd through the recursion, would
    give `gcd_stein_loop m n = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat n.toNat))`
    when both inputs are odd. The body-arm discharge needs the
    trailing-zeros spec from (1).

(3) **Outer wrapper algebraic identity** combining (1) and (2):
    `Nat.gcd a.toNat b.toNat = 2 ^ shift * Nat.gcd m₀ n₀` where
    `shift = tz(a | b) = min(tz(a), tz(b))`, `m₀ = a >>> tz(a)`, and
    `n₀ = b >>> tz(b)`. The Hax / Lean core prelude exposes
    `Nat.gcd_zero_left`, `Nat.gcd_zero_right`, `Nat.gcd_comm`, and
    `Nat.gcd_rec`, but not `Nat.gcd_mul_left`-style shift identities. The
    needed Nat-level facts are:
      • `gcd(2 * m, 2 * n) = 2 * gcd m n`
      • `gcd(2 * m, n) = gcd(m, n)` when `n % 2 = 1`
      • `gcd(m, n) = gcd(m - n, n)` for `m > n` (Stein's subtract step)
    All three are provable from `Nat.gcd_rec` + parity case-split, but
    each is ~30 lines of `omega`-aware case analysis.

**Structural unblock.** Three external pieces would close this in a
follow-up pass — listed in dependency order:

  (a) A separately-verified module `Hax.MissingLean.Init.Data.Nat.GcdStein`
      proving the three Nat-level identities above (`gcd_mul_two_left`,
      `gcd_two_left_odd_right`, `gcd_sub_right` for `m ≥ n`). These are
      the missing prelude lemmas; once they exist, the outer wrapper
      identity in (3) becomes ~10 lines.
  (b) Cross-target import of the trailing-zeros master existential from
      `proof_patterns/trailing_zeros_u64_modified.Trailing_zeros_u64Obligations.trailing_zeros_u64_nonzero_spec`,
      instantiated against `gcd_stein_u64.trailing_zeros_u64`. The Lean
      definitions are character-identical inside their respective
      namespaces, so the whole proof carries verbatim — but the import
      path is target-local and would need a small pipeline mechanism to
      copy-and-rename a closed proof across crates.
  (c) Strong induction on `m.toNat + n.toNat` for the `gcd_stein_loop`
      closed form, conditioned on (a) and (b). Given the helpers from
      (a) and (b), this is a direct port of the `gcd_recursive_modified`
      pattern (`greatest_common_divisor_postcondition`) — ~50 lines,
      mechanical.

The helper-lemma statements named in (a) are stated below as
`private theorem`s with their own focused `sorry`s, so the next pass
inherits the exact target shape. -/

/-! ## Nat-level Stein identities (helpers for the master postcondition).

These are the three algebraic identities the master `gcd_stein_postcondition`
needs at the `Nat.gcd` level. Stated here so the next pass sees the exact
shape; each has its own focused `sorry` (no prelude lemma covers them and
they require a Nat-level induction). The structural unblock for the master
names these by name. -/

/-- `gcd(2m, 2n) = 2 * gcd(m, n)`. Stein's halving identity. -/
private theorem nat_gcd_double_both (m n : Nat) :
    Nat.gcd (2 * m) (2 * n) = 2 * Nat.gcd m n := by
  exact Nat.gcd_mul_left 2 m n

/-- Key auxiliary lemma: if `d` is odd and `d ∣ 2 * m`, then `d ∣ m`.
    This is the parity-divisibility argument that lets us strip even factors
    from one side of a gcd when the other side is odd. -/
private theorem odd_dvd_two_mul {d m : Nat} (hd : d % 2 = 1) (h : d ∣ 2 * m) :
    d ∣ m := by
  obtain ⟨k, hk⟩ := h
  -- 2 * m = d * k
  -- Step 1: k is even.
  have hk_even : k % 2 = 0 := by
    have h_zero : (2 * m) % 2 = 0 := Nat.mul_mod_right 2 m
    rw [hk, Nat.mul_mod, hd, Nat.one_mul, Nat.mod_mod] at h_zero
    exact h_zero
  -- Step 2: extract k = 2 * k'.
  obtain ⟨k', hk'⟩ : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk_even
  -- Step 3: substitute and cancel.
  refine ⟨k', ?_⟩
  -- Goal: m = d * k'. We have hk: 2 * m = d * k and hk': k = 2 * k'.
  have h1 : 2 * m = d * (2 * k') := by rw [hk, hk']
  have h2 : 2 * m = 2 * (d * k') := by
    rw [h1, ← Nat.mul_assoc, Nat.mul_comm d 2, Nat.mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2

/-- `gcd(2m, n) = gcd(m, n)` when `n` is odd. Stein's even-stripping
    identity for the case where only one input is even.

    Proof: divisibility antisymmetry, using `odd_dvd_two_mul` for the
    nontrivial direction. -/
private theorem nat_gcd_two_left_odd_right (m n : Nat) (hn : n % 2 = 1) :
    Nat.gcd (2 * m) n = Nat.gcd m n := by
  refine Nat.dvd_antisymm ?_ ?_
  · -- Backward: gcd(2m, n) ∣ gcd(m, n)
    apply Nat.dvd_gcd
    · -- gcd(2m, n) ∣ m
      have h_dvd_2m : Nat.gcd (2 * m) n ∣ 2 * m := Nat.gcd_dvd_left _ _
      have h_dvd_n : Nat.gcd (2 * m) n ∣ n := Nat.gcd_dvd_right _ _
      -- g is odd (since it divides odd n).
      have h_g_odd : Nat.gcd (2 * m) n % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (Nat.gcd (2 * m) n) with hg | hg
        · exfalso
          have h_2_dvd_g : 2 ∣ Nat.gcd (2 * m) n := Nat.dvd_of_mod_eq_zero hg
          have h_2_dvd_n : 2 ∣ n := Nat.dvd_trans h_2_dvd_g h_dvd_n
          have h_n_mod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_2_dvd_n
          omega
        · exact hg
      exact odd_dvd_two_mul h_g_odd h_dvd_2m
    · exact Nat.gcd_dvd_right _ _
  · -- Forward: gcd(m, n) ∣ gcd(2m, n)
    apply Nat.dvd_gcd
    · -- gcd(m, n) ∣ m ⟹ ∣ 2 * m.
      exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) ⟨2, by rw [Nat.mul_comm]⟩
    · exact Nat.gcd_dvd_right _ _

/-- `gcd(m, n) = gcd(m - n, n)` for `m ≥ n`. Stein's subtract step
    identity. -/
private theorem nat_gcd_sub_right (m n : Nat) (h : n ≤ m) :
    Nat.gcd m n = Nat.gcd (m - n) n := by
  -- m = (m - n) + n, so Nat.gcd m n = Nat.gcd ((m - n) + n) n =
  -- Nat.gcd (m - n) n by Nat.gcd_add_self_left.
  have h_eq : Nat.gcd m n = Nat.gcd ((m - n) + n) n := by
    rw [Nat.sub_add_cancel h]
  rw [h_eq, Nat.gcd_add_self_left]

/-! ## Trailing-zeros infrastructure (port from `trailing_zeros_u64_modified`).

The local `gcd_stein_u64.trailing_zeros_u64` has the same body as the
reference target's `trailing_zeros_u64`, so the proof carries verbatim —
only the namespace prefix changes. -/

open rust_primitives.hax (Tuple2)

private def tzInv (x₀ : u64) (s : Tuple2 u32 u64) : Prop :=
  x₀.toNat = s._1.toNat * 2 ^ s._0.toNat ∧ 0 < s._1.toNat ∧ s._0.toNat < 64

private def tzTerm (s : Tuple2 u32 u64) : Nat := s._1.toNat

private abbrev tzCond : Tuple2 u32 u64 → Bool :=
  fun b => UInt64.toNat (b._1 &&& 1) == UInt64.toNat 0

private abbrev tzBody : Tuple2 u32 u64 → RustM (Tuple2 u32 u64) :=
  fun x =>
    match x with
    | ⟨count, y⟩ =>
      (do
        let y : u64 ← (y >>>? (1 : i32))
        let count : u32 ← (count +? (1 : u32))
        pure (rust_primitives.hax.Tuple2.mk count y) :
        RustM (rust_primitives.hax.Tuple2 u32 u64))

private abbrev tzLoop (x : u64) : RustM (Tuple2 u32 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk tzCond
    (rust_primitives.hax.Tuple2.mk (0 : u32) x) tzBody

private theorem tz_body_step_nat (x₀ : u64) (c : u32) (y : u64)
    (hinv : tzInv x₀ ⟨c, y⟩) (hcond : tzCond ⟨c, y⟩ = true) :
    c.toNat + 1 < 2 ^ 32 ∧
    (y >>> (1 : UInt64)).toNat < y.toNat ∧
    tzInv x₀ ⟨c + 1, y >>> (1 : UInt64)⟩ := by
  unfold tzInv at hinv
  simp only at hinv
  obtain ⟨hx, hy_pos, hc_lt⟩ := hinv
  have h_y_and : (y &&& 1).toNat = 0 := by
    have hb : (UInt64.toNat (y &&& 1) == UInt64.toNat 0) = true := hcond
    have : UInt64.toNat (y &&& 1) = UInt64.toNat 0 := beq_iff_eq.mp hb
    simpa using this
  have h_y_even : y.toNat % 2 = 0 := by
    have : y.toNat &&& 1 = 0 := by
      have := h_y_and
      rw [UInt64.toNat_and] at this
      rw [UInt64.toNat_one] at this
      exact this
    rw [← Nat.and_one_is_mod]; exact this
  have h_y_ge_2 : y.toNat ≥ 2 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
    show y.toNat >>> (1 % 64) < y.toNat
    rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
        show (2 ^ 1 : Nat) = 2 from rfl]
    exact Nat.div_lt_self (by omega) (by decide)
  · have h_cplus : (c + (1 : u32)).toNat = c.toNat + 1 := by
      apply UInt32.toNat_add_of_lt
      have h1 : (1 : UInt32).toNat = 1 := rfl
      rw [h1]; omega
    have h_yshr : (y >>> (1 : UInt64)).toNat = y.toNat / 2 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
      show y.toNat >>> (1 % 64) = _
      rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
          show (2 ^ 1 : Nat) = 2 from rfl]
    have h_new_y_pos : 0 < y.toNat / 2 := Nat.div_pos h_y_ge_2 (by decide)
    have h_y_div_mul : y.toNat / 2 * 2 = y.toNat := by
      have := Nat.div_add_mod y.toNat 2
      omega
    have h_x_eq : x₀.toNat = y.toNat / 2 * 2 ^ (c.toNat + 1) := by
      have key : y.toNat * 2 ^ c.toNat = y.toNat / 2 * 2 ^ (c.toNat + 1) := by
        rw [Nat.pow_succ,
            show 2 ^ c.toNat * 2 = 2 * 2 ^ c.toNat from Nat.mul_comm _ _,
            ← Nat.mul_assoc, h_y_div_mul]
      rw [← key]; exact hx
    have h_cplus_lt_64 : c.toNat + 1 < 64 := by
      have h_x_lt : x₀.toNat < 2 ^ 64 := UInt64.toNat_lt x₀
      have h_pow_le : 2 ^ (c.toNat + 1) ≤ x₀.toNat := by
        rw [h_x_eq]; exact Nat.le_mul_of_pos_left _ h_new_y_pos
      have h_pow_lt : 2 ^ (c.toNat + 1) < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h_pow_le h_x_lt
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_pow_lt
    refine ⟨?_, ?_, ?_⟩
    · show x₀.toNat = (y >>> (1 : UInt64)).toNat * 2 ^ (c + (1 : u32)).toNat
      rw [h_yshr, h_cplus]; exact h_x_eq
    · show 0 < (y >>> (1 : UInt64)).toNat
      rw [h_yshr]; exact h_new_y_pos
    · show (c + (1 : u32)).toNat < 64
      rw [h_cplus]; exact h_cplus_lt_64

private theorem tz_loop_triple (x₀ : u64) :
    ⦃⌜ tzInv x₀ ⟨(0 : u32), x₀⟩ ⌝⦄
      tzLoop x₀
    ⦃⇓ r => ⌜ tzInv x₀ r ∧ ¬ tzCond r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (rust_primitives.hax.Tuple2.mk (0 : u32) x₀) Lean.Loop.mk
    tzCond tzBody (tzInv x₀) tzTerm
  intro s hcond hinv
  cases s with
  | mk c y =>
    have hstep := tz_body_step_nat x₀ c y hinv hcond
    obtain ⟨h_no_add_ovf, h_term_dec, h_inv'⟩ := hstep
    have h_shr : (y >>>? (1 : i32) : RustM u64) = pure (y >>> (1 : UInt64)) := by
      show (rust_primitives.ops.bit.Shr.shr y (1 : i32) : RustM u64) =
           pure (y >>> (1 : UInt64))
      show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
              pure (y >>> ((1 : Int32).toNatClampNeg.toUInt64))
            else .fail .integerOverflow) = pure (y >>> (1 : UInt64))
      rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
      simp only [if_true]
      have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
      rw [this]
    have h_add : (c +? (1 : u32) : RustM u32) = pure (c + 1) := by
      show (rust_primitives.ops.arith.Add.add c (1 : u32) : RustM u32) =
           pure (c + 1)
      show (if BitVec.uaddOverflow c.toBitVec (1 : u32).toBitVec then
              (.fail .integerOverflow : RustM u32)
            else pure (c + 1)) = pure (c + 1)
      have h_no_ovf : BitVec.uaddOverflow c.toBitVec ((1 : u32).toBitVec) = false := by
        cases h_eq : BitVec.uaddOverflow c.toBitVec ((1 : u32).toBitVec) with
        | false => rfl
        | true =>
          exfalso
          have : UInt32.addOverflow c (1 : u32) = true := h_eq
          rw [UInt32.addOverflow_iff] at this
          have h1 : (1 : UInt32).toNat = 1 := rfl
          rw [h1] at this; omega
      rw [h_no_ovf]; rfl
    dsimp only [tzBody]
    rw [h_shr]
    simp only [pure_bind]
    rw [h_add]
    simp only [pure_bind]
    refine ⟨?_, h_inv'⟩
    show tzTerm ⟨c + 1, y >>> 1⟩ < tzTerm ⟨c, y⟩
    show (y >>> (1 : UInt64)).toNat < y.toNat
    exact h_term_dec

private theorem tz_function_nonzero_triple (x : u64) (hx : x ≠ 0) :
    ⦃⌜ True ⌝⦄
      gcd_stein_u64.trailing_zeros_u64 x
    ⦃⇓ r => ⌜ r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧
              (x.toNat >>> r.toNat) &&& 1 = 1 ⌝⦄ := by
  have h_loop := tz_loop_triple x
  have h_loop' :
      ⦃⌜ tzInv x ⟨(0 : u32), x⟩ ⌝⦄
        tzLoop x
      ⦃⇓ r => ⌜ r._0.toNat < 64 ∧ 2 ^ r._0.toNat ∣ x.toNat ∧
                (x.toNat >>> r._0.toNat) &&& 1 = 1 ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    unfold tzInv at hinv
    obtain ⟨hx_eq, hy_pos, hc_lt⟩ := hinv
    have h_y_odd : r._1.toNat % 2 = 1 := by
      have h_ne_zero : ¬ ((UInt64.toNat (r._1 &&& 1)) == UInt64.toNat 0) = true := hncond
      rw [beq_iff_eq] at h_ne_zero
      have h_neq : UInt64.toNat (r._1 &&& 1) ≠ UInt64.toNat 0 := h_ne_zero
      rw [UInt64.toNat_and, UInt64.toNat_one] at h_neq
      have h0 : (UInt64.toNat 0 : Nat) = 0 := rfl
      rw [h0] at h_neq
      rw [← Nat.and_one_is_mod]
      have h_bound : r._1.toNat &&& 1 ≤ 1 := Nat.and_le_right
      omega
    refine ⟨hc_lt, ?_, ?_⟩
    · rw [hx_eq]
      exact ⟨r._1.toNat, by rw [Nat.mul_comm]⟩
    · rw [hx_eq]
      have h_div : (r._1.toNat * 2 ^ r._0.toNat) >>> r._0.toNat = r._1.toNat := by
        rw [Nat.shiftRight_eq_div_pow]
        have hpos : 0 < 2 ^ r._0.toNat := Nat.two_pow_pos r._0.toNat
        exact Nat.mul_div_cancel _ hpos
      rw [h_div, Nat.and_one_is_mod]
      exact h_y_odd
  have h_loop'' :
      ⦃⌜ True ⌝⦄
        tzLoop x
      ⦃⇓ r => ⌜ r._0.toNat < 64 ∧ 2 ^ r._0.toNat ∣ x.toNat ∧
                (x.toNat >>> r._0.toNat) &&& 1 = 1 ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ h_loop'
    intro _
    show tzInv x ⟨(0 : u32), x⟩
    refine ⟨?_, ?_, ?_⟩
    · show x.toNat = x.toNat * 2 ^ ((0 : u32).toNat)
      rw [show ((0 : u32).toNat) = 0 from rfl, Nat.pow_zero, Nat.mul_one]
    · show 0 < x.toNat
      rcases Nat.eq_zero_or_pos x.toNat with h | h
      · exfalso; apply hx; apply UInt64.toNat_inj.mp; rw [h]; rfl
      · exact h
    · show (0 : u32).toNat < 64; decide
  unfold gcd_stein_u64.trailing_zeros_u64
  unfold rust_primitives.hax.while_loop
  show ⦃⌜True⌝⦄
        ((x ==? (0 : u64)) >>= fun b =>
          if b = true then pure (64 : u32)
          else (tzLoop x >>= fun __discr =>
                  match __discr with | ⟨c, _⟩ => pure c))
        ⦃⇓ r => ⌜r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧ (x.toNat >>> r.toNat) &&& 1 = 1⌝⦄
  show ⦃⌜True⌝⦄
        ((pure (x == (0 : u64)) : RustM Bool) >>= fun b =>
          if b = true then pure (64 : u32)
          else (tzLoop x >>= fun __discr =>
                  match __discr with | ⟨c, _⟩ => pure c))
        ⦃⇓ r => ⌜r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧ (x.toNat >>> r.toNat) &&& 1 = 1⌝⦄
  simp only [pure_bind]
  have h_eq_false : (x == (0 : u64)) = false := by
    rw [beq_eq_false_iff_ne]; exact hx
  rw [h_eq_false]
  simp only [if_false, Bool.false_eq_true]
  apply Triple.bind _ _ h_loop''
  intro s
  cases s with
  | mk c y =>
    refine Triple.pure c ?_
    intro h
    exact h

/-- Trailing-zeros master existential on the local `gcd_stein_u64.trailing_zeros_u64`.

    Mechanical port from `proof_patterns/trailing_zeros_u64_modified.trailing_zeros_u64_nonzero_spec`. -/
private theorem tz_nonzero_spec (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, gcd_stein_u64.trailing_zeros_u64 x = RustM.ok r ∧
                r.toNat < 64 ∧
                2 ^ r.toNat ∣ x.toNat ∧
                (x.toNat >>> r.toNat) &&& 1 = 1 := by
  have h := tz_function_nonzero_triple x hx
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hpost⟩ := h
  cases hf : gcd_stein_u64.trailing_zeros_u64 x with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v =>
      rw [hf] at hpost
      simp only [RustM.toBVRustM] at hpost
      exact ⟨v, rfl, hpost.1, hpost.2.1, hpost.2.2⟩
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

/-- Trailing-zeros at zero: definitional. -/
private theorem tz_zero :
    gcd_stein_u64.trailing_zeros_u64 (0 : u64) = RustM.ok (64 : u32) := by
  unfold gcd_stein_u64.trailing_zeros_u64
  rfl

/-- Power-of-two extension of `nat_gcd_two_left_odd_right`: stripping any
    power of 2 from the left side preserves gcd when the right side is odd. -/
private theorem nat_gcd_mul_pow_two_left_odd_right (a n : Nat) (hn : n % 2 = 1) :
    ∀ k, Nat.gcd (a * 2 ^ k) n = Nat.gcd a n
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]
  | k + 1 => by
    have ih := nat_gcd_mul_pow_two_left_odd_right a n hn k
    -- a * 2^(k+1) = 2 * (a * 2^k)
    have h_eq : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [Nat.pow_succ]
      -- a * (2^k * 2) = 2 * (a * 2^k)
      rw [← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ k) 2]
    rw [h_eq, nat_gcd_two_left_odd_right _ _ hn, ih]

/-- `gcd_stein_loop` closed form for **odd, nonzero** inputs.

    When both `m` and `n` are odd, the binary-GCD subtract-and-strip loop
    converges to `Nat.gcd m.toNat n.toNat`. Proof by strong induction on
    the measure `m.toNat + n.toNat`.

    The base case (`m = n`) is closed below. The step cases (`m > n` and
    `m < n`) require a substantial chain of monadic-bind reductions
    (`m -? n`, `d >>>? r`, recursive call) plus the Nat-level identity
    bridge via `nat_gcd_sub_right` and `nat_gcd_mul_pow_two_left_odd_right`.

    Stuck sub-goal: the step cases need to introduce `d = m - n` (or
    `n - m`) and `m' = d >>> trailing_zeros(d)` as locally-named values
    to apply the IH. The `set` tactic (Mathlib) is not available in this
    project; the workaround is to inline `m - n` everywhere or use
    `generalize`. The full inlined proof is ~150 lines per case.

    Structural unblock: adding Mathlib's `set` tactic to the project, or
    extracting the step-case body into a separate `private theorem`
    parameterised by `d` and `m'`. With either, the step cases collapse to
    ~30 lines each (the algebraic bridging at the end is straightforward
    given the Nat-level identities proven above). -/
private theorem gcd_stein_loop_spec (m n : u64)
    (hm_odd : m.toNat % 2 = 1) (hn_odd : n.toNat % 2 = 1) :
    gcd_stein_u64.gcd_stein_loop m n
      = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat n.toNat)) := by
  -- Bridge: odd ⟹ positive.
  have hm_pos : 0 < m.toNat := by omega
  have hn_pos : 0 < n.toNat := by omega
  induction hk : (m.toNat + n.toNat) using Nat.strongRecOn generalizing m n with
  | _ k ih =>
    unfold gcd_stein_u64.gcd_stein_loop
    have h_mn_eqq : (m ==? n : RustM Bool) = pure (m == n) := rfl
    rw [h_mn_eqq]
    simp only [pure_bind]
    by_cases hmn : m = n
    · -- Base case: m = n. Returns pure m. gcd(m, m) = m.
      subst hmn
      have h_dec : (m == m) = true := beq_self_eq_true m
      rw [h_dec]
      simp only [if_true]
      show RustM.ok m = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat m.toNat))
      congr 1
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (by rw [Nat.gcd_self]; exact m.toNat_lt),
          Nat.gcd_self]
    · -- Step cases: m ≠ n. Either m > n or m < n; both subtract the smaller
      -- from the larger, strip trailing zeros, and recurse on a smaller pair.
      have h_mn_false : (m == n) = false := by
        rw [beq_eq_false_iff_ne]; exact hmn
      rw [h_mn_false]
      simp only [Bool.false_eq_true, if_false]
      have h_gt_eqq : (m >? n : RustM Bool) = pure (decide (m > n)) := rfl
      rw [h_gt_eqq]
      simp only [pure_bind]
      by_cases hgt : m > n
      · -- Case m > n: d = m - n, recurse on the stripped (m - n, n).
        rw [decide_eq_true hgt]
        simp only [if_true]
        have hnm : n.toNat < m.toNat := UInt64.lt_iff_toNat_lt.mp hgt
        have h_sub : (m -? n : RustM u64) = pure (m - n) := by
          have h_no_underflow : UInt64.subOverflow m n = false := by
            generalize hbo : UInt64.subOverflow m n = bo
            cases bo with
            | false => rfl
            | true => exfalso; rw [UInt64.subOverflow_iff] at hbo; omega
          show (rust_primitives.ops.arith.Sub.sub m n : RustM u64) = pure (m - n)
          show (if BitVec.usubOverflow m.toBitVec n.toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (m - n)) = pure (m - n)
          rw [show BitVec.usubOverflow m.toBitVec n.toBitVec = false from h_no_underflow]
          rfl
        rw [h_sub]
        simp only [pure_bind]
        have hd_toNat : (m - n).toNat = m.toNat - n.toNat :=
          UInt64.toNat_sub_of_le' (Nat.le_of_lt hnm)
        have hd_ne : (m - n) ≠ 0 := by
          intro h
          have hz : (m - n).toNat = 0 := by rw [h]; rfl
          omega
        obtain ⟨r, h_tz, hr_lt, hr_dvd, hr_bit⟩ := tz_nonzero_spec (m - n) hd_ne
        rw [h_tz]
        simp only [RustM_ok_bind]
        have hr_lt_2_64 : r.toNat < 2 ^ 64 := by
          have h32 : r.toNat < 2 ^ 32 := UInt32.toNat_lt r
          omega
        have hr_uint64_toNat : (r.toNat.toUInt64).toNat = r.toNat :=
          UInt64.toNat_ofNat_of_lt' hr_lt_2_64
        have h_0_le : (0 : UInt32) ≤ r := by
          rw [UInt32.le_iff_toNat_le]
          show (0 : UInt32).toNat ≤ r.toNat
          have h0 : (0 : UInt32).toNat = 0 := rfl
          omega
        have h_lt_64 : r < (64 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt]
          show r.toNat < (64 : UInt32).toNat
          have h64 : (64 : UInt32).toNat = 64 := rfl
          omega
        have h_shr : ((m - n) >>>? r : RustM u64)
            = RustM.ok ((m - n) >>> r.toNat.toUInt64) := by
          show (rust_primitives.ops.bit.Shr.shr (m - n) r : RustM u64)
              = RustM.ok ((m - n) >>> r.toNat.toUInt64)
          show (if ((0 : UInt32) ≤ r && r < (64 : UInt32)) then
                  pure ((m - n) >>> r.toNat.toUInt64)
                else .fail .integerOverflow) = RustM.ok ((m - n) >>> r.toNat.toUInt64)
          have h_cond_eq : ((0 : UInt32) ≤ r && r < (64 : UInt32)) = true := by
            simp [h_0_le, h_lt_64]
          rw [h_cond_eq]; rfl
        rw [h_shr]
        simp only [RustM_ok_bind]
        have h_m'_toNat : ((m - n) >>> r.toNat.toUInt64).toNat
            = (m - n).toNat >>> r.toNat := by
          rw [UInt64.toNat_shiftRight, hr_uint64_toNat, Nat.mod_eq_of_lt hr_lt]
        have h_m'_div : ((m - n) >>> r.toNat.toUInt64).toNat
            = (m - n).toNat / 2 ^ r.toNat := by
          rw [h_m'_toNat, Nat.shiftRight_eq_div_pow]
        have h_m'_mul : ((m - n) >>> r.toNat.toUInt64).toNat * 2 ^ r.toNat
            = (m - n).toNat := by
          rw [h_m'_div]; exact Nat.div_mul_cancel hr_dvd
        have h_m'_odd : ((m - n) >>> r.toNat.toUInt64).toNat % 2 = 1 := by
          rw [h_m'_toNat, ← Nat.and_one_is_mod]; exact hr_bit
        have h_m'_pos : 0 < ((m - n) >>> r.toNat.toUInt64).toNat := by omega
        have h_meas : ((m - n) >>> r.toNat.toUInt64).toNat + n.toNat < k := by
          have h_le : ((m - n) >>> r.toNat.toUInt64).toNat ≤ (m - n).toNat := by
            rw [h_m'_div]; exact Nat.div_le_self _ _
          omega
        rw [ih (((m - n) >>> r.toNat.toUInt64).toNat + n.toNat) h_meas
              ((m - n) >>> r.toNat.toUInt64) n h_m'_odd hn_odd h_m'_pos hn_pos rfl]
        apply congrArg RustM.ok
        apply congrArg UInt64.ofNat
        rw [nat_gcd_sub_right m.toNat n.toNat (Nat.le_of_lt hnm), ← hd_toNat,
            ← h_m'_mul, nat_gcd_mul_pow_two_left_odd_right _ _ hn_odd]
      · -- Case m < n: d = n - m, recurse on the stripped (m, n - m).
        rw [decide_eq_false hgt]
        simp only [Bool.false_eq_true, if_false]
        have hnm : m.toNat < n.toNat := by
          rcases Nat.lt_trichotomy m.toNat n.toNat with h | h | h
          · exact h
          · exfalso; exact hmn (UInt64.toNat_inj.mp h)
          · exfalso; exact hgt (UInt64.lt_iff_toNat_lt.mpr h)
        have h_sub : (n -? m : RustM u64) = pure (n - m) := by
          have h_no_underflow : UInt64.subOverflow n m = false := by
            generalize hbo : UInt64.subOverflow n m = bo
            cases bo with
            | false => rfl
            | true => exfalso; rw [UInt64.subOverflow_iff] at hbo; omega
          show (rust_primitives.ops.arith.Sub.sub n m : RustM u64) = pure (n - m)
          show (if BitVec.usubOverflow n.toBitVec m.toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (n - m)) = pure (n - m)
          rw [show BitVec.usubOverflow n.toBitVec m.toBitVec = false from h_no_underflow]
          rfl
        rw [h_sub]
        simp only [pure_bind]
        have hd_toNat : (n - m).toNat = n.toNat - m.toNat :=
          UInt64.toNat_sub_of_le' (Nat.le_of_lt hnm)
        have hd_ne : (n - m) ≠ 0 := by
          intro h
          have hz : (n - m).toNat = 0 := by rw [h]; rfl
          omega
        obtain ⟨r, h_tz, hr_lt, hr_dvd, hr_bit⟩ := tz_nonzero_spec (n - m) hd_ne
        rw [h_tz]
        simp only [RustM_ok_bind]
        have hr_lt_2_64 : r.toNat < 2 ^ 64 := by
          have h32 : r.toNat < 2 ^ 32 := UInt32.toNat_lt r
          omega
        have hr_uint64_toNat : (r.toNat.toUInt64).toNat = r.toNat :=
          UInt64.toNat_ofNat_of_lt' hr_lt_2_64
        have h_0_le : (0 : UInt32) ≤ r := by
          rw [UInt32.le_iff_toNat_le]
          show (0 : UInt32).toNat ≤ r.toNat
          have h0 : (0 : UInt32).toNat = 0 := rfl
          omega
        have h_lt_64 : r < (64 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt]
          show r.toNat < (64 : UInt32).toNat
          have h64 : (64 : UInt32).toNat = 64 := rfl
          omega
        have h_shr : ((n - m) >>>? r : RustM u64)
            = RustM.ok ((n - m) >>> r.toNat.toUInt64) := by
          show (rust_primitives.ops.bit.Shr.shr (n - m) r : RustM u64)
              = RustM.ok ((n - m) >>> r.toNat.toUInt64)
          show (if ((0 : UInt32) ≤ r && r < (64 : UInt32)) then
                  pure ((n - m) >>> r.toNat.toUInt64)
                else .fail .integerOverflow) = RustM.ok ((n - m) >>> r.toNat.toUInt64)
          have h_cond_eq : ((0 : UInt32) ≤ r && r < (64 : UInt32)) = true := by
            simp [h_0_le, h_lt_64]
          rw [h_cond_eq]; rfl
        rw [h_shr]
        simp only [RustM_ok_bind]
        have h_n'_toNat : ((n - m) >>> r.toNat.toUInt64).toNat
            = (n - m).toNat >>> r.toNat := by
          rw [UInt64.toNat_shiftRight, hr_uint64_toNat, Nat.mod_eq_of_lt hr_lt]
        have h_n'_div : ((n - m) >>> r.toNat.toUInt64).toNat
            = (n - m).toNat / 2 ^ r.toNat := by
          rw [h_n'_toNat, Nat.shiftRight_eq_div_pow]
        have h_n'_mul : ((n - m) >>> r.toNat.toUInt64).toNat * 2 ^ r.toNat
            = (n - m).toNat := by
          rw [h_n'_div]; exact Nat.div_mul_cancel hr_dvd
        have h_n'_odd : ((n - m) >>> r.toNat.toUInt64).toNat % 2 = 1 := by
          rw [h_n'_toNat, ← Nat.and_one_is_mod]; exact hr_bit
        have h_n'_pos : 0 < ((n - m) >>> r.toNat.toUInt64).toNat := by omega
        have h_meas : m.toNat + ((n - m) >>> r.toNat.toUInt64).toNat < k := by
          have h_le : ((n - m) >>> r.toNat.toUInt64).toNat ≤ (n - m).toNat := by
            rw [h_n'_div]; exact Nat.div_le_self _ _
          omega
        rw [ih (m.toNat + ((n - m) >>> r.toNat.toUInt64).toNat) h_meas
              m ((n - m) >>> r.toNat.toUInt64) hm_odd h_n'_odd hm_pos h_n'_pos rfl]
        apply congrArg RustM.ok
        apply congrArg UInt64.ofNat
        rw [Nat.gcd_comm m.toNat n.toNat,
            nat_gcd_sub_right n.toNat m.toNat (Nat.le_of_lt hnm), ← hd_toNat,
            ← h_n'_mul, nat_gcd_mul_pow_two_left_odd_right _ _ hm_odd]
        exact Nat.gcd_comm m.toNat _

/-! ## Outer-wrapper Nat helpers -/

/-- Combining two pure powers of two under a gcd: for odd `m, n`,
    `gcd (m * 2^p) (n * 2^q) = 2^(min p q) * gcd m n`. -/
private theorem gcd_two_pow_combine (m n p q : Nat)
    (hm : m % 2 = 1) (hn : n % 2 = 1) :
    Nat.gcd (m * 2 ^ p) (n * 2 ^ q) = 2 ^ (min p q) * Nat.gcd m n := by
  rcases Nat.le_total p q with hpq | hqp
  · rw [Nat.min_eq_left hpq]
    have h2q : (2 : Nat) ^ q = 2 ^ (q - p) * 2 ^ p := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2q, ← Nat.mul_assoc, Nat.gcd_mul_right]
    have h_strip : Nat.gcd m (n * 2 ^ (q - p)) = Nat.gcd m n := by
      rw [Nat.gcd_comm m (n * 2 ^ (q - p)),
          nat_gcd_mul_pow_two_left_odd_right n m hm (q - p),
          Nat.gcd_comm n m]
    rw [h_strip, Nat.mul_comm]
  · rw [Nat.min_eq_right hqp]
    have h2p : (2 : Nat) ^ p = 2 ^ (p - q) * 2 ^ q := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2p, ← Nat.mul_assoc, Nat.gcd_mul_right,
        nat_gcd_mul_pow_two_left_odd_right m n hn (p - q), Nat.mul_comm]

/-- If `2^s` divides `m * 2^t` with `m` odd, then `s ≤ t`. -/
private theorem pow_two_dvd_odd_mul (s m t : Nat)
    (hdvd : 2 ^ s ∣ m * 2 ^ t) (hm : m % 2 = 1) : s ≤ t := by
  by_cases hcon : s ≤ t
  · exact hcon
  · exfalso
    have hts : t + 1 ≤ s := by omega
    have h_dvd' : 2 ^ (t + 1) ∣ m * 2 ^ t := Nat.dvd_trans (Nat.pow_dvd_pow 2 hts) hdvd
    rw [Nat.pow_succ, Nat.mul_comm m (2 ^ t)] at h_dvd'
    have h2m : 2 ∣ m := (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos t)).mp h_dvd'
    omega

/-- `2^k` divides `z` iff all of `z`'s low `k` bits are zero. -/
private theorem two_pow_dvd_iff_testBit (k z : Nat) :
    2 ^ k ∣ z ↔ ∀ i, i < k → Nat.testBit z i = false := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have h2split : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    constructor
    · intro hdvd i hik
      obtain ⟨c, hc⟩ := hdvd
      have hz_half : z / 2 = 2 ^ k * c := by
        rw [hc, h2split, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false :=
        (ih (z / 2)).mp ⟨c, hz_half⟩
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        have hz_even : z % 2 = 0 := by
          have hzc : z = 2 * (2 ^ k * c) := by rw [hc, h2split, Nat.mul_assoc]
          omega
        exact Nat.mod_two_eq_zero_iff_testBit_zero.mp hz_even
      · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        subst hj
        rw [Nat.testBit_succ]
        exact hbits_half j (by omega)
    · intro hbits
      have hz_even : z % 2 = 0 :=
        Nat.mod_two_eq_zero_iff_testBit_zero.mpr (hbits 0 (by omega))
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false := by
        intro j hjk
        rw [← Nat.testBit_succ]
        exact hbits (j + 1) (by omega)
      obtain ⟨c, hc⟩ := (ih (z / 2)).mpr hbits_half
      refine ⟨c, ?_⟩
      have hz2 : z = 2 * (z / 2) := by omega
      rw [hz2, hc, h2split, Nat.mul_assoc]

/-- `2^k` divides a bitwise-or iff it divides each operand. -/
private theorem two_pow_dvd_or (k x y : Nat) :
    2 ^ k ∣ (x ||| y) ↔ 2 ^ k ∣ x ∧ 2 ^ k ∣ y := by
  rw [two_pow_dvd_iff_testBit, two_pow_dvd_iff_testBit, two_pow_dvd_iff_testBit]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' := h i hi
      rw [Nat.testBit_or] at hi'
      exact (Bool.or_eq_false_iff.mp hi').1
    · have hi' := h i hi
      rw [Nat.testBit_or] at hi'
      exact (Bool.or_eq_false_iff.mp hi').2
  · intro ⟨hx, hy⟩ i hi
    rw [Nat.testBit_or, hx i hi, hy i hi]
    rfl

/-! ## Master closed-form postcondition -/

theorem gcd_stein_postcondition (a b : u64) :
    gcd_stein_u64.gcd_stein a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  -- The function body has three branches:
  --   (i)   `a = 0`: returns `a ||| b = b`; gcd(0, b) = b.
  --   (ii)  `b = 0` (a ≠ 0): returns `a ||| b = a`; gcd(a, 0) = a.
  --   (iii) both nonzero: compute shift = tz(a|b), m = a>>tz(a), n = b>>tz(b),
  --         return gcd_stein_loop m n << shift.
  -- We dispatch (i)-(ii) completely; (iii) is sorried with structural unblock.
  unfold gcd_stein_u64.gcd_stein
  -- Each `(x ==? y)` definitionally equals `pure (x == y)`; the `||?` returns
  -- `pure (l || r)`. After all binds simplify, the head `if` test on `Bool`
  -- becomes `((a == 0) || (b == 0))`.
  have h_a_eqq : (a ==? (0 : u64) : RustM Bool) = pure (a == (0 : u64)) := rfl
  have h_b_eqq : (b ==? (0 : u64) : RustM Bool) = pure (b == (0 : u64)) := rfl
  have h_or_def : ∀ (x y : Bool),
      (x ||? y : RustM Bool) = pure (x || y) := fun _ _ => rfl
  rw [h_a_eqq, h_b_eqq]
  simp only [pure_bind, h_or_def]
  -- Goal: (if ((a == 0) || (b == 0)) = true then (a |||? b) else ...) = ...
  by_cases ha : a = 0
  · -- Branch (i): a = 0.
    subst ha
    have h_dec : ((0 : u64) == (0 : u64)) = true := rfl
    rw [h_dec]
    simp only [Bool.true_or, if_true]
    -- Goal: pure (0 ||| b) = RustM.ok (UInt64.ofNat (Nat.gcd 0 b.toNat))
    show RustM.ok (0 ||| b) = RustM.ok (UInt64.ofNat (Nat.gcd 0 b.toNat))
    congr 1
    rw [Nat.gcd_zero_left]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' b.toNat_lt]
    show (0 ||| b).toNat = b.toNat
    rw [UInt64.toNat_or]
    show (0 : u64).toNat ||| b.toNat = b.toNat
    show 0 ||| b.toNat = b.toNat
    exact Nat.zero_or _
  · by_cases hb : b = 0
    · -- Branch (ii): a ≠ 0, b = 0.
      subst hb
      have h_a_dec : (a == (0 : u64)) = false := beq_eq_false_iff_ne.mpr ha
      have h_b_dec : ((0 : u64) == (0 : u64)) = true := rfl
      rw [h_a_dec, h_b_dec]
      simp only [Bool.false_or, if_true]
      show RustM.ok (a ||| 0) = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat 0))
      congr 1
      rw [Nat.gcd_zero_right]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' a.toNat_lt]
      show (a ||| 0).toNat = a.toNat
      rw [UInt64.toNat_or]
      show a.toNat ||| (0 : u64).toNat = a.toNat
      show a.toNat ||| 0 = a.toNat
      exact Nat.or_zero _
    · -- Branch (iii): a ≠ 0 ∧ b ≠ 0.
      have h_a_dec : (a == (0 : u64)) = false := beq_eq_false_iff_ne.mpr ha
      have h_b_dec : (b == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hb
      rw [h_a_dec, h_b_dec]
      simp only [Bool.false_or, Bool.false_eq_true, if_false]
      -- Both nonzero ⟹ `a ||| b ≠ 0`.
      have h_ab_or : (a ||| b).toNat = a.toNat ||| b.toNat := UInt64.toNat_or a b
      have h_ab_ne : a ||| b ≠ 0 := by
        intro hcon
        apply ha
        apply UInt64.toNat_inj.mp
        show a.toNat = (0 : u64).toNat
        have h_or0 : a.toNat ||| b.toNat = 0 := by
          have h1 : (a ||| b).toNat = 0 := by rw [hcon]; rfl
          rwa [h_ab_or] at h1
        have h_dvd : (2 : Nat) ^ 64 ∣ (a.toNat ||| b.toNat) := by
          rw [h_or0]; exact Nat.dvd_zero _
        have h_a_dvd := ((two_pow_dvd_or 64 a.toNat b.toNat).mp h_dvd).1
        have h_a0 : a.toNat = 0 := Nat.eq_zero_of_dvd_of_lt h_a_dvd (UInt64.toNat_lt a)
        rw [h_a0]; rfl
      -- Trailing-zeros specs for `a ||| b`, `a`, `b`.
      obtain ⟨shift, h_tz_ab, hsh_lt, hsh_dvd, hsh_bit⟩ :=
        tz_nonzero_spec (a ||| b) h_ab_ne
      obtain ⟨mTz, h_tz_a, hmTz_lt, hmTz_dvd, hmTz_bit⟩ := tz_nonzero_spec a ha
      obtain ⟨nTz, h_tz_b, hnTz_lt, hnTz_dvd, hnTz_bit⟩ := tz_nonzero_spec b hb
      -- Shift-amount reductions for `a >>> mTz` and `b >>> nTz`.
      have h_shr_a : (a >>>? mTz : RustM u64) = RustM.ok (a >>> mTz.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shr.shr a mTz : RustM u64)
            = RustM.ok (a >>> mTz.toNat.toUInt64)
        show (if ((0 : UInt32) ≤ mTz && mTz < (64 : UInt32)) then
                pure (a >>> mTz.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok (a >>> mTz.toNat.toUInt64)
        have h_c : ((0 : UInt32) ≤ mTz && mTz < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ mTz := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ mTz.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : mTz < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show mTz.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      have h_shr_b : (b >>>? nTz : RustM u64) = RustM.ok (b >>> nTz.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shr.shr b nTz : RustM u64)
            = RustM.ok (b >>> nTz.toNat.toUInt64)
        show (if ((0 : UInt32) ≤ nTz && nTz < (64 : UInt32)) then
                pure (b >>> nTz.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok (b >>> nTz.toNat.toUInt64)
        have h_c : ((0 : UInt32) ≤ nTz && nTz < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ nTz := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ nTz.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : nTz < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show nTz.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      -- toNat of the trailing-zero counts (they are < 64 < 2^64).
      have hmTz_lt64 : mTz.toNat < 2 ^ 64 := by omega
      have hmTz_u : mTz.toNat.toUInt64.toNat = mTz.toNat :=
        UInt64.toNat_ofNat_of_lt' hmTz_lt64
      have hnTz_lt64 : nTz.toNat < 2 ^ 64 := by omega
      have hnTz_u : nTz.toNat.toUInt64.toNat = nTz.toNat :=
        UInt64.toNat_ofNat_of_lt' hnTz_lt64
      -- The stripped values `m = a >>> mTz`, `n = b >>> nTz`.
      have h_m_toNat : (a >>> mTz.toNat.toUInt64).toNat = a.toNat / 2 ^ mTz.toNat := by
        rw [UInt64.toNat_shiftRight, hmTz_u, Nat.mod_eq_of_lt hmTz_lt,
            Nat.shiftRight_eq_div_pow]
      have h_n_toNat : (b >>> nTz.toNat.toUInt64).toNat = b.toNat / 2 ^ nTz.toNat := by
        rw [UInt64.toNat_shiftRight, hnTz_u, Nat.mod_eq_of_lt hnTz_lt,
            Nat.shiftRight_eq_div_pow]
      have h_m_odd : (a >>> mTz.toNat.toUInt64).toNat % 2 = 1 := by
        rw [← Nat.and_one_is_mod, UInt64.toNat_shiftRight, hmTz_u,
            Nat.mod_eq_of_lt hmTz_lt]
        exact hmTz_bit
      have h_n_odd : (b >>> nTz.toNat.toUInt64).toNat % 2 = 1 := by
        rw [← Nat.and_one_is_mod, UInt64.toNat_shiftRight, hnTz_u,
            Nat.mod_eq_of_lt hnTz_lt]
        exact hnTz_bit
      have h_a_eq : a.toNat = (a >>> mTz.toNat.toUInt64).toNat * 2 ^ mTz.toNat := by
        rw [h_m_toNat]; exact (Nat.div_mul_cancel hmTz_dvd).symm
      have h_b_eq : b.toNat = (b >>> nTz.toNat.toUInt64).toNat * 2 ^ nTz.toNat := by
        rw [h_n_toNat]; exact (Nat.div_mul_cancel hnTz_dvd).symm
      -- `shift = min mTz nTz`.
      have hsh_a : 2 ^ shift.toNat ∣ a.toNat := by
        have h := hsh_dvd; rw [h_ab_or] at h
        exact ((two_pow_dvd_or shift.toNat a.toNat b.toNat).mp h).1
      have hsh_b : 2 ^ shift.toNat ∣ b.toNat := by
        have h := hsh_dvd; rw [h_ab_or] at h
        exact ((two_pow_dvd_or shift.toNat a.toNat b.toNat).mp h).2
      have hsh_le_mTz : shift.toNat ≤ mTz.toNat := by
        rw [h_a_eq] at hsh_a
        exact pow_two_dvd_odd_mul shift.toNat _ mTz.toNat hsh_a h_m_odd
      have hsh_le_nTz : shift.toNat ≤ nTz.toNat := by
        rw [h_b_eq] at hsh_b
        exact pow_two_dvd_odd_mul shift.toNat _ nTz.toNat hsh_b h_n_odd
      have h_shift_eq : shift.toNat = min mTz.toNat nTz.toNat := by
        rcases Nat.lt_or_ge shift.toNat (min mTz.toNat nTz.toNat) with hlt | hge
        · exfalso
          have hd_a : 2 ^ (shift.toNat + 1) ∣ a.toNat :=
            Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hmTz_dvd
          have hd_b : 2 ^ (shift.toNat + 1) ∣ b.toNat :=
            Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hnTz_dvd
          have hd_ab : 2 ^ (shift.toNat + 1) ∣ (a.toNat ||| b.toNat) :=
            (two_pow_dvd_or (shift.toNat + 1) a.toNat b.toNat).mpr ⟨hd_a, hd_b⟩
          rw [← h_ab_or] at hd_ab
          obtain ⟨c, hc⟩ := hd_ab
          have hbit0 : ((a ||| b).toNat >>> shift.toNat) &&& 1 = 0 := by
            rw [hc, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_assoc,
                Nat.mul_div_cancel_left _ (Nat.two_pow_pos shift.toNat),
                Nat.and_one_is_mod]
            exact Nat.mul_mod_right 2 c
          rw [hbit0] at hsh_bit
          exact absurd hsh_bit (by decide)
        · omega
      -- Reduce the monadic body.
      rw [h_tz_ab]
      simp only [RustM_ok_bind]
      rw [h_tz_a]
      simp only [RustM_ok_bind]
      rw [h_shr_a]
      simp only [RustM_ok_bind]
      rw [h_tz_b]
      simp only [RustM_ok_bind]
      rw [h_shr_b]
      simp only [RustM_ok_bind]
      rw [gcd_stein_loop_spec (a >>> mTz.toNat.toUInt64) (b >>> nTz.toNat.toUInt64)
            h_m_odd h_n_odd]
      simp only [RustM_ok_bind]
      -- Final left shift + algebraic bridge.
      have h_combine : Nat.gcd a.toNat b.toNat
            = 2 ^ shift.toNat * Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
                (b >>> nTz.toNat.toUInt64).toNat := by
        rw [h_a_eq, h_b_eq, gcd_two_pow_combine _ _ _ _ h_m_odd h_n_odd, h_shift_eq]
      have hsh_lt64 : shift.toNat < 2 ^ 64 := by omega
      have hsh_u : shift.toNat.toUInt64.toNat = shift.toNat :=
        UInt64.toNat_ofNat_of_lt' hsh_lt64
      have h_shl : ((UInt64.ofNat (Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
            (b >>> nTz.toNat.toUInt64).toNat)) <<<? shift : RustM u64)
          = RustM.ok ((UInt64.ofNat (Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
              (b >>> nTz.toNat.toUInt64).toNat)) <<< shift.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shl.shl _ shift : RustM u64) = RustM.ok _
        show (if ((0 : UInt32) ≤ shift && shift < (64 : UInt32)) then
                pure (_ <<< shift.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok _
        have h_c : ((0 : UInt32) ≤ shift && shift < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ shift := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ shift.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : shift < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show shift.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      rw [h_shl]
      apply congrArg RustM.ok
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b), UInt64.toNat_shiftLeft,
          UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 _ _), hsh_u,
          Nat.mod_eq_of_lt (show shift.toNat < 64 by omega), Nat.shiftLeft_eq,
          Nat.mul_comm, ← h_combine]
      exact Nat.mod_eq_of_lt (gcd_lt_2_64 a b)

/-! ## Contract clauses derived from the closed form

Each derived clause goes through `gcd_stein_postcondition`; once the master
closes, every clause below closes automatically. -/

/-- Totality / no panic: `gcd_stein` returns a value on every `u64 × u64`
    input — no division by zero, no shift overflow, no add/sub overflow. The
    Rust source has no `panic!`; failure modes are confined to the inner
    arithmetic primitives, all of which the closed form rules out. -/
theorem gcd_stein_total (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v :=
  ⟨_, gcd_stein_postcondition a b⟩

/-- Boundary `gcd(0, 0) = 0`: captures the `zero_zero_is_zero` test and pins
    the source's `m | n` shortcut at the all-zero input. -/
theorem gcd_stein_zero_zero :
    gcd_stein_u64.gcd_stein 0 0 = RustM.ok 0 := by
  unfold gcd_stein_u64.gcd_stein
  rfl

/-- Common-divisor half (left): the result divides `a`. Captures the
    `a % g == 0` arm of `result_divides_both_inputs` (and recovers `gcd(0, b) = b`
    via the divisibility of any `v` by `0`). -/
theorem gcd_stein_divides_a (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ a.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left a.toNat b.toNat

/-- Common-divisor half (right): the result divides `b`. Captures the
    `b % g == 0` arm of `result_divides_both_inputs`. -/
theorem gcd_stein_divides_b (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ b.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_right a.toNat b.toNat

/-- Greatest-common-divisor half: every common divisor of `a` and `b` divides
    the result. Captures the `result_is_greatest` test. Combined with
    `gcd_stein_divides_a` / `gcd_stein_divides_b`, this characterises the
    result as the maximum common divisor in the divisibility lattice. -/
theorem gcd_stein_greatest (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧
      ∀ d : Nat, d ∣ a.toNat → d ∣ b.toNat → d ∣ v.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  intro d hda hdb
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hda hdb

/-- Zero-result clause: the result is `0` only when both inputs are `0`.
    Captures the `g == 0 → a == 0 ∧ b == 0` arm of `result_divides_both_inputs`. -/
theorem gcd_stein_zero_iff (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧
      (v = 0 → a = 0 ∧ b = 0) := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  intro hv
  -- hv : UInt64.ofNat (Nat.gcd a.toNat b.toNat) = 0
  have h_gcd_zero : Nat.gcd a.toNat b.toNat = 0 := by
    have h := congrArg UInt64.toNat hv
    rw [gcd_toNat_ofNat] at h
    exact h
  -- From gcd = 0: gcd | a and gcd | b, so 0 | a and 0 | b, so a = b = 0.
  have h_dvd_a : Nat.gcd a.toNat b.toNat ∣ a.toNat := Nat.gcd_dvd_left _ _
  have h_dvd_b : Nat.gcd a.toNat b.toNat ∣ b.toNat := Nat.gcd_dvd_right _ _
  rw [h_gcd_zero] at h_dvd_a h_dvd_b
  have ha_nat : a.toNat = 0 := Nat.eq_zero_of_zero_dvd h_dvd_a
  have hb_nat : b.toNat = 0 := Nat.eq_zero_of_zero_dvd h_dvd_b
  refine ⟨?_, ?_⟩
  · apply UInt64.toNat_inj.mp; rw [ha_nat]; rfl
  · apply UInt64.toNat_inj.mp; rw [hb_nat]; rfl

end Gcd_stein_u64Obligations
