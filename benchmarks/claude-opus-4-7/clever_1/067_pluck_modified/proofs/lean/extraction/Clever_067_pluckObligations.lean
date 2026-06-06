-- Companion obligations file for the `clever_067_pluck` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_067_pluck

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_067_pluckObligations

/-! ## Predicates used in the contract. -/

/-- An `i64` value is even (the spec interprets `l[i] % 2 == 0` in `Int`;
    since the test compares to `0`, this is sign-agnostic). -/
private abbrev isEven (x : i64) : Prop := x.toInt % 2 = 0

/-- There exists an even element in `s`. -/
private abbrev hasEven (s : RustSlice i64) : Prop :=
  ∃ (i : Nat) (hi : i < s.val.size), isEven (s.val[i]'hi)

/-! ## Standard helper lemmas. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_no_bv (i : usize) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hii := (USize64.uaddOverflow_iff i 1).mp hbo
    rw [usize_one_toNat] at hii
    omega

private theorem usize_add_one_eq (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [usize_add_one_no_bv i h]; rfl

/-! ## i64 even-ness bridge.

The Rust check `l[i] % 2 == 0` (on `i64`) is equivalent to the spec's
`isEven`, namely `l[i].toInt % 2 = 0`. We bridge through `tmod` (the
two's-complement `srem`), which agrees with `Int.emod` modulo 2 because
the difference `tmod - emod` is always a multiple of 2. -/

private theorem i64_mod_two_eq_zero_iff (x : i64) :
    ((x % (2 : i64)) = (0 : i64)) ↔ x.toInt % 2 = 0 := by
  constructor
  · intro h
    have h_toInt : (x % 2 : i64).toInt = (0 : i64).toInt := by rw [h]
    -- Reduce to Int128, where toInt_mod is available.
    have h_via128 : (x % 2 : i64).toInt128.toInt = (x.toInt128 % (2 : i64).toInt128).toInt := by
      rw [Int64.toInt128_mod]
    rw [Int64.toInt_toInt128] at h_via128
    rw [h_via128] at h_toInt
    rw [Int128.toInt_mod] at h_toInt
    rw [Int64.toInt_toInt128] at h_toInt
    rw [show (((2 : i64).toInt128).toInt) = (2 : Int) from rfl] at h_toInt
    rw [show ((0 : i64).toInt) = (0 : Int) from by decide] at h_toInt
    -- h_toInt : x.toInt.tmod 2 = 0
    -- Goal: x.toInt % 2 = 0
    -- Int.tmod 2 = 0 ↔ 2 ∣ x ↔ Int.emod 2 = 0
    have h_dvd : (2 : Int) ∣ x.toInt := Int.dvd_of_tmod_eq_zero h_toInt
    exact Int.emod_eq_zero_of_dvd h_dvd
  · intro h
    apply Int64.toInt_inj.mp
    have h_via128 : (x % 2 : i64).toInt128.toInt = (x.toInt128 % (2 : i64).toInt128).toInt := by
      rw [Int64.toInt128_mod]
    rw [Int64.toInt_toInt128] at h_via128
    rw [h_via128]
    rw [Int128.toInt_mod]
    rw [Int64.toInt_toInt128]
    rw [show (((2 : i64).toInt128).toInt) = (2 : Int) from rfl]
    rw [show ((0 : i64).toInt) = (0 : Int) from by decide]
    -- Goal: x.toInt.tmod 2 = 0
    have h_dvd : (2 : Int) ∣ x.toInt := Int.dvd_of_emod_eq_zero h
    exact Int.tmod_eq_zero_of_dvd h_dvd

/-! ## Step lemmas for `smallest_even_at`. -/

/-- Stop case: when `i ≥ size`, returns `(best, found)`. -/
private theorem smallest_even_at_oob
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : l.val.size ≤ i.toNat) :
    clever_067_pluck.smallest_even_at l i best found
      = RustM.ok (rust_primitives.hax.Tuple2.mk best found) := by
  conv => lhs; unfold clever_067_pluck.smallest_even_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- Index lemma: `l[i]_? = RustM.ok (l.val[i.toNat])` when `i.toNat < l.val.size`. -/
private theorem slice_index_eq (l : RustSlice i64) (i : usize)
    (hi : i.toNat < l.val.size) :
    (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
  show (if h : i.toNat < l.val.size then pure (l.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (l.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-- Helper: `(x %? 2 : RustM i64) = RustM.ok (x % 2)` (since `2 ≠ -1, 0`). -/
private theorem i64_rem_two_eq (x : i64) :
    (x %? (2 : i64) : RustM i64) = RustM.ok (x % 2) := by
  show (rust_primitives.ops.arith.Rem.rem x 2 : RustM i64) = RustM.ok (x % 2)
  show (if (x = Int64.minValue && (2 : i64) = -1) then (.fail .integerOverflow : RustM i64)
        else if (2 : i64) = 0 then .fail .divisionByZero
        else pure (x % 2)) = _
  have h_and : (x = Int64.minValue && decide ((2 : i64) = -1)) = false := by
    rw [show (decide ((2 : i64) = -1)) = false from by decide]
    exact Bool.and_false _
  rw [h_and]
  rw [if_neg (by decide : ¬ ((2 : i64) = 0))]
  rfl

/-- Take case: when `i < size`, `l[i]` is even, and (¬ found ∨ l[i] < best),
    recurse with `(i+1, l[i], true)`. -/
private theorem smallest_even_at_take
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_even : isEven (l.val[i.toNat]'hi))
    (h_cond2 : ¬ found ∨ (l.val[i.toNat]'hi).toInt < best.toInt) :
    clever_067_pluck.smallest_even_at l i best found
      = clever_067_pluck.smallest_even_at l (i + 1) (l.val[i.toNat]'hi) true := by
  conv => lhs; unfold clever_067_pluck.smallest_even_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_rem := i64_rem_two_eq (l.val[i.toNat]'hi)
  -- The evenness check: (l[i] % 2) == 0 is true
  have h_even_eq : ((l.val[i.toNat]'hi) % 2 : i64) = 0 :=
    (i64_mod_two_eq_zero_iff (l.val[i.toNat]'hi)).mpr h_even
  have h_beq_zero : ((l.val[i.toNat]'hi) % 2 == (0 : i64)) = true := by
    rw [beq_iff_eq]; exact h_even_eq
  -- The OR condition: ¬found ∨ l[i] < best
  have h_not_found_or : ((!found) || decide ((l.val[i.toNat]'hi) < best)) = true := by
    rcases h_cond2 with hnf | hlt
    · have h_false : found = false := by
        cases found
        · rfl
        · exact absurd rfl hnf
      rw [h_false]; rfl
    · have h_dec : decide ((l.val[i.toNat]'hi) < best) = true := by
        rw [decide_eq_true_iff]
        exact Int64.lt_iff_toInt_lt.mpr hlt
      rw [h_dec]; rw [Bool.or_true]
  have h_and_true :
      (((l.val[i.toNat]'hi) % 2 == (0 : i64)) && ((!found) || decide ((l.val[i.toNat]'hi) < best))) = true := by
    rw [h_beq_zero, h_not_found_or]; rfl
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_rem, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and, rust_primitives.cmp.lt,
             h_add_eq, h_and_true]

/-- Skip case: when `i < size` and either `l[i]` is odd or (found ∧ best ≤ l[i]),
    recurse with `(i+1, best, found)`. -/
private theorem smallest_even_at_skip
    (l : RustSlice i64) (i : usize) (best : i64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_cond : ¬ isEven (l.val[i.toNat]'hi) ∨
               (found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi).toInt)) :
    clever_067_pluck.smallest_even_at l i best found
      = clever_067_pluck.smallest_even_at l (i + 1) best found := by
  conv => lhs; unfold clever_067_pluck.smallest_even_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_rem := i64_rem_two_eq (l.val[i.toNat]'hi)
  have h_and_false :
      (((l.val[i.toNat]'hi) % 2 == (0 : i64)) && ((!found) || decide ((l.val[i.toNat]'hi) < best))) = false := by
    rcases h_cond with h_odd | ⟨h_found, h_ge⟩
    · -- evenness check is false
      have h_neq : ((l.val[i.toNat]'hi) % 2 : i64) ≠ 0 := by
        intro h_eq
        exact h_odd ((i64_mod_two_eq_zero_iff (l.val[i.toNat]'hi)).mp h_eq)
      have h_beq_false : ((l.val[i.toNat]'hi) % 2 == (0 : i64)) = false := by
        rw [beq_eq_false_iff_ne]; exact h_neq
      rw [h_beq_false]; rfl
    · -- found = true and best ≤ l[i]
      have h_not_found : (!found) = false := by
        rw [h_found]; rfl
      have h_not_lt : decide ((l.val[i.toNat]'hi) < best) = false := by
        rw [decide_eq_false_iff_not]
        intro h_lt
        have h_lt_int : (l.val[i.toNat]'hi).toInt < best.toInt := Int64.lt_iff_toInt_lt.mp h_lt
        omega
      rw [h_not_found, h_not_lt]
      simp
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_rem, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and, rust_primitives.cmp.lt,
             h_add_eq, h_and_false]

/-! ## Master correctness lemma for `smallest_even_at`. -/

private theorem smallest_even_at_correct (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (best : i64) (found : Bool),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      ∃ (rv : i64) (rf : Bool),
        clever_067_pluck.smallest_even_at l i best found
          = RustM.ok (rust_primitives.hax.Tuple2.mk rv rf) ∧
        (rf = true ↔ found = true ∨ ∃ (j : Nat) (hj : j < l.val.size),
                                       i.toNat ≤ j ∧ isEven (l.val[j]'hj)) ∧
        (rf = true →
          (found = true ∧ rv = best) ∨
          ∃ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j ∧ rv = (l.val[j]'hj) ∧ isEven (l.val[j]'hj)) ∧
        (rf = true →
          (found = true → rv.toInt ≤ best.toInt) ∧
          ∀ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j → isEven (l.val[j]'hj) →
            rv.toInt ≤ (l.val[j]'hj).toInt) := by
  intro m
  induction m with
  | zero =>
    intro i best found hm hi_le
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨best, found, smallest_even_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
    · -- liveness
      constructor
      · intro hf
        left; exact hf
      · rintro (hf | ⟨j, hj, h_jge, h_even⟩)
        · exact hf
        · -- j ≥ i = size and j < size: contradiction
          rw [hi_eq] at h_jge; omega
    · -- membership
      intro hrf; left
      exact ⟨hrf, rfl⟩
    · -- minimality
      intro hrf
      refine ⟨fun _ => Int.le_refl _, ?_⟩
      intro j hj h_jge h_even
      -- j ≥ i = size and j < size: contradiction
      rw [hi_eq] at h_jge; omega
  | succ m ih =>
    intro i best found hm hi_le
    by_cases hi_ge : l.val.size ≤ i.toNat
    · -- OOB case (same as base)
      have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨best, found, smallest_even_at_oob l i best found hi_ge, ?_, ?_, ?_⟩
      · constructor
        · intro hf; left; exact hf
        · rintro (hf | ⟨j, hj, h_jge, h_even⟩)
          · exact hf
          · rw [hi_eq] at h_jge; omega
      · intro hrf; left; exact ⟨hrf, rfl⟩
      · intro hrf
        refine ⟨fun _ => Int.le_refl _, ?_⟩
        intro j hj h_jge h_even
        rw [hi_eq] at h_jge; omega
    · -- i.toNat < l.val.size
      have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      by_cases h_take :
          isEven (l.val[i.toNat]'hi_lt) ∧
          (¬ found = true ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt)
      · -- TAKE branch
        obtain ⟨h_even_i, h_cond2_raw⟩ := h_take
        have h_cond2 : ¬ (found = true) ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt :=
          h_cond2_raw
        have h_cond2' : (¬ found = true) ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt :=
          h_cond2
        have h_cond2_simpl : ¬ found ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt := by
          rcases h_cond2 with hf | hlt
          · left; intro h_eq; apply hf; cases found
            · cases h_eq
            · rfl
          · right; exact hlt
        have h_step :=
          smallest_even_at_take l i best found hi_lt h_even_i h_cond2_simpl
        -- Apply IH with new state (i+1, l[i], true).
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) (l.val[i.toNat]'hi_lt) true h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness for (i, best, found)
          constructor
          · intro hrf
            -- Show found ∨ ∃ j ≥ i, isEven l[j]
            right
            exact ⟨i.toNat, hi_lt, Nat.le_refl _, h_even_i⟩
          · intro _
            -- Show rf = true. Apply h_live; we have found' = true.
            apply h_live.mpr
            left; rfl
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf_true, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jeven⟩
          · -- rv = l[i] (since new best = l[i])
            right
            refine ⟨i.toNat, hi_lt, Nat.le_refl _, ?_, h_even_i⟩
            exact hrv_eq
          · -- rv = l[j] for j ≥ i+1 ≥ i
            right
            refine ⟨j, hj, ?_, h_rv_eq, h_jeven⟩
            rw [h_i1] at h_jge; omega
        · -- minimality
          intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          have h_min_li : rv.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := h_min_best rfl
          refine ⟨?_, ?_⟩
          · -- found = true → rv ≤ best.
            intro hf
            -- Take case: when found = true, we have l[i] < best.
            rcases h_cond2 with hnf | hlt
            · exact absurd hf hnf
            · have : rv.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := h_min_li
              omega
          · intro j hj h_jge h_jeven
            by_cases h_jeq : j = i.toNat
            · -- rv ≤ l[i] from h_min_li
              subst h_jeq; exact h_min_li
            · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
              exact h_min_suffix j hj h_jge1 h_jeven
      · -- SKIP branch (negation of TAKE)
        have h_skip_cond :
            ¬ isEven (l.val[i.toNat]'hi_lt) ∨
            (found = true ∧ best.toInt ≤ (l.val[i.toNat]'hi_lt).toInt) := by
          by_cases h_even_i : isEven (l.val[i.toNat]'hi_lt)
          · right
            -- ¬ (h_even_i ∧ (¬ found ∨ l[i] < best)) and h_even_i.
            have h_neg : ¬ (¬ found = true ∨ (l.val[i.toNat]'hi_lt).toInt < best.toInt) := by
              intro h
              exact h_take ⟨h_even_i, h⟩
            -- Manual de Morgan: ¬ (P ∨ Q) → ¬ P ∧ ¬ Q.
            have h_nf : ¬ ¬ found = true := fun hnf => h_neg (Or.inl hnf)
            have h_nlt : ¬ (l.val[i.toNat]'hi_lt).toInt < best.toInt :=
              fun hlt => h_neg (Or.inr hlt)
            have hf : found = true := by
              cases found
              · exact absurd (by intro h; exact Bool.noConfusion h) h_nf
              · rfl
            refine ⟨hf, ?_⟩
            omega
          · left; exact h_even_i
        have h_step :=
          smallest_even_at_skip l i best found hi_lt h_skip_cond
        -- Apply IH with same state.
        obtain ⟨rv, rf, hres, h_live, h_mem, h_min⟩ :=
          ih (i + 1) best found h_m_le h_i1_le
        refine ⟨rv, rf, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- liveness
          constructor
          · intro hrf
            rcases h_live.mp hrf with hf | ⟨j, hj, h_jge, h_jeven⟩
            · left; exact hf
            · right; refine ⟨j, hj, ?_, h_jeven⟩
              rw [h_i1] at h_jge; omega
          · rintro (hf | ⟨j, hj, h_jge, h_jeven⟩)
            · apply h_live.mpr; left; exact hf
            · -- j ≥ i. Either j = i (then isEven l[i], handled by skip-cond) or j ≥ i+1.
              apply h_live.mpr
              by_cases h_jeq : j = i.toNat
              · -- isEven l[i]; from skip cond, found ∧ best ≤ l[i] holds. So found.
                subst h_jeq
                rcases h_skip_cond with h_neg | ⟨hf, _⟩
                · exact absurd h_jeven h_neg
                · left; exact hf
              · right
                refine ⟨j, hj, ?_, h_jeven⟩
                rw [h_i1]; omega
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf, hrv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq, h_jeven⟩
          · left; exact ⟨hf, hrv_eq⟩
          · right
            refine ⟨j, hj, ?_, h_rv_eq, h_jeven⟩
            rw [h_i1] at h_jge; omega
        · -- minimality
          intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          refine ⟨h_min_best, ?_⟩
          intro j hj h_jge h_jeven
          by_cases h_jeq : j = i.toNat
          · -- isEven l[i] (since h_jeven and j = i.toNat).
            subst h_jeq
            rcases h_skip_cond with h_neg | ⟨hf, h_ge⟩
            · exact absurd h_jeven h_neg
            · -- found = true and best ≤ l[i].
              have h_rv_best : rv.toInt ≤ best.toInt := h_min_best hf
              omega
          · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_min_suffix j hj h_jge1 h_jeven

/-! ## Step lemmas for `first_index_of`. -/

private theorem first_index_of_oob (l : RustSlice i64) (target : i64) (i : usize)
    (hi : l.val.size ≤ i.toNat) :
    clever_067_pluck.first_index_of l target i = RustM.ok (0 : u64) := by
  conv => lhs; unfold clever_067_pluck.first_index_of
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem first_index_of_found
    (l : RustSlice i64) (target : i64) (i : usize)
    (hi : i.toNat < l.val.size)
    (h : (l.val[i.toNat]'hi) = target) :
    clever_067_pluck.first_index_of l target i = RustM.ok (USize64.toUInt64 i) := by
  conv => lhs; unfold clever_067_pluck.first_index_of
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_beq : ((l.val[i.toNat]'hi) == target) = true := by rw [beq_iff_eq]; exact h
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.eq, h_beq]
  -- cast_op : usize → u64 = pure (USize64.toUInt64 i)
  show (rust_primitives.hax.cast_op i : RustM u64) = _
  rfl

private theorem first_index_of_recurse
    (l : RustSlice i64) (target : i64) (i : usize)
    (hi : i.toNat < l.val.size)
    (h : (l.val[i.toNat]'hi) ≠ target) :
    clever_067_pluck.first_index_of l target i
      = clever_067_pluck.first_index_of l target (i + 1) := by
  conv => lhs; unfold clever_067_pluck.first_index_of
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov : i.toNat + 1 < 2 ^ 64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    omega
  have h_idx := slice_index_eq l i hi
  have h_beq_false : ((l.val[i.toNat]'hi) == target) = false := by
    rw [beq_eq_false_iff_ne]; exact h
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.eq, h_beq_false,
             h_add_eq]

/-! ## USize64 → UInt64 cast: `toNat` is preserved. -/

private theorem usize_toUInt64_toNat (i : usize) : (USize64.toUInt64 i).toNat = i.toNat := by
  have h_lt : i.toNat < 2 ^ 64 := by
    have h_size_lt : i.toNat < USize64.size := i.toNat_lt
    rw [usize_size_eq] at h_size_lt; exact h_size_lt
  show (i.toNat.toUInt64).toNat = i.toNat
  -- Nat.toUInt64 n = UInt64.ofNat n
  -- (UInt64.ofNat n).toNat = n % 2^64 = n
  change (UInt64.ofNat i.toNat).toNat = i.toNat
  simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt h_lt]

/-! ## Master correctness lemma for `first_index_of`.

When there exists `j ∈ [i, size)` with `l[j] = target`, the result is a
u64 whose `toNat` is the smallest such `j`. Otherwise the result is `0`. -/

private theorem first_index_of_correct
    (l : RustSlice i64) (target : i64) :
    ∀ (m : Nat) (i : usize),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      ∃ r : u64,
        clever_067_pluck.first_index_of l target i = RustM.ok r ∧
        ((∃ (j : Nat) (hj : j < l.val.size), i.toNat ≤ j ∧ (l.val[j]'hj) = target) →
          r.toNat < l.val.size ∧
          i.toNat ≤ r.toNat ∧
          (∀ (hr : r.toNat < l.val.size), (l.val[r.toNat]'hr) = target) ∧
          ∀ (j : Nat) (hj : j < l.val.size),
            i.toNat ≤ j → j < r.toNat → (l.val[j]'hj) ≠ target) := by
  intro m
  induction m with
  | zero =>
    intro i hm hi_le
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨0, first_index_of_oob l target i hi_ge, ?_⟩
    rintro ⟨j, hj, h_ij, _⟩
    rw [hi_eq] at h_ij; omega
  | succ m ih =>
    intro i hm hi_le
    by_cases hi_ge : l.val.size ≤ i.toNat
    · -- OOB
      have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨0, first_index_of_oob l target i hi_ge, ?_⟩
      rintro ⟨j, hj, h_ij, _⟩
      rw [hi_eq] at h_ij; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov : i.toNat + 1 < 2 ^ 64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      by_cases h_eq : (l.val[i.toNat]'hi_lt) = target
      · -- FOUND: r = USize64.toUInt64 i
        have h_step := first_index_of_found l target i hi_lt h_eq
        have h_toNat : (USize64.toUInt64 i).toNat = i.toNat := usize_toUInt64_toNat i
        refine ⟨USize64.toUInt64 i, h_step, ?_⟩
        intro _
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [h_toNat]; exact hi_lt
        · rw [h_toNat]; exact Nat.le_refl _
        · intro hr
          -- (l.val[(USize64.toUInt64 i).toNat]'hr) = target
          have h_re : (l.val[(USize64.toUInt64 i).toNat]'hr)
                       = (l.val[i.toNat]'hi_lt) := by
            apply getElem_congr_idx
            exact h_toNat
          rw [h_re]; exact h_eq
        · intro j hj h_ij h_jlt
          rw [h_toNat] at h_jlt; omega
      · -- RECURSE
        have h_step := first_index_of_recurse l target i hi_lt h_eq
        obtain ⟨r, hres, h_witness⟩ := ih (i + 1) h_m_le h_i1_le
        refine ⟨r, ?_, ?_⟩
        · rw [h_step]; exact hres
        · rintro ⟨j, hj, h_ij, h_jeq⟩
          have h_in_suffix : ∃ (j : Nat) (hj : j < l.val.size),
                              (i + 1).toNat ≤ j ∧ (l.val[j]'hj) = target := by
            refine ⟨j, hj, ?_, h_jeq⟩
            rw [h_i1]
            by_cases h_jeqi : j = i.toNat
            · subst h_jeqi
              exact absurd h_jeq h_eq
            · omega
          obtain ⟨h_r_size, h_r_ge, h_r_eq, h_r_first⟩ := h_witness h_in_suffix
          refine ⟨h_r_size, ?_, h_r_eq, ?_⟩
          · rw [h_i1] at h_r_ge; omega
          · intro j' hj' h_ij' h_jlt
            by_cases h_jeqi : j' = i.toNat
            · subst h_jeqi
              exact h_eq
            · have h_jge1 : (i + 1).toNat ≤ j' := by rw [h_i1]; omega
              exact h_r_first j' hj' h_jge1 h_jlt

/-! ## Pluck body reduction. -/

/-- Empty `Vec i64` (for the "not found" branch). -/
private def emptyVec : alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨(List.nil : List i64).toArray, by decide⟩

/-- The 2-element output `Vec` (for the "found" branch). -/
private def pairVec (val idx : i64) : alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨#[val, idx], by
    show (2 : Nat) < USize64.size
    decide⟩

private theorem emptyVec_size : emptyVec.val.size = 0 := rfl
private theorem pairVec_size (val idx : i64) : (pairVec val idx).val.size = 2 := rfl
private theorem pairVec_getElem_0 (val idx : i64) (h : 0 < (pairVec val idx).val.size) :
    (pairVec val idx).val[0]'h = val := rfl
private theorem pairVec_getElem_1 (val idx : i64) (h : 1 < (pairVec val idx).val.size) :
    (pairVec val idx).val[1]'h = idx := rfl

/-- Reduce `pluck l` given the result of `smallest_even_at l 0 0 false`.
    Splits on the `found` flag. -/
private theorem pluck_eval_not_found
    (l : RustSlice i64) (val : i64)
    (h_smallest : clever_067_pluck.smallest_even_at l (0 : usize) (0 : i64) false
                    = RustM.ok (rust_primitives.hax.Tuple2.mk val false)) :
    clever_067_pluck.pluck l = RustM.ok emptyVec := by
  unfold clever_067_pluck.pluck
  rw [h_smallest]
  simp only [RustM_ok_bind, rust_primitives.hax.logical_op.not, pure_bind, ↓reduceIte]
  rfl

private theorem pluck_eval_found
    (l : RustSlice i64) (val : i64) (r : u64)
    (h_smallest : clever_067_pluck.smallest_even_at l (0 : usize) (0 : i64) false
                    = RustM.ok (rust_primitives.hax.Tuple2.mk val true))
    (h_first : clever_067_pluck.first_index_of l val (0 : usize) = RustM.ok r) :
    clever_067_pluck.pluck l = RustM.ok (pairVec val (UInt64.toInt64 r)) := by
  unfold clever_067_pluck.pluck
  rw [h_smallest]
  simp only [RustM_ok_bind, rust_primitives.hax.logical_op.not, pure_bind, ↓reduceIte,
             Bool.not_true, Bool.false_eq_true]
  rw [h_first]
  simp only [RustM_ok_bind]
  -- cast_op: u64 → i64 = pure (UInt64.toInt64 r)
  let idx : i64 := UInt64.toInt64 r
  let init_vec : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by decide⟩
  have h_cast : (rust_primitives.hax.cast_op r : RustM i64) = RustM.ok idx := rfl
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk
                  : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok init_vec := rfl
  rw [h_cast, h_new]
  simp only [RustM_ok_bind]
  -- Now reduce the unsize + extend_from_slice for the 2-element chunk.
  -- Replace the chunk with its concrete form by using `change`.
  change ((rust_primitives.unsize (RustArray.ofVec (n := (2 : usize)) #v[val, idx])
            : RustM (rust_primitives.sequence.Seq i64)) >>= fun s =>
              alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global init_vec s
          >>= fun r => pure r)
        = RustM.ok (pairVec val idx)
  have h_unsize : (rust_primitives.unsize (RustArray.ofVec (n := (2 : usize)) #v[val, idx])
                    : RustM (rust_primitives.sequence.Seq i64))
                = RustM.ok ⟨#[val, idx], by show (2 : Nat) < USize64.size; decide⟩ := rfl
  rw [h_unsize]
  simp only [RustM_ok_bind]
  have h_app_size : init_vec.val.size + (#[val, idx] : Array i64).size < USize64.size := by
    show 0 + 2 < USize64.size
    decide
  have h_ext :
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global init_vec
            ⟨#[val, idx], by show (2 : Nat) < USize64.size; decide⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (pairVec val idx) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl
  rw [h_ext]
  rfl

/-! ## Cast helpers for the index. -/

private theorem u64_toInt64_toInt_of_lt (r : u64) (h : r.toNat < 2^63) :
    (UInt64.toInt64 r).toInt = (r.toNat : Int) := by
  -- (UInt64.toInt64 r).toInt = (Int64.toBitVec (UInt64.toInt64 r)).toInt
  -- = (UInt64.toInt64 r).toUInt64.toBitVec.toInt
  -- = r.toBitVec.toInt (since UInt64.toInt64_toUInt64 is rfl)
  -- ... actually use toBitVec_toInt64 directly:
  show ((UInt64.toInt64 r).toBitVec).toInt = (r.toNat : Int)
  rw [UInt64.toBitVec_toInt64]
  -- Goal: r.toBitVec.toInt = r.toNat
  -- Use toInt_eq_toNat_of_lt: needs 2 * r.toBitVec.toNat < 2^64.
  have h_lt : 2 * r.toBitVec.toNat < 2^64 := by
    have : r.toBitVec.toNat = r.toNat := rfl
    rw [this]; omega
  rw [BitVec.toInt_eq_toNat_of_lt h_lt]
  rfl

/-! ## Master pluck theorem.

Gathers all relevant facts about `pluck l`:
* totality (returns `RustM.ok v`),
* exact form of `v` (empty when no even; `[val, UInt64.toInt64 r]` when found),
* membership / minimality / first-occurrence properties of `val` and `r`. -/

private theorem pluck_master (l : RustSlice i64) :
    (¬ hasEven l →
      clever_067_pluck.pluck l = RustM.ok emptyVec) ∧
    (hasEven l →
      ∃ (val : i64) (r : u64),
        clever_067_pluck.pluck l = RustM.ok (pairVec val (UInt64.toInt64 r)) ∧
        isEven val ∧
        (∀ (i : Nat) (hi : i < l.val.size),
            isEven (l.val[i]'hi) → val.toInt ≤ (l.val[i]'hi).toInt) ∧
        r.toNat < l.val.size ∧
        (∀ (hrn : r.toNat < l.val.size), (l.val[r.toNat]'hrn) = val) ∧
        (∀ (j : Nat) (hj : j < l.val.size), j < r.toNat → (l.val[j]'hj) ≠ val)) := by
  -- First, invoke smallest_even_at_correct.
  obtain ⟨rv, rf, h_se, h_live, h_mem, h_min⟩ :=
    smallest_even_at_correct l l.val.size (0 : usize) (0 : i64) false
      (by show l.val.size - 0 ≤ l.val.size; omega)
      (by show 0 ≤ l.val.size; omega)
  refine ⟨?_, ?_⟩
  · -- Empty branch.
    intro h_no_even
    -- Show rf = false (since neither `false` nor `∃ even` holds).
    have h_rf_false : rf = false := by
      cases hrf : rf
      · rfl
      · exfalso
        have h_disj := h_live.mp hrf
        rcases h_disj with hfalse | ⟨j, hj, h_jge, h_jeven⟩
        · cases hfalse
        · apply h_no_even
          exact ⟨j, hj, h_jeven⟩
    rw [h_rf_false] at h_se
    exact pluck_eval_not_found l rv h_se
  · -- Found branch.
    intro h_has_even
    obtain ⟨j₀, hj₀, h_j₀even⟩ := h_has_even
    -- Show rf = true.
    have h_rf_true : rf = true := by
      apply h_live.mpr
      right
      exact ⟨j₀, hj₀, by show 0 ≤ j₀; omega, h_j₀even⟩
    rw [h_rf_true] at h_se
    -- From membership: rv = best (= 0, but found = false) OR rv = l[j] for some j ≥ 0 even.
    have h_membership := h_mem h_rf_true
    rcases h_membership with ⟨hf, _⟩ | ⟨j_v, hj_v, h_j_v_ge, h_rv_eq, h_rv_even⟩
    · -- found = true contradicts the initial found = false.
      cases hf
    · -- rv is at l[j_v] with j_v ≥ 0 (trivially) and isEven l[j_v].
      have h_rv_isEven : isEven rv := by
        rw [h_rv_eq]; exact h_rv_even
      -- Minimality: rv ≤ every even l[i] (for i ≥ 0, trivially every i).
      have h_min_use := h_min h_rf_true
      have h_rv_min : ∀ (i : Nat) (hi : i < l.val.size),
                       isEven (l.val[i]'hi) → rv.toInt ≤ (l.val[i]'hi).toInt := by
        intro i hi h_ieven
        exact h_min_use.2 i hi (by show 0 ≤ i; omega) h_ieven
      -- Now run first_index_of with target = rv.
      obtain ⟨r, h_fi, h_fi_witness⟩ :=
        first_index_of_correct l rv l.val.size (0 : usize)
          (by show l.val.size - 0 ≤ l.val.size; omega)
          (by show 0 ≤ l.val.size; omega)
      have h_target_exists :
          ∃ (j : Nat) (hj : j < l.val.size),
            (0 : usize).toNat ≤ j ∧ (l.val[j]'hj) = rv := by
        refine ⟨j_v, hj_v, ?_, ?_⟩
        · show 0 ≤ j_v; omega
        · exact h_rv_eq.symm
      obtain ⟨h_r_size, _h_r_ge, h_r_eq, h_r_first⟩ := h_fi_witness h_target_exists
      refine ⟨rv, r, ?_, h_rv_isEven, h_rv_min, h_r_size, ?_, ?_⟩
      · exact pluck_eval_found l rv r h_se h_fi
      · intro hrn
        exact h_r_eq hrn
      · intro j hj h_jlt
        exact h_r_first j hj (by show 0 ≤ j; omega) h_jlt

/-! ## Obligations.

The `pluck` function always succeeds (no failing operations on the path:
all `usize +? 1` increments respect the slice bound, the casts
`usize → u64` and `u64 → i64` are total wrapping conversions, and the
`extend_from_slice` of a fixed 2-element chunk onto a freshly-allocated
empty `Vec` doesn't overflow). The contract clauses below describe the
*postconditions* on the returned vector. -/

/-- Boundary: when `s` contains no even element (e.g. empty input or all-odd
    input), `pluck` returns an empty vector.
    Covers Rust tests `empty_returns_empty` and `all_odd_returns_empty`. -/
theorem pluck_no_even_returns_empty
    (s : RustSlice i64)
    (hno : ¬ hasEven s) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_067_pluck.pluck s = RustM.ok v ∧ v.val.size = 0 := by
  obtain ⟨h_empty, _⟩ := pluck_master s
  exact ⟨emptyVec, h_empty hno, emptyVec_size⟩

/-- Common helper: from `pluck s = RustM.ok v` and the master theorem,
    derive an exhaustive characterisation of `v`. -/
private theorem pluck_result_form
    (s : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0) :
    hasEven s ∧
    ∃ (val : i64) (r : u64),
      v = pairVec val (UInt64.toInt64 r) ∧
      isEven val ∧
      (∀ (i : Nat) (hi : i < s.val.size),
          isEven (s.val[i]'hi) → val.toInt ≤ (s.val[i]'hi).toInt) ∧
      r.toNat < s.val.size ∧
      (∀ (hrn : r.toNat < s.val.size), (s.val[r.toNat]'hrn) = val) ∧
      (∀ (j : Nat) (hj : j < s.val.size), j < r.toNat → (s.val[j]'hj) ≠ val) := by
  obtain ⟨h_empty, h_found⟩ := pluck_master s
  by_cases h_has : hasEven s
  · obtain ⟨val, r, h_pluck, h1', h2', h3', h4', h5'⟩ := h_found h_has
    rw [h_pluck] at hres
    have h_v : v = pairVec val (UInt64.toInt64 r) := by
      injection hres with h1
      injection h1 with h2
      exact h2.symm
    refine ⟨h_has, val, r, h_v, h1', h2', h3', h4', h5'⟩
  · exfalso
    have h_empty_v := h_empty h_has
    rw [h_empty_v] at hres
    have h_v : v = emptyVec := by
      injection hres with h1
      injection h1 with h2
      exact h2.symm
    rw [h_v] at hne
    exact hne emptyVec_size

/-- Existence characterization: the result is non-empty exactly when `s`
    contains an even element. Covers Rust proptest `nonempty_iff_has_even`. -/
theorem pluck_nonempty_iff_has_even
    (s : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_067_pluck.pluck s = RustM.ok v ∧
      (v.val.size ≠ 0 ↔ hasEven s) := by
  obtain ⟨h_empty, h_found⟩ := pluck_master s
  by_cases h_has : hasEven s
  · obtain ⟨val, r, h_pluck, _, _, _, _, _⟩ := h_found h_has
    refine ⟨pairVec val (UInt64.toInt64 r), h_pluck, ?_⟩
    constructor
    · intro _; exact h_has
    · intro _; rw [pairVec_size]; decide
  · refine ⟨emptyVec, h_empty h_has, ?_⟩
    constructor
    · intro h_ne; exact absurd emptyVec_size h_ne
    · intro h; exact absurd h h_has

/-- Output-shape clause (size): a non-empty result has size exactly `2`
    (the `[value, index]` pair). Covers the first sub-clause of Rust
    proptest `output_shape`. -/
theorem pluck_nonempty_size_two
    (s : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0) :
    v.val.size = 2 := by
  obtain ⟨_, val, r, h_v, _, _, _, _, _⟩ := pluck_result_form s v hres hne
  rw [h_v]; rfl

/-- Output-shape clause (index non-negative): when the result is non-empty,
    the index slot is non-negative. This requires the size of `s` to fit in
    the positive `i64` range so the `u64 → i64` cast doesn't wrap.
    Covers the `r[1] >= 0` sub-clause of `output_shape`. -/
theorem pluck_nonempty_index_nonneg
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h1 : 1 < v.val.size) :
    0 ≤ (v.val[1]'h1).toInt := by
  obtain ⟨_, val, r, h_v, _, _, h_r_size, _, _⟩ := pluck_result_form s v hres hne
  have h_r_lt : r.toNat < 2 ^ 63 := Nat.lt_of_lt_of_le h_r_size hbnd
  subst h_v
  show 0 ≤ (UInt64.toInt64 r).toInt
  rw [u64_toInt64_toInt_of_lt r h_r_lt]
  omega

/-- Output-shape clause (index in bounds): when the result is non-empty,
    the index slot, viewed as an `Int`, is a valid position into `s`.
    Covers the `(r[1] as usize) < l.len()` sub-clause of `output_shape`. -/
theorem pluck_nonempty_index_in_bounds
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h1 : 1 < v.val.size) :
    (v.val[1]'h1).toInt < (s.val.size : Int) := by
  obtain ⟨_, val, r, h_v, _, _, h_r_size, _, _⟩ := pluck_result_form s v hres hne
  have h_r_lt : r.toNat < 2 ^ 63 := Nat.lt_of_lt_of_le h_r_size hbnd
  subst h_v
  show (UInt64.toInt64 r).toInt < (s.val.size : Int)
  rw [u64_toInt64_toInt_of_lt r h_r_lt]
  exact_mod_cast h_r_size

/-- Value-clause (parity): when the result is non-empty, the value slot
    `v[0]` is even. Covers the `v % 2 == 0` sub-clause of Rust proptest
    `value_is_minimum_even`. -/
theorem pluck_nonempty_value_is_even
    (s : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) :
    isEven (v.val[0]'h0) := by
  obtain ⟨_, val, r, h_v, h_val_even, _, _, _, _⟩ := pluck_result_form s v hres hne
  subst h_v
  exact h_val_even

/-- Value-clause (minimality): when the result is non-empty, the value slot
    `v[0]` is at most every even element of `s`. Covers the `v ≤ x` sub-clause
    of Rust proptest `value_is_minimum_even`. -/
theorem pluck_nonempty_value_is_minimum_even
    (s : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) :
    ∀ (i : Nat) (hi : i < s.val.size),
      isEven (s.val[i]'hi) → (v.val[0]'h0).toInt ≤ (s.val[i]'hi).toInt := by
  obtain ⟨_, val, r, h_v, _, h_val_min, _, _, _⟩ := pluck_result_form s v hres hne
  subst h_v
  intro i hi h_ieven
  exact h_val_min i hi h_ieven

/-- Index-clause (points to value): when the result is non-empty, the index
    slot identifies a position in `s` whose element equals the value slot.
    Covers the `l[i] == v` sub-clause of Rust proptest `index_is_first_occurrence`. -/
theorem pluck_nonempty_index_points_to_value
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) (h1 : 1 < v.val.size)
    (hbd : (v.val[1]'h1).toInt.toNat < s.val.size) :
    (s.val[(v.val[1]'h1).toInt.toNat]'hbd) = (v.val[0]'h0) := by
  obtain ⟨_, val, r, h_v, _, _, h_r_size, h_r_eq, _⟩ := pluck_result_form s v hres hne
  have h_r_lt : r.toNat < 2 ^ 63 := Nat.lt_of_lt_of_le h_r_size hbnd
  subst h_v
  show (s.val[((UInt64.toInt64 r).toInt).toNat]'hbd) = val
  have h_idx_eq : ((UInt64.toInt64 r).toInt).toNat = r.toNat := by
    rw [u64_toInt64_toInt_of_lt r h_r_lt]
    exact Int.toNat_natCast r.toNat
  have h_re : (s.val[((UInt64.toInt64 r).toInt).toNat]'hbd) = (s.val[r.toNat]'h_r_size) :=
    getElem_congr_idx h_idx_eq
  rw [h_re, h_r_eq h_r_size]

/-- Index-clause (first occurrence): when the result is non-empty, no
    position strictly earlier than the index slot holds the value slot.
    Covers the `l[j] != v` sub-clause (tie-break on smallest index) of
    Rust proptest `index_is_first_occurrence`. -/
theorem pluck_nonempty_index_is_first_occurrence
    (s : RustSlice i64)
    (hbnd : s.val.size ≤ 2 ^ 63)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_067_pluck.pluck s = RustM.ok v)
    (hne : v.val.size ≠ 0)
    (h0 : 0 < v.val.size) (h1 : 1 < v.val.size) :
    ∀ (j : Nat) (hj : j < s.val.size),
      (j : Int) < (v.val[1]'h1).toInt → (s.val[j]'hj) ≠ (v.val[0]'h0) := by
  obtain ⟨_, val, r, h_v, _, _, h_r_size, _, h_r_first⟩ := pluck_result_form s v hres hne
  have h_r_lt : r.toNat < 2 ^ 63 := Nat.lt_of_lt_of_le h_r_size hbnd
  subst h_v
  intro j hj h_jlt_int
  show (s.val[j]'hj) ≠ val
  -- Reduce (pairVec val (UInt64.toInt64 r)).val[1] to UInt64.toInt64 r.
  have h_reduce : (pairVec val (UInt64.toInt64 r)).val[1]'h1 = UInt64.toInt64 r := rfl
  rw [h_reduce] at h_jlt_int
  rw [u64_toInt64_toInt_of_lt r h_r_lt] at h_jlt_int
  have h_jlt_nat : j < r.toNat := by exact_mod_cast h_jlt_int
  exact h_r_first j hj h_jlt_nat

end Clever_067_pluckObligations
