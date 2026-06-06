-- Companion obligations file for the `clever_160_generate_integers` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_160_generate_integers

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_160_generate_integersObligations

/-! ## Numeric helper lemmas -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat  : (1 : u64).toNat = 1 := rfl
private theorem u64_two_toNat  : (2 : u64).toNat = 2 := rfl
private theorem u64_eight_toNat : (8 : u64).toNat = 8 := rfl

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide
private theorem usize_size_eq_2_64 : USize64.size = 2 ^ 64 := by decide

/-- `(d + 1).toNat = d.toNat + 1` when the sum fits in u64. -/
private theorem u64_succ_toNat (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h), u64_one_toNat]

/-- `d +? 1 = pure (d + 1)` when `d.toNat + 1` fits in u64. -/
private theorem u64_add_one_pure (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d +? (1 : u64) : RustM u64) = RustM.ok (d + 1) := by
  show (rust_primitives.ops.arith.Add.add d 1 : RustM u64) = RustM.ok (d + 1)
  show (if BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d + 1)) = _
  have h_no : ¬ UInt64.addOverflow d 1 := by
    rw [UInt64.addOverflow_iff, u64_one_toNat]; omega
  have h_bv : BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- `2 : u64` is not zero. -/
private theorem u64_two_ne_zero : (2 : u64) ≠ 0 := by decide

/-- `n %? 2 = pure (n % 2)`. -/
private theorem u64_mod_two_pure (n : u64) :
    (n %? (2 : u64) : RustM u64) = RustM.ok (n % 2) := by
  show (rust_primitives.ops.arith.Rem.rem n 2 : RustM u64) = RustM.ok (n % 2)
  show (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64) else pure (n % 2)) = _
  rw [if_neg u64_two_ne_zero]; rfl

private theorem u64_mod_two_toNat (n : u64) : (n % 2).toNat = n.toNat % 2 := by
  rw [UInt64.toNat_mod, u64_two_toNat]

/-- `(0 : u64) = (0 : u64).toNat`. -/
private theorem u64_eq_zero_iff (n : u64) : n = (0 : u64) ↔ n.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply UInt64.toNat_inj.mp
    rw [h]; rfl

/-! ## Push helper (extend_from_slice of a 1-element chunk) -/

private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

@[simp]
private theorem push_one_size (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

private theorem push_one_val (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val = acc.val ++ #[x] := rfl

/-! ## One-step reductions for `build_at` -/

/-- Exit branch: `k > hi ∨ k > 8` → returns `acc`. -/
private theorem build_at_oob
    (lo hi k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_exit : hi.toNat < k.toNat ∨ 8 < k.toNat) :
    clever_160_generate_integers.build_at lo hi k acc = RustM.ok acc := by
  conv => lhs; unfold clever_160_generate_integers.build_at
  have h_gt_hi : ((k >? hi) : RustM Bool) = pure (decide (k > hi)) := rfl
  have h_gt_8  : ((k >? (8 : u64)) : RustM Bool) = pure (decide (k > 8)) := rfl
  rw [h_gt_hi, h_gt_8]
  simp only [pure_bind]
  rw [show ((decide (k > hi) : Bool) ||? (decide (k > 8) : Bool)) =
        pure (decide (k > hi) || decide (k > 8)) from rfl]
  simp only [pure_bind]
  have h_cond_true : (decide (k > hi) || decide (k > 8)) = true := by
    rw [Bool.or_eq_true]
    rcases h_exit with h | h
    · left
      exact decide_eq_true (UInt64.lt_iff_toNat_lt.mpr h)
    · right
      apply decide_eq_true
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [u64_eight_toNat]; exact h
  rw [if_pos h_cond_true]
  rfl

/-- Step (push): in non-exit branch with `k ≥ lo ∧ k % 2 = 0`, push `k` and recurse. -/
private theorem build_at_step_push
    (lo hi k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_k_le_hi : k.toNat ≤ hi.toNat)
    (h_k_le_8 : k.toNat ≤ 8)
    (h_k_ge_lo : lo.toNat ≤ k.toNat)
    (h_k_even : k.toNat % 2 = 0)
    (h_acc : acc.val.size + 1 < USize64.size)
    (h_no_ov : k.toNat + 1 < 2 ^ 64) :
    clever_160_generate_integers.build_at lo hi k acc =
      clever_160_generate_integers.build_at lo hi (k + 1) (push_one acc k h_acc) := by
  conv => lhs; unfold clever_160_generate_integers.build_at
  have h_gt_hi : ((k >? hi) : RustM Bool) = pure (decide (k > hi)) := rfl
  have h_gt_8  : ((k >? (8 : u64)) : RustM Bool) = pure (decide (k > 8)) := rfl
  have h_ge_lo : ((k >=? lo) : RustM Bool) = pure (decide (k ≥ lo)) := rfl
  have h_mod   : ((k %? (2 : u64)) : RustM u64) = RustM.ok (k % 2) := u64_mod_two_pure k
  have h_eq_zero : (((k % 2) ==? (0 : u64)) : RustM Bool) =
      pure (decide ((k % 2) = (0 : u64))) := rfl
  -- Exit cond is false.
  have h_not_gt_hi : ¬ k > hi := by
    intro h; have := UInt64.lt_iff_toNat_lt.mp h; omega
  have h_not_gt_8 : ¬ k > (8 : u64) := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    rw [u64_eight_toNat] at this; omega
  have h_cond_exit : (decide (k > hi) || decide (k > (8 : u64))) = false := by
    rw [Bool.or_eq_false_iff]
    exact ⟨decide_eq_false h_not_gt_hi, decide_eq_false h_not_gt_8⟩
  -- Inner cond is true.
  have h_ge_lo_true : k ≥ lo := UInt64.le_iff_toNat_le.mpr h_k_ge_lo
  have h_mod_eq : (k % 2 : u64) = (0 : u64) := by
    apply UInt64.toNat_inj.mp
    rw [u64_mod_two_toNat, u64_zero_toNat]; exact h_k_even
  have h_inner : (decide (k ≥ lo) && decide ((k % 2) = (0 : u64))) = true := by
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true h_ge_lo_true, decide_eq_true h_mod_eq⟩
  have h_add : (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) := u64_add_one_pure k h_no_ov
  -- Reduce the unsize and extend_from_slice.
  have h_unsize :
      (rust_primitives.unsize (RustArray.ofVec #v[k] : RustArray u64 1)
        : RustM (rust_primitives.sequence.Seq u64))
        = RustM.ok ⟨#[k], one_lt_usize_size⟩ := rfl
  have h_app_size : acc.val.size + (#[k] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
          ⟨#[k], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc k h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl
  rw [h_gt_hi, h_gt_8]
  simp only [pure_bind]
  rw [show ((decide (k > hi) : Bool) ||? (decide (k > (8 : u64)) : Bool)) =
        pure (decide (k > hi) || decide (k > (8 : u64))) from rfl]
  simp only [pure_bind]
  rw [if_neg (by rw [h_cond_exit]; exact Bool.false_ne_true)]
  rw [h_ge_lo, h_mod]
  simp only [pure_bind, RustM_ok_bind]
  rw [h_eq_zero]
  simp only [pure_bind]
  rw [show ((decide (k ≥ lo) : Bool) &&? (decide ((k % 2) = (0 : u64)) : Bool)) =
        pure (decide (k ≥ lo) && decide ((k % 2) = (0 : u64))) from rfl]
  simp only [pure_bind]
  rw [if_pos h_inner]
  rw [h_unsize]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  rfl

/-- Step (skip): in non-exit branch with `¬(k ≥ lo ∧ k % 2 = 0)`, just recurse. -/
private theorem build_at_step_skip
    (lo hi k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_k_le_hi : k.toNat ≤ hi.toNat)
    (h_k_le_8 : k.toNat ≤ 8)
    (h_skip : k.toNat < lo.toNat ∨ k.toNat % 2 ≠ 0)
    (h_no_ov : k.toNat + 1 < 2 ^ 64) :
    clever_160_generate_integers.build_at lo hi k acc =
      clever_160_generate_integers.build_at lo hi (k + 1) acc := by
  conv => lhs; unfold clever_160_generate_integers.build_at
  have h_gt_hi : ((k >? hi) : RustM Bool) = pure (decide (k > hi)) := rfl
  have h_gt_8  : ((k >? (8 : u64)) : RustM Bool) = pure (decide (k > 8)) := rfl
  have h_ge_lo : ((k >=? lo) : RustM Bool) = pure (decide (k ≥ lo)) := rfl
  have h_mod   : ((k %? (2 : u64)) : RustM u64) = RustM.ok (k % 2) := u64_mod_two_pure k
  have h_eq_zero : (((k % 2) ==? (0 : u64)) : RustM Bool) =
      pure (decide ((k % 2) = (0 : u64))) := rfl
  -- Exit cond is false.
  have h_not_gt_hi : ¬ k > hi := by
    intro h; have := UInt64.lt_iff_toNat_lt.mp h; omega
  have h_not_gt_8 : ¬ k > (8 : u64) := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    rw [u64_eight_toNat] at this; omega
  have h_cond_exit : (decide (k > hi) || decide (k > (8 : u64))) = false := by
    rw [Bool.or_eq_false_iff]
    exact ⟨decide_eq_false h_not_gt_hi, decide_eq_false h_not_gt_8⟩
  -- Inner cond is false (skip).
  have h_inner : (decide (k ≥ lo) && decide ((k % 2) = (0 : u64))) = false := by
    rcases h_skip with h | h
    · have h_not_ge : ¬ k ≥ lo := by
        intro h_ge
        have := UInt64.le_iff_toNat_le.mp h_ge
        omega
      rw [Bool.and_eq_false_iff]
      exact Or.inl (decide_eq_false h_not_ge)
    · have h_ne : (k % 2 : u64) ≠ (0 : u64) := by
        intro h_eq
        have h_toNat : (k % 2 : u64).toNat = 0 := by rw [h_eq]; rfl
        rw [u64_mod_two_toNat] at h_toNat
        exact h h_toNat
      rw [Bool.and_eq_false_iff]
      exact Or.inr (decide_eq_false h_ne)
  have h_add : (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) := u64_add_one_pure k h_no_ov
  rw [h_gt_hi, h_gt_8]
  simp only [pure_bind]
  rw [show ((decide (k > hi) : Bool) ||? (decide (k > (8 : u64)) : Bool)) =
        pure (decide (k > hi) || decide (k > (8 : u64))) from rfl]
  simp only [pure_bind]
  rw [if_neg (by rw [h_cond_exit]; exact Bool.false_ne_true)]
  rw [h_ge_lo, h_mod]
  simp only [pure_bind, RustM_ok_bind]
  rw [h_eq_zero]
  simp only [pure_bind]
  rw [show ((decide (k ≥ lo) : Bool) &&? (decide ((k % 2) = (0 : u64)) : Bool)) =
        pure (decide (k ≥ lo) && decide ((k % 2) = (0 : u64))) from rfl]
  simp only [pure_bind]
  rw [if_neg (by rw [h_inner]; exact Bool.false_ne_true)]
  rw [h_add]
  rfl

/-! ## Strong-induction lemma over `build_at`.

Carries the invariant that the returned vector equals `acc ++ rest`, where
`rest` lists exactly the even `u64`s `y` with `max(k, lo) ≤ y.toNat ≤ min(hi, 8)`,
in strictly-ascending order. -/

private theorem build_at_correct (lo hi : u64) :
    ∀ (m : Nat) (k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (v : alloc.vec.Vec u64 alloc.alloc.Global),
      9 - k.toNat ≤ m →
      k.toNat ≤ 10 →
      acc.val.size + (9 - k.toNat) < USize64.size →
      clever_160_generate_integers.build_at lo hi k acc = RustM.ok v →
      ∃ rest : List u64,
        v.val.toList = acc.val.toList ++ rest ∧
        (∀ y ∈ rest, lo.toNat ≤ y.toNat ∧ y.toNat ≤ hi.toNat ∧
          y.toNat ≤ 8 ∧ y.toNat % 2 = 0 ∧ k.toNat ≤ y.toNat) ∧
        rest.Pairwise (fun a b => a.toNat < b.toNat) ∧
        (∀ x : Nat, k.toNat ≤ x → lo.toNat ≤ x → x ≤ hi.toNat → x ≤ 8 →
            x % 2 = 0 → ∃ y ∈ rest, y.toNat = x) := by
  intro m
  induction m with
  | zero =>
    intro k acc v hm hk_le h_room hres
    -- 9 - k.toNat ≤ 0 → k.toNat ≥ 9 → exit branch.
    have h_k_ge_9 : 9 ≤ k.toNat := by omega
    have h_exit : hi.toNat < k.toNat ∨ 8 < k.toNat := Or.inr (by omega)
    rw [build_at_oob lo hi k acc h_exit] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨[], ?_, ?_, ?_, ?_⟩
    · simp
    · intro y hy; simp at hy
    · exact List.Pairwise.nil
    · intro x hx_ge_k _ _ hx_le_8 _
      exfalso; omega
  | succ m ih =>
    intro k acc v hm hk_le h_room hres
    by_cases h_k_gt_8 : 8 < k.toNat
    · -- Exit via k > 8.
      have h_exit : hi.toNat < k.toNat ∨ 8 < k.toNat := Or.inr h_k_gt_8
      rw [build_at_oob lo hi k acc h_exit] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · simp
      · intro y hy; simp at hy
      · exact List.Pairwise.nil
      · intro x hx_ge_k _ _ hx_le_8 _
        exfalso; omega
    · by_cases h_k_gt_hi : hi.toNat < k.toNat
      · -- Exit via k > hi.
        have h_exit : hi.toNat < k.toNat ∨ 8 < k.toNat := Or.inl h_k_gt_hi
        rw [build_at_oob lo hi k acc h_exit] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨[], ?_, ?_, ?_, ?_⟩
        · simp
        · intro y hy; simp at hy
        · exact List.Pairwise.nil
        · intro x _ _ hx_le_hi hx_le_8 _
          have : x ≤ hi.toNat := hx_le_hi
          exfalso; omega
      · -- Non-exit branch.
        have h_k_le_hi : k.toNat ≤ hi.toNat := Nat.le_of_not_lt h_k_gt_hi
        have h_k_le_8 : k.toNat ≤ 8 := Nat.le_of_not_lt h_k_gt_8
        have h_no_ov : k.toNat + 1 < 2 ^ 64 := by omega
        have h_k1_toNat : (k + 1).toNat = k.toNat + 1 := u64_succ_toNat k h_no_ov
        have h_k1_le : (k + 1).toNat ≤ 10 := by rw [h_k1_toNat]; omega
        have h_meas : 9 - (k + 1).toNat ≤ m := by rw [h_k1_toNat]; omega
        have h_room_skip : acc.val.size + (9 - (k + 1).toNat) < USize64.size := by
          rw [h_k1_toNat]; omega
        have h_acc_succ : acc.val.size + 1 < USize64.size := by
          have h_diff_pos : 1 ≤ 9 - k.toNat := by omega
          omega
        by_cases h_dec_lo : k.toNat < lo.toNat
        · -- Skip via lo.
          rw [build_at_step_skip lo hi k acc h_k_le_hi h_k_le_8
                (Or.inl h_dec_lo) h_no_ov] at hres
          obtain ⟨rest, hval, hbnd, hpw, hcompl⟩ :=
            ih (k + 1) acc v h_meas h_k1_le h_room_skip hres
          refine ⟨rest, hval, ?_, hpw, ?_⟩
          · intro y hy
            obtain ⟨h1, h2, h3, h4, h5⟩ := hbnd y hy
            refine ⟨h1, h2, h3, h4, ?_⟩
            rw [h_k1_toNat] at h5; omega
          · intro x h_ge_k h_ge_lo h_le_hi h_le_8 h_even
            by_cases h_x_eq_k : x = k.toNat
            · exfalso
              rw [h_x_eq_k] at h_ge_lo
              omega
            · have h_ge_succ : (k + 1).toNat ≤ x := by
                rw [h_k1_toNat]; omega
              exact hcompl x h_ge_succ h_ge_lo h_le_hi h_le_8 h_even
        · by_cases h_dec_even : k.toNat % 2 = 0
          · -- Push branch.
            rw [build_at_step_push lo hi k acc h_k_le_hi h_k_le_8
                  (Nat.le_of_not_lt h_dec_lo) h_dec_even h_acc_succ h_no_ov] at hres
            have h_push_size : (push_one acc k h_acc_succ).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[k]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_room_push :
                (push_one acc k h_acc_succ).val.size + (9 - (k + 1).toNat) <
                  USize64.size := by
              rw [h_push_size, h_k1_toNat]; omega
            obtain ⟨rest', hval', hbnd', hpw', hcompl'⟩ :=
              ih (k + 1) (push_one acc k h_acc_succ) v h_meas h_k1_le h_room_push hres
            refine ⟨k :: rest', ?_, ?_, ?_, ?_⟩
            · -- v.val.toList = acc.val.toList ++ (k :: rest').
              rw [hval']
              show (acc.val ++ #[k]).toList ++ rest' = acc.val.toList ++ k :: rest'
              simp
            · intro y hy
              rcases List.mem_cons.mp hy with h_eq | hyr
              · subst h_eq
                refine ⟨Nat.le_of_not_lt h_dec_lo, h_k_le_hi, h_k_le_8, h_dec_even,
                        Nat.le_refl _⟩
              · obtain ⟨h1, h2, h3, h4, h5⟩ := hbnd' y hyr
                refine ⟨h1, h2, h3, h4, ?_⟩
                rw [h_k1_toNat] at h5; omega
            · refine List.Pairwise.cons ?_ hpw'
              intro y hy
              have := hbnd' y hy
              rw [h_k1_toNat] at this
              -- this.5 : k.toNat + 1 ≤ y.toNat
              have h_y : k.toNat + 1 ≤ y.toNat := this.2.2.2.2
              exact UInt64.lt_iff_toNat_lt.mpr (by omega)
            · intro x h_ge_k h_ge_lo h_le_hi h_le_8 h_even
              by_cases h_x_eq_k : x = k.toNat
              · refine ⟨k, ?_, h_x_eq_k.symm⟩
                exact List.mem_cons_self
              · have h_ge_succ : (k + 1).toNat ≤ x := by
                  rw [h_k1_toNat]; omega
                obtain ⟨y, hy, hy_eq⟩ :=
                  hcompl' x h_ge_succ h_ge_lo h_le_hi h_le_8 h_even
                exact ⟨y, List.mem_cons_of_mem _ hy, hy_eq⟩
          · -- Skip branch (odd).
            rw [build_at_step_skip lo hi k acc h_k_le_hi h_k_le_8
                  (Or.inr h_dec_even) h_no_ov] at hres
            obtain ⟨rest, hval, hbnd, hpw, hcompl⟩ :=
              ih (k + 1) acc v h_meas h_k1_le h_room_skip hres
            refine ⟨rest, hval, ?_, hpw, ?_⟩
            · intro y hy
              obtain ⟨h1, h2, h3, h4, h5⟩ := hbnd y hy
              refine ⟨h1, h2, h3, h4, ?_⟩
              rw [h_k1_toNat] at h5; omega
            · intro x h_ge_k h_ge_lo h_le_hi h_le_8 h_even
              by_cases h_x_eq_k : x = k.toNat
              · exfalso
                rw [h_x_eq_k] at h_even
                exact h_dec_even h_even
              · have h_ge_succ : (k + 1).toNat ≤ x := by
                  rw [h_k1_toNat]; omega
                exact hcompl x h_ge_succ h_ge_lo h_le_hi h_le_8 h_even

/-! ## Aux: reduce `generate_integers a b` to a `build_at` call. -/

private theorem generate_integers_reduce (a b : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    clever_160_generate_integers.build_at
      (if a < b then a else b) (if a < b then b else a) (0 : u64)
      ⟨(List.nil : List u64).toArray, by grind⟩ = RustM.ok v := by
  unfold clever_160_generate_integers.generate_integers at hres
  have h_lt : ((a <? b) : RustM Bool) = pure (decide (a < b)) := rfl
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil : List u64).toArray, by grind⟩ := rfl
  rw [h_lt, h_new] at hres
  simp only [pure_bind, RustM_ok_bind] at hres
  by_cases h : a < b
  · have hd : decide (a < b) = true := decide_eq_true h
    rw [hd] at hres
    simp only [if_true] at hres
    rw [if_pos h, if_pos h]
    exact hres
  · have hd : decide (a < b) = false := decide_eq_false h
    rw [hd] at hres
    simp only [Bool.false_eq_true, if_false] at hres
    rw [if_neg h, if_neg h]
    exact hres

/-- `(if a < b then a else b).toNat = min a.toNat b.toNat`. -/
private theorem lo_eq_min (a b : u64) :
    (if a < b then a else b).toNat = min a.toNat b.toNat := by
  by_cases h : a < b
  · rw [if_pos h]
    have h_le : a.toNat ≤ b.toNat := Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp h)
    rw [Nat.min_eq_left h_le]
  · rw [if_neg h]
    have h_not : ¬ a.toNat < b.toNat := fun hh => h (UInt64.lt_iff_toNat_lt.mpr hh)
    have h_le : b.toNat ≤ a.toNat := Nat.le_of_not_lt h_not
    rw [Nat.min_eq_right h_le]

/-- `(if a < b then b else a).toNat = max a.toNat b.toNat`. -/
private theorem hi_eq_max (a b : u64) :
    (if a < b then b else a).toNat = max a.toNat b.toNat := by
  by_cases h : a < b
  · rw [if_pos h]
    have h_le : a.toNat ≤ b.toNat := Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp h)
    rw [Nat.max_eq_right h_le]
  · rw [if_neg h]
    have h_not : ¬ a.toNat < b.toNat := fun hh => h (UInt64.lt_iff_toNat_lt.mpr hh)
    have h_le : b.toNat ≤ a.toNat := Nat.le_of_not_lt h_not
    rw [Nat.max_eq_left h_le]

/-- Spec extracted by applying `build_at_correct` with the empty starting acc. -/
private theorem build_at_zero_spec (lo hi : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.build_at lo hi (0 : u64)
              ⟨(List.nil : List u64).toArray, by grind⟩ = RustM.ok v) :
    (∀ y ∈ v.val.toList, lo.toNat ≤ y.toNat ∧ y.toNat ≤ hi.toNat ∧
       y.toNat ≤ 8 ∧ y.toNat % 2 = 0) ∧
    v.val.toList.Pairwise (fun a b => a.toNat < b.toNat) ∧
    (∀ x : Nat, lo.toNat ≤ x → x ≤ hi.toNat → x ≤ 8 → x % 2 = 0 →
        ∃ y ∈ v.val.toList, y.toNat = x) := by
  let acc0 : alloc.vec.Vec u64 alloc.alloc.Global :=
    ⟨(List.nil : List u64).toArray, by grind⟩
  have h_meas : 9 - (0 : u64).toNat ≤ 9 := by rw [u64_zero_toNat]; omega
  have h_zero_le : (0 : u64).toNat ≤ 10 := by rw [u64_zero_toNat]; omega
  have h_room0 : acc0.val.size + (9 - (0 : u64).toNat) < USize64.size := by
    show 0 + (9 - 0) < USize64.size
    rw [usize_size_eq_2_64]; decide
  obtain ⟨rest, hval, hbnd, hpw, hcompl⟩ :=
    build_at_correct lo hi 9 (0 : u64) acc0 v h_meas h_zero_le h_room0 hres
  have h_vlist : v.val.toList = rest := by
    rw [hval]
    show (List.nil : List u64).toArray.toList ++ rest = rest
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [h_vlist] at hy
    obtain ⟨h1, h2, h3, h4, _⟩ := hbnd y hy
    exact ⟨h1, h2, h3, h4⟩
  · rw [h_vlist]; exact hpw
  · intro x hx_ge_lo hx_le_hi hx_le_8 hx_even
    have h_zero_le_x : (0 : u64).toNat ≤ x := by rw [u64_zero_toNat]; omega
    obtain ⟨y, hy, hy_eq⟩ := hcompl x h_zero_le_x hx_ge_lo hx_le_hi hx_le_8 hx_even
    refine ⟨y, ?_, hy_eq⟩
    rw [h_vlist]; exact hy

/-! ## Main contract clauses. -/

theorem all_elements_even
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat % 2 = 0 := by
  obtain ⟨hbnd, _, _⟩ := build_at_zero_spec _ _ v (generate_integers_reduce a b v hres)
  intro k hk
  have h_mem : v.val[k]'hk ∈ v.val.toList :=
    Array.mem_def.mp (Array.getElem_mem hk)
  exact (hbnd _ h_mem).2.2.2

theorem all_elements_at_most_8
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat ≤ 8 := by
  obtain ⟨hbnd, _, _⟩ := build_at_zero_spec _ _ v (generate_integers_reduce a b v hres)
  intro k hk
  have h_mem : v.val[k]'hk ∈ v.val.toList :=
    Array.mem_def.mp (Array.getElem_mem hk)
  exact (hbnd _ h_mem).2.2.1

theorem all_elements_at_least_min
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size),
      min a.toNat b.toNat ≤ (v.val[k]'hk).toNat := by
  obtain ⟨hbnd, _, _⟩ := build_at_zero_spec _ _ v (generate_integers_reduce a b v hres)
  intro k hk
  have h_mem : v.val[k]'hk ∈ v.val.toList :=
    Array.mem_def.mp (Array.getElem_mem hk)
  have h1 := (hbnd _ h_mem).1
  rw [lo_eq_min] at h1
  exact h1

theorem all_elements_at_most_max
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size),
      (v.val[k]'hk).toNat ≤ max a.toNat b.toNat := by
  obtain ⟨hbnd, _, _⟩ := build_at_zero_spec _ _ v (generate_integers_reduce a b v hres)
  intro k hk
  have h_mem : v.val[k]'hk ∈ v.val.toList :=
    Array.mem_def.mp (Array.getElem_mem hk)
  have h2 := (hbnd _ h_mem).2.1
  rw [hi_eq_max] at h2
  exact h2

theorem complete
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v)
    (x : u64)
    (hx_even : x.toNat % 2 = 0)
    (hx_le_8 : x.toNat ≤ 8)
    (hx_ge_lo : min a.toNat b.toNat ≤ x.toNat)
    (hx_le_hi : x.toNat ≤ max a.toNat b.toNat) :
    ∃ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk) = x := by
  obtain ⟨_, _, hcompl⟩ := build_at_zero_spec _ _ v (generate_integers_reduce a b v hres)
  -- Convert hx_ge_lo / hx_le_hi to use lo, hi directly.
  rw [← lo_eq_min a b] at hx_ge_lo
  rw [← hi_eq_max a b] at hx_le_hi
  obtain ⟨y, hy, hy_eq⟩ := hcompl x.toNat hx_ge_lo hx_le_hi hx_le_8 hx_even
  -- y ∈ v.val.toList, y.toNat = x.toNat ⇒ y = x.
  have h_eq : y = x := UInt64.toNat_inj.mp hy_eq
  subst h_eq
  obtain ⟨k, hk_lt, hget⟩ := List.mem_iff_getElem.mp hy
  have hk_size : k < v.val.size := by simpa using hk_lt
  refine ⟨k, hk_size, ?_⟩
  simp only [Array.getElem_toList] at hget
  exact hget

theorem strictly_ascending
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k + 1 < v.val.size),
      (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat < (v.val[k + 1]'hk).toNat := by
  obtain ⟨_, hpw, _⟩ := build_at_zero_spec _ _ v (generate_integers_reduce a b v hres)
  intro k hk
  have hk1_list : k + 1 < v.val.toList.length := by simp [hk]
  have hk_list : k < v.val.toList.length := Nat.lt_of_succ_lt hk1_list
  have h_pw_at :=
    List.pairwise_iff_getElem.mp hpw k (k + 1) hk_list hk1_list (Nat.lt_succ_self _)
  simp only [Array.getElem_toList] at h_pw_at
  exact h_pw_at

theorem symmetric_in_arguments
    (a b : u64) :
    clever_160_generate_integers.generate_integers a b =
      clever_160_generate_integers.generate_integers b a := by
  unfold clever_160_generate_integers.generate_integers
  have h_ab : ((a <? b) : RustM Bool) = pure (decide (a < b)) := rfl
  have h_ba : ((b <? a) : RustM Bool) = pure (decide (b < a)) := rfl
  rw [h_ab, h_ba]
  simp only [pure_bind]
  -- Case split on a vs b.
  by_cases h_ab : a < b
  · -- Then ¬ b < a.
    have h_ba_not : ¬ b < a := by
      intro h
      have h1 := UInt64.lt_iff_toNat_lt.mp h_ab
      have h2 := UInt64.lt_iff_toNat_lt.mp h
      omega
    have hd_ab : decide (a < b) = true := decide_eq_true h_ab
    have hd_ba : decide (b < a) = false := decide_eq_false h_ba_not
    rw [hd_ab, hd_ba]
    simp only [if_true, Bool.false_eq_true, if_false]
  · -- ¬ a < b.
    by_cases h_ba : b < a
    · -- a > b, so this case.
      have hd_ab : decide (a < b) = false := decide_eq_false h_ab
      have hd_ba : decide (b < a) = true := decide_eq_true h_ba
      rw [hd_ab, hd_ba]
      simp only [if_true, Bool.false_eq_true, if_false]
    · -- ¬ a < b ∧ ¬ b < a ⇒ a = b.
      have h_eq : a = b := by
        have h1 : ¬ a.toNat < b.toNat := fun hh => h_ab (UInt64.lt_iff_toNat_lt.mpr hh)
        have h2 : ¬ b.toNat < a.toNat := fun hh => h_ba (UInt64.lt_iff_toNat_lt.mpr hh)
        apply UInt64.toNat_inj.mp
        omega
      subst h_eq
      rfl

end Clever_160_generate_integersObligations
