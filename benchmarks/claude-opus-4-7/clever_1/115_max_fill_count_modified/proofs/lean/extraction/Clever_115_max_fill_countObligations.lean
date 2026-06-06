-- Companion obligations file for the `clever_115_max_fill_count` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_115_max_fill_count

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Clever_115_max_fill_countObligations

/-! ## Specification oracles. -/

/-- Count occurrences of `target` among the first `k` entries of `s`. -/
private def vec_count (s : Array u64) (target : u64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-- Nat-level popcount: number of `1`-bits in the binary representation. -/
private def popcount_nat : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) % 2 + popcount_nat ((n + 1) / 2)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

/-- Lifted spec: popcount of a `u64` value. -/
private def popcount (x : u64) : Nat := popcount_nat x.toNat

/-! ## Standard scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide
private theorem u64_size_eq : (UInt64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  have h_no_bv :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  rw [h_no_bv]; rfl

private theorem u64_add_ok (a b : u64) (h : a.toNat + b.toNat < 2^64) :
    (a +? b : RustM u64) = RustM.ok (a + b) := by
  show (rust_primitives.ops.arith.Add.add a b : RustM u64) = RustM.ok (a + b)
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec
        then (.fail .integerOverflow : RustM u64)
        else pure (a + b)) = _
  have h_no_bv :
      BitVec.uaddOverflow a.toBitVec b.toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow a.toBitVec b.toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_ov : UInt64.addOverflow a b = true := hbo
      have h_iff := @UInt64.addOverflow_iff a b
      have hii : a.toNat + b.toNat ≥ 2 ^ 64 := h_iff.mp h_ov
      omega
  rw [h_no_bv]; rfl

private theorem u64_add_toNat (a b : u64) (h : a.toNat + b.toNat < 2^64) :
    (a + b).toNat = a.toNat + b.toNat :=
  UInt64.toNat_add_of_lt h

/-- Push a single element onto an `alloc.vec.Vec`. -/
private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

private theorem push_one_size (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

/-! ## `vec_count` lemmas. -/

private theorem vec_count_succ (s : Array u64) (target : u64) (k : Nat) (hk : k < s.size) :
    vec_count s target (k + 1) =
      (if (s[k]'hk) = target then 1 else 0) + vec_count s target k := by
  show (if h : k < s.size then
          (if (s[k]'h) = target then 1 else 0) + vec_count s target k
        else vec_count s target k) = _
  rw [dif_pos hk]

private theorem vec_count_prefix (acc : Array u64) (y target : u64) :
    ∀ k, k ≤ acc.size →
      vec_count (acc ++ #[y]) target k = vec_count acc target k := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < acc.size := by omega
    have hk_lt_app : k < (acc ++ #[y]).size := by rw [h_size_app]; omega
    have h_app : (acc ++ #[y])[k]'hk_lt_app = acc[k]'hk_lt :=
      Array.getElem_append_left hk_lt
    show (if h : k < (acc ++ #[y]).size then
            (if ((acc ++ #[y])[k]'h) = target then 1 else 0)
              + vec_count (acc ++ #[y]) target k
          else vec_count (acc ++ #[y]) target k) = _
    rw [dif_pos hk_lt_app, h_app, ih (Nat.le_of_lt hk)]
    show _ = (if h : k < acc.size then
                (if (acc[k]'h) = target then 1 else 0) + vec_count acc target k
              else vec_count acc target k)
    rw [dif_pos hk_lt]

private theorem vec_count_append_singleton (acc : Array u64) (y target : u64) :
    vec_count (acc ++ #[y]) target (acc.size + 1) =
      vec_count acc target acc.size + (if y = target then 1 else 0) := by
  have h_size_app : (acc ++ #[y]).size = acc.size + 1 := by rw [Array.size_append]; rfl
  have h_lt : acc.size < (acc ++ #[y]).size := by rw [h_size_app]; omega
  have h_get : (acc ++ #[y])[acc.size]'h_lt = y := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  have h_step := vec_count_succ (acc ++ #[y]) target acc.size h_lt
  rw [h_step, h_get, vec_count_prefix acc y target acc.size (Nat.le_refl _)]
  omega

/-! ## Sortedness predicate under lex order. -/

/-- Non-strict lex order on `u64` keyed by `(popcount, value)`. -/
private def lex_le_u64 (a b : u64) : Prop :=
  popcount a < popcount b ∨ (popcount a = popcount b ∧ a.toNat ≤ b.toNat)

/-- Strict lex order on `u64` keyed by `(popcount, value)`. -/
private def lex_lt_u64 (a b : u64) : Prop :=
  popcount a < popcount b ∨ (popcount a = popcount b ∧ a.toNat < b.toNat)

private instance decLex_le_u64 (a b : u64) : Decidable (lex_le_u64 a b) := by
  unfold lex_le_u64; exact inferInstance

private instance decLex_lt_u64 (a b : u64) : Decidable (lex_lt_u64 a b) := by
  unfold lex_lt_u64; exact inferInstance

/-- Lex-sorted array. -/
private def sorted_lex (arr : Array u64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → lex_le_u64 (arr[k₁]'h₁) (arr[k₂]'h₂)

private theorem lex_le_u64_refl (a : u64) : lex_le_u64 a a := by
  right; exact ⟨rfl, Nat.le_refl _⟩

private theorem lex_le_u64_trans (a b c : u64)
    (hab : lex_le_u64 a b) (hbc : lex_le_u64 b c) : lex_le_u64 a c := by
  rcases hab with h_lt | ⟨h_eq, h_le⟩
  · rcases hbc with h_lt' | ⟨h_eq', _⟩
    · left; omega
    · left; rw [← h_eq']; exact h_lt
  · rcases hbc with h_lt' | ⟨h_eq', h_le'⟩
    · left; rw [h_eq]; exact h_lt'
    · right; refine ⟨?_, ?_⟩
      · rw [h_eq, h_eq']
      · omega

private theorem lex_lt_u64_imp_le (a b : u64) (h : lex_lt_u64 a b) : lex_le_u64 a b := by
  rcases h with h | ⟨h_eq, h_lt⟩
  · left; exact h
  · right; exact ⟨h_eq, Nat.le_of_lt h_lt⟩

/-- Totality: `¬ lex_lt b a ↔ lex_le a b`. -/
private theorem not_lex_lt_iff_lex_le (a b : u64) :
    ¬ lex_lt_u64 b a ↔ lex_le_u64 a b := by
  constructor
  · intro h
    by_cases h_pa : popcount a < popcount b
    · exact Or.inl h_pa
    · by_cases h_pb : popcount b < popcount a
      · exfalso; exact h (Or.inl h_pb)
      · have h_eq : popcount a = popcount b := by
          unfold popcount at h_pa h_pb
          unfold popcount
          omega
        refine Or.inr ⟨h_eq, ?_⟩
        by_cases h_ab : a.toNat ≤ b.toNat
        · exact h_ab
        · exfalso
          have h_ba : b.toNat < a.toNat := by omega
          exact h (Or.inr ⟨h_eq.symm, h_ba⟩)
  · intro h h_lt
    rcases h with h_lt' | ⟨h_eq', h_le'⟩
    · rcases h_lt with h | ⟨h_eq, _⟩
      · unfold popcount at h h_lt'; omega
      · unfold popcount at h_eq h_lt'; omega
    · rcases h_lt with h | ⟨_, h_lt''⟩
      · unfold popcount at h h_eq'; omega
      · omega

/-- `¬ lex_le b a` implies `lex_lt a b`. -/
private theorem lex_lt_of_not_le (a b : u64) (h : ¬ lex_le_u64 b a) : lex_lt_u64 a b := by
  by_cases h_lt : lex_lt_u64 a b
  · exact h_lt
  · exfalso; exact h ((not_lex_lt_iff_lex_le b a).mp h_lt)

/-! ## Sortedness append lemma under lex. -/

private theorem sorted_lex_empty : sorted_lex #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array u64).size = 0 := rfl
  omega

private theorem sorted_lex_append_singleton (acc : Array u64) (y : u64)
    (h_acc : sorted_lex acc)
    (h_le : ∀ (k : Nat) (hk : k < acc.size), lex_le_u64 (acc[k]'hk) y) :
    sorted_lex (acc ++ #[y]) := by
  intro k₁ k₂ h₁ h₂ hle12
  rw [Array.size_append] at h₁ h₂
  have h_one : (#[y] : Array u64).size = 1 := rfl
  by_cases h_k1_lt : k₁ < acc.size
  · by_cases h_k2_lt : k₂ < acc.size
    · rw [Array.getElem_append_left h_k1_lt, Array.getElem_append_left h_k2_lt]
      exact h_acc k₁ k₂ h_k1_lt h_k2_lt hle12
    · have h_k2_ge : acc.size ≤ k₂ := by omega
      rw [Array.getElem_append_left h_k1_lt]
      rw [Array.getElem_append_right h_k2_ge]
      have h_idx : k₂ - acc.size = 0 := by omega
      have h_zero : (0 : Nat) < (#[y] : Array u64).size := by rw [h_one]; omega
      rw [show ((#[y] : Array u64)[k₂ - acc.size]'(by rw [h_idx]; exact h_zero))
              = (#[y] : Array u64)[0]'h_zero from by simp [h_idx]]
      show lex_le_u64 (acc[k₁]'h_k1_lt) y
      exact h_le k₁ h_k1_lt
  · have h_k1_ge : acc.size ≤ k₁ := by omega
    have h_k2_ge : acc.size ≤ k₂ := by omega
    rw [Array.getElem_append_right h_k1_ge, Array.getElem_append_right h_k2_ge]
    have h_k1_idx : k₁ - acc.size = 0 := by omega
    have h_k2_idx : k₂ - acc.size = 0 := by omega
    have h_zero : (0 : Nat) < (#[y] : Array u64).size := by rw [h_one]; omega
    rw [show ((#[y] : Array u64)[k₁ - acc.size]'(by rw [h_k1_idx]; exact h_zero))
            = (#[y] : Array u64)[0]'h_zero from by simp [h_k1_idx]]
    rw [show ((#[y] : Array u64)[k₂ - acc.size]'(by rw [h_k2_idx]; exact h_zero))
            = (#[y] : Array u64)[0]'h_zero from by simp [h_k2_idx]]
    exact lex_le_u64_refl _

/-! ## popcount Nat-level lemmas. -/

private theorem popcount_nat_zero : popcount_nat 0 = 0 := by
  conv => lhs; unfold popcount_nat

private theorem popcount_nat_succ_eq (n : Nat) :
    popcount_nat (n + 1) = (n + 1) % 2 + popcount_nat ((n + 1) / 2) := by
  conv => lhs; unfold popcount_nat

/-- Auxiliary: `popcount_nat n ≤ n` for all natural numbers (induction on a bound). -/
private theorem popcount_nat_le_self_aux : ∀ (m n : Nat), n ≤ m → popcount_nat n ≤ n := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have h_zero : n = 0 := Nat.le_zero.mp hn
    rw [h_zero, popcount_nat_zero]
    exact Nat.zero_le _
  | succ m ih =>
    intro n hn
    match n with
    | 0 => rw [popcount_nat_zero]; exact Nat.zero_le _
    | k + 1 =>
      rw [popcount_nat_succ_eq]
      have h_div_lt : (k+1)/2 < k+1 := Nat.div_lt_self (Nat.succ_pos _) (by decide)
      have h_div_le : (k+1)/2 ≤ m := by omega
      have ih_d := ih ((k+1)/2) h_div_le
      have h_mod_lt : (k+1) % 2 < 2 := Nat.mod_lt _ (by decide)
      have h_split : k + 1 = 2 * ((k+1)/2) + (k+1)%2 := (Nat.div_add_mod (k+1) 2).symm
      omega

private theorem popcount_nat_le_self (n : Nat) : popcount_nat n ≤ n :=
  popcount_nat_le_self_aux n n (Nat.le_refl _)

/-! ## u64 div/mod/cmp oracle lemmas. -/

private theorem u64_mod_ok (n d : u64) (hd : d ≠ 0) :
    (n %? d : RustM u64) = RustM.ok (n % d) := by
  show (rust_primitives.ops.arith.Rem.rem n d : RustM u64) = _
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n % d)) = _
  rw [if_neg hd]; rfl

private theorem u64_div_ok (n d : u64) (hd : d ≠ 0) :
    (n /? d : RustM u64) = RustM.ok (n / d) := by
  show (rust_primitives.ops.arith.Div.div n d : RustM u64) = _
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n / d)) = _
  rw [if_neg hd]; rfl

private theorem u64_toNat_div (a b : u64) : (a / b).toNat = a.toNat / b.toNat :=
  UInt64.toNat_div a b

private theorem u64_toNat_mod (a b : u64) : (a % b).toNat = a.toNat % b.toNat :=
  UInt64.toNat_mod a b

private theorem u64_eq_zero_test (n : u64) :
    (n ==? (0 : u64) : RustM Bool) = RustM.ok (decide (n = 0)) := by
  show (rust_primitives.cmp.eq n (0 : u64) : RustM Bool) = _
  show pure (n == (0 : u64) : Bool) = _
  rw [show (n == (0 : u64) : Bool) = decide (n = 0) from by
    by_cases h : n = 0
    · rw [h]; decide
    · simp [h]]
  rfl

private theorem u64_lt_test (a b : u64) :
    (a <? b : RustM Bool) = RustM.ok (decide (a.toNat < b.toNat)) := by
  show (rust_primitives.cmp.lt a b : RustM Bool) = _
  show pure (decide (a < b) : Bool) = _
  rw [show (decide (a < b) : Bool) = decide (a.toNat < b.toNat) from by
    by_cases h : a.toNat < b.toNat
    · have : a < b := by rw [UInt64.lt_iff_toNat_lt]; exact h
      rw [decide_eq_true this, decide_eq_true h]
    · have : ¬ (a < b) := by rw [UInt64.lt_iff_toNat_lt]; exact h
      rw [decide_eq_false this, decide_eq_false h]]
  rfl

private theorem u64_gt_test (a b : u64) :
    (a >? b : RustM Bool) = RustM.ok (decide (b.toNat < a.toNat)) := by
  show (rust_primitives.cmp.gt a b : RustM Bool) = _
  show pure (decide (a > b) : Bool) = _
  rw [show (decide (a > b) : Bool) = decide (b.toNat < a.toNat) from by
    by_cases h : b.toNat < a.toNat
    · have : a > b := by show b < a; rw [UInt64.lt_iff_toNat_lt]; exact h
      rw [decide_eq_true this, decide_eq_true h]
    · have : ¬ (a > b) := by show ¬ b < a; rw [UInt64.lt_iff_toNat_lt]; exact h
      rw [decide_eq_false this, decide_eq_false h]]
  rfl

private theorem u64_toNat_pos_of_ne_zero (n : u64) (h : n ≠ 0) : 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with h_zero | h_pos
  · exfalso; apply h
    have : n.toNat = (0 : u64).toNat := by rw [h_zero]; rfl
    exact UInt64.toNat_inj.mp this
  · exact h_pos

/-! ## popcount oracle correctness. -/

private theorem popcount_at_correct :
    ∀ (m : Nat) (n : u64) (acc : u64),
      n.toNat ≤ m →
      acc.toNat + popcount_nat n.toNat < 2^64 →
      ∃ p : u64,
        clever_115_max_fill_count.popcount_at n acc = RustM.ok p ∧
        p.toNat = acc.toNat + popcount_nat n.toNat := by
  intro m
  induction m with
  | zero =>
    intro n acc hm _
    have h_zero : n.toNat = 0 := by omega
    have h_n_eq : n = 0 := by
      have : n.toNat = (0 : u64).toNat := by rw [h_zero]; rfl
      exact UInt64.toNat_inj.mp this
    refine ⟨acc, ?_, ?_⟩
    · unfold clever_115_max_fill_count.popcount_at
      rw [h_n_eq]
      have h_eq_zero : ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := by
        show pure ((0 : u64) == (0 : u64) : Bool) = RustM.ok true
        rfl
      simp only [h_eq_zero, RustM_ok_bind, ↓reduceIte]
      rfl
    · rw [h_zero, popcount_nat_zero]
  | succ m ih =>
    intro n acc hm h_bound
    by_cases hn_zero : n = 0
    · refine ⟨acc, ?_, ?_⟩
      · unfold clever_115_max_fill_count.popcount_at
        rw [hn_zero]
        have h_eq_zero : ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := by
          show pure ((0 : u64) == (0 : u64) : Bool) = RustM.ok true
          rfl
        simp only [h_eq_zero, RustM_ok_bind, ↓reduceIte]
        rfl
      · have h_zero_toNat : n.toNat = 0 := by rw [hn_zero]; rfl
        rw [h_zero_toNat, popcount_nat_zero]
    · have hn_pos : 0 < n.toNat := u64_toNat_pos_of_ne_zero n hn_zero
      have h_mod_toNat : (n % 2).toNat = n.toNat % 2 := u64_toNat_mod n 2
      have h_div_toNat : (n / 2).toNat = n.toNat / 2 := u64_toNat_div n 2
      have h_popcount_succ : popcount_nat n.toNat
          = n.toNat % 2 + popcount_nat (n.toNat / 2) := by
        cases h : n.toNat with
        | zero => omega
        | succ k =>
          show popcount_nat (k+1) = _
          rw [popcount_nat_succ_eq]
      have h_div_lt : n.toNat / 2 < n.toNat := Nat.div_lt_self hn_pos (by decide)
      have h_div_le_m : (n / 2).toNat ≤ m := by rw [h_div_toNat]; omega
      have h_acc_add_bound : acc.toNat + (n % 2).toNat < 2^64 := by
        rw [h_mod_toNat]; rw [h_popcount_succ] at h_bound
        have h_pc_ge : 0 ≤ popcount_nat (n.toNat / 2) := Nat.zero_le _
        omega
      have h_acc_add_toNat : (acc + (n % 2)).toNat = acc.toNat + (n % 2).toNat :=
        u64_add_toNat acc (n % 2) h_acc_add_bound
      have h_new_bound : (acc + (n % 2)).toNat + popcount_nat (n / 2).toNat < 2^64 := by
        rw [h_acc_add_toNat, h_mod_toNat, h_div_toNat]
        rw [h_popcount_succ] at h_bound
        omega
      have ih_app := ih (n / 2) (acc + (n % 2)) h_div_le_m h_new_bound
      obtain ⟨p, h_p_eq, h_p_toNat⟩ := ih_app
      refine ⟨p, ?_, ?_⟩
      · unfold clever_115_max_fill_count.popcount_at
        rw [u64_eq_zero_test]
        have h_dec_ne : decide (n = 0) = false := decide_eq_false hn_zero
        simp only [RustM_ok_bind, h_dec_ne, Bool.false_eq_true, ↓reduceIte]
        rw [u64_div_ok n 2 (by decide)]
        simp only [RustM_ok_bind]
        rw [u64_mod_ok n 2 (by decide)]
        simp only [RustM_ok_bind]
        rw [u64_add_ok acc (n % 2) h_acc_add_bound]
        simp only [RustM_ok_bind]
        exact h_p_eq
      · rw [h_p_toNat, h_acc_add_toNat, h_mod_toNat, h_div_toNat]
        rw [h_popcount_succ]; omega

private theorem popcount_at_zero_correct (n : u64) :
    ∃ p : u64,
      clever_115_max_fill_count.popcount_at n 0 = RustM.ok p ∧
      p.toNat = popcount_nat n.toNat := by
  have h_bound : (0 : u64).toNat + popcount_nat n.toNat < 2^64 := by
    have h_le := popcount_nat_le_self n.toNat
    have h_n_lt : n.toNat < 2^64 := by
      have := n.toNat_lt
      have h_size : (UInt64.size : Nat) = 2^64 := by decide
      omega
    have h_zero : (0 : u64).toNat = 0 := rfl
    omega
  have h := popcount_at_correct n.toNat n 0 (Nat.le_refl _) h_bound
  obtain ⟨p, h_eq, h_p⟩ := h
  refine ⟨p, h_eq, ?_⟩
  have h_zero : (0 : u64).toNat = 0 := rfl
  rw [h_zero] at h_p
  omega

/-! ## lex_less Bool oracle correctness. -/

private theorem lex_less_correct (a b : u64) :
    clever_115_max_fill_count.lex_less a b = RustM.ok (decide (lex_lt_u64 a b)) := by
  unfold clever_115_max_fill_count.lex_less
  obtain ⟨pa, h_pa_eq, h_pa_toNat⟩ := popcount_at_zero_correct a
  obtain ⟨pb, h_pb_eq, h_pb_toNat⟩ := popcount_at_zero_correct b
  rw [h_pa_eq]
  simp only [RustM_ok_bind]
  rw [h_pb_eq]
  simp only [RustM_ok_bind]
  rw [u64_lt_test, u64_gt_test]
  simp only [RustM_ok_bind]
  by_cases h_lt : pa.toNat < pb.toNat
  · have h_dec : decide (pa.toNat < pb.toNat) = true := decide_eq_true h_lt
    rw [h_dec]
    simp only [↓reduceIte]
    have h_pc_lt : popcount a < popcount b := by
      show popcount_nat a.toNat < popcount_nat b.toNat
      rw [← h_pa_toNat, ← h_pb_toNat]; exact h_lt
    have h_lex_lt : lex_lt_u64 a b := Or.inl h_pc_lt
    rw [decide_eq_true h_lex_lt]
    rfl
  · have h_dec_lt : decide (pa.toNat < pb.toNat) = false := decide_eq_false h_lt
    rw [h_dec_lt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h_gt : pb.toNat < pa.toNat
    · have h_dec_gt : decide (pb.toNat < pa.toNat) = true := decide_eq_true h_gt
      rw [h_dec_gt]
      simp only [↓reduceIte]
      have h_pc_gt : popcount b < popcount a := by
        show popcount_nat b.toNat < popcount_nat a.toNat
        rw [← h_pa_toNat, ← h_pb_toNat]; exact h_gt
      have h_not_lex_lt : ¬ lex_lt_u64 a b := by
        intro h
        rcases h with h | ⟨h_eq, _⟩
        · unfold popcount at h_pc_gt h; omega
        · unfold popcount at h_eq h_pc_gt; omega
      rw [decide_eq_false h_not_lex_lt]
      rfl
    · have h_dec_gt : decide (pb.toNat < pa.toNat) = false := decide_eq_false h_gt
      rw [h_dec_gt]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h_pc_eq : popcount a = popcount b := by
        show popcount_nat a.toNat = popcount_nat b.toNat
        rw [← h_pa_toNat, ← h_pb_toNat]; omega
      rw [u64_lt_test]
      by_cases h_ab : a.toNat < b.toNat
      · have h_dec_ab : decide (a.toNat < b.toNat) = true := decide_eq_true h_ab
        rw [h_dec_ab]
        have h_lex_lt : lex_lt_u64 a b := Or.inr ⟨h_pc_eq, h_ab⟩
        rw [decide_eq_true h_lex_lt]
      · have h_dec_ab : decide (a.toNat < b.toNat) = false := decide_eq_false h_ab
        rw [h_dec_ab]
        have h_not_lex_lt : ¬ lex_lt_u64 a b := by
          intro h
          rcases h with h | ⟨_, h_lt⟩
          · unfold popcount at h_pc_eq h; omega
          · exact h_ab h_lt
        rw [decide_eq_false h_not_lex_lt]

end Clever_115_max_fill_countObligations

namespace Clever_115_max_fill_countObligations

/-! ## OOB / step / fail lemmas for `insert_sorted_at`. -/

private theorem insert_sorted_at_oob_done (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_115_max_fill_count.insert_sorted_at v x i true acc = RustM.ok acc := by
  unfold clever_115_max_fill_count.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not,
             Bool.not_true]
  rfl

private theorem insert_sorted_at_oob_not_done (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_115_max_fill_count.insert_sorted_at v x i false acc =
      RustM.ok (push_one acc x h_acc) := by
  unfold clever_115_max_fill_count.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  rfl

private theorem insert_sorted_at_oob_not_done_fail (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_115_max_fill_count.insert_sorted_at v x i false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_115_max_fill_count.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- Step-insert branch: i in bounds, done=false, lex_less v[i] x = false (i.e. lex_le x v[i]).
    Pushes x, then pushes v[i], recurses with done=true. -/
private theorem insert_sorted_at_step_insert (v : RustSlice u64) (x : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_le : lex_le_u64 x (v.val[i.toNat]'hi))
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_115_max_fill_count.insert_sorted_at v x i false acc =
      clever_115_max_fill_count.insert_sorted_at v x (i + 1) true
        (push_one (push_one acc x (by omega)) (v.val[i.toNat]'hi)
          (by rw [push_one_size]; omega)) := by
  conv => lhs; unfold clever_115_max_fill_count.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_not_lex_lt : ¬ lex_lt_u64 (v.val[i.toNat]'hi) x :=
    (not_lex_lt_iff_lex_le x (v.val[i.toNat]'hi)).mpr h_le
  have h_lex_false : clever_115_max_fill_count.lex_less (v.val[i.toNat]'hi) x
                      = RustM.ok false := by
    rw [lex_less_correct]
    have : decide (lex_lt_u64 (v.val[i.toNat]'hi) x) = false :=
      decide_eq_false h_not_lex_lt
    rw [this]
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_acc_e : acc.val.size + 1 < USize64.size := by omega
  have h_app_size_e :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc_e
  have h_extend_e :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc_e) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_e]; rfl
  have h_acc_v : (push_one acc x h_acc_e).val.size + 1 < USize64.size := by
    rw [push_one_size]; omega
  have h_app_size_v :
      (push_one acc x h_acc_e).val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show (push_one acc x h_acc_e).val.size + 1 < USize64.size; exact h_acc_v
  have h_extend_v :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global (push_one acc x h_acc_e)
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi) h_acc_v) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_v]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false]
  rw [h_lex_false]
  simp only [RustM_ok_bind, Bool.not_false,
             rust_primitives.hax.logical_op.and, Bool.true_and,
             pure_bind, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_e]
  simp only [RustM_ok_bind]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_v]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- Step-insert failure: first push of x overflows. -/
private theorem insert_sorted_at_step_insert_fail_x (v : RustSlice u64) (x : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_le : lex_le_u64 x (v.val[i.toNat]'hi))
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_115_max_fill_count.insert_sorted_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_115_max_fill_count.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_not_lex_lt : ¬ lex_lt_u64 (v.val[i.toNat]'hi) x :=
    (not_lex_lt_iff_lex_le x (v.val[i.toNat]'hi)).mpr h_le
  have h_lex_false : clever_115_max_fill_count.lex_less (v.val[i.toNat]'hi) x
                      = RustM.ok false := by
    rw [lex_less_correct]
    have : decide (lex_lt_u64 (v.val[i.toNat]'hi) x) = false :=
      decide_eq_false h_not_lex_lt
    rw [this]
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false]
  rw [h_lex_false]
  simp only [RustM_ok_bind, Bool.not_false,
             rust_primitives.hax.logical_op.and, Bool.true_and,
             pure_bind, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- Step-insert failure: first push succeeds, second push of v[i] overflows. -/
private theorem insert_sorted_at_step_insert_fail_v (v : RustSlice u64) (x : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_le : lex_le_u64 x (v.val[i.toNat]'hi))
    (h_acc_e : acc.val.size + 1 < USize64.size)
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_115_max_fill_count.insert_sorted_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_115_max_fill_count.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_not_lex_lt : ¬ lex_lt_u64 (v.val[i.toNat]'hi) x :=
    (not_lex_lt_iff_lex_le x (v.val[i.toNat]'hi)).mpr h_le
  have h_lex_false : clever_115_max_fill_count.lex_less (v.val[i.toNat]'hi) x
                      = RustM.ok false := by
    rw [lex_less_correct]
    have : decide (lex_lt_u64 (v.val[i.toNat]'hi) x) = false :=
      decide_eq_false h_not_lex_lt
    rw [this]
  have h_app_size_e :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc_e
  have h_extend_e :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc_e) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_e]; rfl
  have h_app_size_v_neg :
      ¬ (push_one acc x h_acc_e).val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    rw [push_one_size]
    show ¬ acc.val.size + 1 + 1 < USize64.size; omega
  have h_extend_v_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global (push_one acc x h_acc_e)
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_v_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false]
  rw [h_lex_false]
  simp only [RustM_ok_bind, Bool.not_false,
             rust_primitives.hax.logical_op.and, Bool.true_and,
             pure_bind, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_e]
  simp only [RustM_ok_bind]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_v_fail]
  rfl

/-- Pass step: either done=true, or lex_lt_u64 (v[i]) x. Push v[i] once and recurse. -/
private theorem insert_sorted_at_step_pass (v : RustSlice u64) (x : u64) (i : usize)
    (done : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : done = true ∨ lex_lt_u64 (v.val[i.toNat]'hi) x)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_115_max_fill_count.insert_sorted_at v x i done acc =
      clever_115_max_fill_count.insert_sorted_at v x (i + 1) done
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_115_max_fill_count.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_app_size :
      acc.val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  -- Reduce the lex_less call to a Bool and then take the else branch.
  have h_lex_eq : clever_115_max_fill_count.lex_less (v.val[i.toNat]'hi) x
                    = RustM.ok (decide (lex_lt_u64 (v.val[i.toNat]'hi) x)) :=
    lex_less_correct _ _
  -- The condition `(!done) && (! decide(lex_lt v[i] x))` should be false in both subcases.
  have h_cond_false : ((!done) && (!(decide (lex_lt_u64 (v.val[i.toNat]'hi) x)))) = false := by
    cases h_skip with
    | inl h_done_true => subst h_done_true; rfl
    | inr h_lt =>
      have hh : decide (lex_lt_u64 (v.val[i.toNat]'hi) x) = true := decide_eq_true h_lt
      rw [hh]
      cases done <;> rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_lex_eq]
  simp only [RustM_ok_bind,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and,
             pure_bind]
  rw [h_cond_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem insert_sorted_at_step_pass_fail (v : RustSlice u64) (x : u64) (i : usize)
    (done : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : done = true ∨ lex_lt_u64 (v.val[i.toNat]'hi) x)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_115_max_fill_count.insert_sorted_at v x i done acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_115_max_fill_count.insert_sorted_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_app_size_neg :
      ¬ acc.val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  have h_lex_eq : clever_115_max_fill_count.lex_less (v.val[i.toNat]'hi) x
                    = RustM.ok (decide (lex_lt_u64 (v.val[i.toNat]'hi) x)) :=
    lex_less_correct _ _
  have h_cond_false : ((!done) && (!(decide (lex_lt_u64 (v.val[i.toNat]'hi) x)))) = false := by
    cases h_skip with
    | inl h_done_true => subst h_done_true; rfl
    | inr h_lt =>
      have hh : decide (lex_lt_u64 (v.val[i.toNat]'hi) x) = true := decide_eq_true h_lt
      rw [hh]
      cases done <;> rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_lex_eq]
  simp only [RustM_ok_bind,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and,
             pure_bind]
  rw [h_cond_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## Invariant for `insert_sorted_at`: size + vec_count (multiset). -/

private theorem insert_sorted_at_inv :
    ∀ (n : Nat) (v : RustSlice u64) (x : u64) (i : usize) (done : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_115_max_fill_count.insert_sorted_at v x i done acc = RustM.ok r →
      r.val.size = acc.val.size + (v.val.size - i.toNat) + (if done then 0 else 1) ∧
      vec_count r.val target r.val.size + vec_count v.val target i.toNat =
        vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
          + (if done then 0 else (if x = target then 1 else 0)) := by
  intro n
  induction n with
  | zero =>
    intro v x i done acc r target hm hi_le hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = v.val.size := by omega
    cases done with
    | true =>
      rw [insert_sorted_at_oob_done v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · simp [hi_eq]
      · rw [hi_eq]; simp
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_oob_not_done v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
          rw [Array.size_append]; simp; omega
        · show vec_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + vec_count v.val target i.toNat
              = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                + (if x = target then 1 else 0)
          have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size, vec_count_append_singleton, hi_eq]
          omega
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v x i done acc r target hm hi_le hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · have hi_eq : i.toNat = v.val.size := by omega
      cases done with
      | true =>
        rw [insert_sorted_at_oob_done v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · simp [hi_eq]
        · rw [hi_eq]; simp
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_oob_not_done v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          refine ⟨?_, ?_⟩
          · show (acc.val ++ #[x]).size = acc.val.size + (v.val.size - i.toNat) + 1
            rw [Array.size_append]; simp; omega
          · show vec_count (acc.val ++ #[x]) target (acc.val ++ #[x]).size + vec_count v.val target i.toNat
                = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                  + (if x = target then 1 else 0)
            have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            rw [h_size, vec_count_append_singleton, hi_eq]
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vec_succ_v :
          vec_count v.val target (i.toNat + 1) =
            (if v.val[i.toNat]'hi_lt = target then 1 else 0) + vec_count v.val target i.toNat :=
        vec_count_succ v.val target i.toNat hi_lt
      cases done with
      | true =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_push_size :
              (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 :=
            push_one_size acc _ h_acc
          have h_count_pushed :
              vec_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                (acc.val.size + 1) =
              vec_count acc.val target acc.val.size +
                (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
            show vec_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
            exact vec_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
          have ih_app := ih v x (i + 1) true (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
            h_meas h_i1_le hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
          rw [h_push_size] at h_size_eq h_count_eq
          simp only [if_true, if_pos rfl] at h_size_eq h_count_eq
          refine ⟨?_, ?_⟩
          · simp only [if_true, if_pos rfl]; rw [h_size_eq]
            have : 0 < v.val.size - i.toNat := by omega
            omega
          · simp only [if_true, if_pos rfl]
            rw [h_count_pushed] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_xi : lex_le_u64 x (v.val[i.toNat]'hi_lt)
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · have h_acc_e : acc.val.size + 1 < USize64.size := by omega
            have h_acc_v : (push_one acc x h_acc_e).val.size + 1 < USize64.size := by
              rw [push_one_size]; omega
            rw [insert_sorted_at_step_insert v x i acc hi_lt h_xi h_acc] at hres
            have h_push2_size :
                (push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val.size
                  = acc.val.size + 2 := by
              rw [push_one_size, push_one_size]
            have h_count_pushed_x :
                vec_count (push_one acc x h_acc_e).val target (acc.val.size + 1) =
                vec_count acc.val target acc.val.size +
                  (if x = target then 1 else 0) := by
              show vec_count (acc.val ++ #[x]) target (acc.val.size + 1) = _
              exact vec_count_append_singleton acc.val x target
            have h_count_pushed_2 :
                vec_count (push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val target
                  (acc.val.size + 2) =
                vec_count acc.val target acc.val.size +
                  (if x = target then 1 else 0) +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show vec_count ((push_one acc x h_acc_e).val ++ #[v.val[i.toNat]'hi_lt])
                    target (acc.val.size + 2) = _
              have h_p1_size : (push_one acc x h_acc_e).val.size = acc.val.size + 1 :=
                push_one_size acc x h_acc_e
              have h_lemma :
                  vec_count ((push_one acc x h_acc_e).val ++ #[v.val[i.toNat]'hi_lt])
                    target ((push_one acc x h_acc_e).val.size + 1) =
                  vec_count (push_one acc x h_acc_e).val target (push_one acc x h_acc_e).val.size +
                    (if v.val[i.toNat]'hi_lt = target then 1 else 0) :=
                vec_count_append_singleton (push_one acc x h_acc_e).val (v.val[i.toNat]'hi_lt) target
              rw [h_p1_size] at h_lemma
              rw [h_lemma, h_count_pushed_x]
            have ih_app := ih v x (i + 1) true
              (push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v)
              r target h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push2_size] at h_size_eq h_count_eq
            rw [if_pos (rfl : true = true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed_2] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            by_cases h_acc_e : acc.val.size + 1 < USize64.size
            · have h_big : USize64.size ≤ acc.val.size + 2 := by omega
              rw [insert_sorted_at_step_insert_fail_v v x i acc hi_lt h_xi h_acc_e h_big] at hres
              cases hres
            · have h_big : USize64.size ≤ acc.val.size + 1 := by omega
              rw [insert_sorted_at_step_insert_fail_x v x i acc hi_lt h_xi h_big] at hres
              cases hres
        · have h_lt : lex_lt_u64 (v.val[i.toNat]'hi_lt) x := lex_lt_of_not_le _ _ h_xi
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_push_size :
                (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 :=
              push_one_size acc _ h_acc
            have h_count_pushed :
                vec_count (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val target
                  (acc.val.size + 1) =
                vec_count acc.val target acc.val.size +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show vec_count (acc.val ++ #[v.val[i.toNat]'hi_lt]) target (acc.val.size + 1) = _
              exact vec_count_append_singleton acc.val (v.val[i.toNat]'hi_lt) target
            have ih_app := ih v x (i + 1) false (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
              h_meas h_i1_le hres
            rw [h_i1] at ih_app
            obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
            rw [h_push_size] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true)] at h_size_eq h_count_eq
            rw [if_neg (Bool.false_ne_true), if_neg (Bool.false_ne_true)]
            rw [h_count_pushed] at h_count_eq
            rw [h_vec_succ_v] at h_count_eq
            refine ⟨?_, ?_⟩
            · rw [h_size_eq]
              have : 0 < v.val.size - i.toNat := by omega
              omega
            · omega
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-! ## Sortedness preservation for `insert_sorted_at`. -/

private theorem insert_sorted_at_sorted (v : RustSlice u64) (x : u64)
    (h_v_sorted : sorted_lex v.val) :
    ∀ (n : Nat) (i : usize) (done : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_115_max_fill_count.insert_sorted_at v x i done acc = RustM.ok r →
      sorted_lex acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : i.toNat < v.val.size),
          lex_le_u64 (acc.val[k]'hk) (v.val[i.toNat]'hi_lt)) →
      (done = false →
          ∀ (k : Nat) (hk : k < acc.val.size), lex_le_u64 (acc.val[k]'hk) x) →
      sorted_lex r.val := by
  intro n
  induction n with
  | zero =>
    intro i done acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases done with
    | true =>
      rw [insert_sorted_at_oob_done v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_sorted_at_oob_not_done v x i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show sorted_lex (acc.val ++ #[x])
        apply sorted_lex_append_singleton acc.val x h_acc_sorted
        exact h_acc_le_x rfl
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_sorted_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i done acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_x
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases done with
      | true =>
        rw [insert_sorted_at_oob_done v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_acc_sorted
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_oob_not_done v x i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show sorted_lex (acc.val ++ #[x])
          apply sorted_lex_append_singleton acc.val x h_acc_sorted
          exact h_acc_le_x rfl
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      cases done with
      | true =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_sorted_at_step_pass v x i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_new_sorted : sorted_lex (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
            apply sorted_lex_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
            intro k hk
            exact h_acc_le_vi k hk hi_lt
          have h_new_le_vi :
              ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                (hi_i1 : (i + 1).toNat < v.val.size),
                lex_le_u64 ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk)
                  (v.val[(i + 1).toNat]'hi_i1) := by
            intro k hk hi_i1
            rw [Array.size_append] at hk
            have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
            have h_v_step : lex_le_u64 (v.val[i.toNat]'hi_lt) (v.val[(i + 1).toNat]'hi_i1) := by
              have h_le_idx : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
              exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le_idx
            by_cases h_k_lt : k < acc.val.size
            · rw [Array.getElem_append_left h_k_lt]
              exact lex_le_u64_trans _ _ _ (h_acc_le_vi k h_k_lt hi_lt) h_v_step
            · have h_k_ge : acc.val.size ≤ k := by omega
              rw [Array.getElem_append_right h_k_ge]
              have h_idx : k - acc.val.size = 0 := by omega
              have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                rw [h_one]; omega
              rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                      = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
              exact h_v_step
          exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
            (fun h => by cases h)
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_sorted_at_step_pass_fail v x i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_xi : lex_le_u64 x (v.val[i.toNat]'hi_lt)
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · have h_acc_e : acc.val.size + 1 < USize64.size := by omega
            have h_acc_v : (push_one acc x h_acc_e).val.size + 1 < USize64.size := by
              rw [push_one_size]; omega
            rw [insert_sorted_at_step_insert v x i acc hi_lt h_xi h_acc] at hres
            have h_p1 : sorted_lex (acc.val ++ #[x]) := by
              apply sorted_lex_append_singleton acc.val x h_acc_sorted
              exact h_acc_le_x rfl
            have h_p1_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[x]).size),
                  lex_le_u64 ((acc.val ++ #[x])[k]'hk) (v.val[i.toNat]'hi_lt) := by
              intro k hk
              rw [Array.size_append] at hk
              have h_one : (#[x] : Array u64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_vi k h_k_lt hi_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[x] : Array u64).size := by rw [h_one]; omega
                rw [show ((#[x] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[x] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_xi
            have h_p2_sorted : sorted_lex ((acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt]) :=
              sorted_lex_append_singleton _ _ h_p1 h_p1_le_vi
            have h_new_sorted :
                sorted_lex (push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val :=
              h_p2_sorted
            have h_new_le_vi :
                ∀ (k : Nat)
                  (hk : k < (push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val.size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  lex_le_u64
                    ((push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val[k]'hk)
                    (v.val[(i + 1).toNat]'hi_i1) := by
              intro k hk hi_i1
              have h_v_step : lex_le_u64 (v.val[i.toNat]'hi_lt) (v.val[(i + 1).toNat]'hi_i1) := by
                have h_le_idx : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le_idx
              have h_pp_size :
                  (push_one (push_one acc x h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val.size
                    = acc.val.size + 2 := by
                rw [push_one_size, push_one_size]
              have hk' : k < acc.val.size + 2 := by rw [h_pp_size] at hk; exact hk
              show lex_le_u64
                  (((acc.val ++ #[x]) ++ #[v.val[i.toNat]'hi_lt])[k]'hk)
                  (v.val[(i + 1).toNat]'hi_i1)
              have h_outer_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              have h_p1_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
                rw [Array.size_append]; rfl
              by_cases h_k_lt : k < (acc.val ++ #[x]).size
              · rw [Array.getElem_append_left h_k_lt]
                exact lex_le_u64_trans _ _ _ (h_p1_le_vi k h_k_lt) h_v_step
              · have h_k_ge : (acc.val ++ #[x]).size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - (acc.val ++ #[x]).size = 0 := by
                  rw [h_p1_size]; omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_outer_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - (acc.val ++ #[x]).size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_v_step
            exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
              (fun h => by cases h)
          · exfalso
            by_cases h_acc_e : acc.val.size + 1 < USize64.size
            · have h_big : USize64.size ≤ acc.val.size + 2 := by omega
              rw [insert_sorted_at_step_insert_fail_v v x i acc hi_lt h_xi h_acc_e h_big] at hres
              cases hres
            · have h_big : USize64.size ≤ acc.val.size + 1 := by omega
              rw [insert_sorted_at_step_insert_fail_x v x i acc hi_lt h_xi h_big] at hres
              cases hres
        · have h_lt : lex_lt_u64 (v.val[i.toNat]'hi_lt) x := lex_lt_of_not_le _ _ h_xi
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_sorted_at_step_pass v x i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_new_sorted : sorted_lex (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
              apply sorted_lex_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
              intro k hk
              exact h_acc_le_vi k hk hi_lt
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  lex_le_u64 ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk)
                    (v.val[(i + 1).toNat]'hi_i1) := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              have h_v_step : lex_le_u64 (v.val[i.toNat]'hi_lt) (v.val[(i + 1).toNat]'hi_i1) := by
                have h_le_idx : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le_idx
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact lex_le_u64_trans _ _ _ (h_acc_le_vi k h_k_lt hi_lt) h_v_step
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_v_step
            have h_new_le_x :
                false = false → ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size),
                  lex_le_u64 ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk) x := by
              intro _ k hk
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_x rfl k h_k_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                exact lex_lt_u64_imp_le _ _ h_lt
            exact ih (i + 1) false _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi h_new_le_x
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_sorted_at_step_pass_fail v x i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-! ## `insert_sorted` wrappers (from empty acc, starting from i = 0). -/

private theorem insert_sorted_inv (v : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64)
    (hres : clever_115_max_fill_count.insert_sorted v x = RustM.ok r) :
    r.val.size = v.val.size + 1 ∧
    vec_count r.val target r.val.size =
      vec_count v.val target v.val.size + (if x = target then 1 else 0) := by
  unfold clever_115_max_fill_count.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have inv := insert_sorted_at_inv v.val.size v x (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r target h_meas h_le hres
  obtain ⟨h_size_eq, h_count_eq⟩ := inv
  have h_empty_size : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
  rw [h_empty_size, h_zero_toNat] at h_size_eq
  rw [h_empty_size, h_zero_toNat] at h_count_eq
  have h_empty_count : vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val target 0 = 0 := rfl
  refine ⟨?_, ?_⟩
  · rw [h_size_eq]; simp
  · rw [h_empty_count] at h_count_eq
    have h_total_zero : vec_count v.val target 0 = 0 := rfl
    rw [h_total_zero] at h_count_eq
    simp at h_count_eq
    omega

private theorem insert_sorted_sorted (v : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_115_max_fill_count.insert_sorted v x = RustM.ok r)
    (h_v_sorted : sorted_lex v.val) :
    sorted_lex r.val := by
  unfold clever_115_max_fill_count.insert_sorted at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_toNat]; omega
  have h_empty_sorted : sorted_lex ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_vi :
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size)
        (_ : (0 : usize).toNat < v.val.size),
      lex_le_u64 (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k]'hk)
        (v.val[(0 : usize).toNat]'(by assumption)) := by
    intro k hk _
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_x : false = false →
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size),
      lex_le_u64 (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k]'hk) x := by
    intro _ k hk
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  exact insert_sorted_at_sorted v x h_v_sorted v.val.size (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres h_empty_sorted h_empty_le_vi h_empty_le_x

/-! ## `sort_at` OOB + step lemmas. -/

private theorem sort_at_oob (l : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_115_max_fill_count.sort_at l i acc = RustM.ok acc := by
  unfold clever_115_max_fill_count.sort_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem sort_at_step (l : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size) :
    clever_115_max_fill_count.sort_at l i acc =
      (do
        let acc' ← clever_115_max_fill_count.insert_sorted acc (l.val[i.toNat]'hi)
        clever_115_max_fill_count.sort_at l (i + 1) acc') := by
  conv => lhs; unfold clever_115_max_fill_count.sort_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx]
  rw [h_add]
  simp only [RustM_ok_bind]

/-! ## Invariants for `sort_at`: size, vec_count, sortedness. -/

private theorem sort_at_inv :
    ∀ (n : Nat) (l : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_115_max_fill_count.sort_at l i acc = RustM.ok r →
      r.val.size = acc.val.size + (l.val.size - i.toNat) ∧
      vec_count r.val target r.val.size + vec_count l.val target i.toNat =
        vec_count acc.val target acc.val.size + vec_count l.val target l.val.size := by
  intro n
  induction n with
  | zero =>
    intro l i acc r target hm hi_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [hi_eq]; omega
    · rw [hi_eq]
  | succ n ih =>
    intro l i acc r target hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · rw [hi_eq]; omega
      · rw [hi_eq]
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vec_succ_l :
          vec_count l.val target (i.toNat + 1) =
            (if l.val[i.toNat]'hi_lt = target then 1 else 0) + vec_count l.val target i.toNat :=
        vec_count_succ l.val target i.toNat hi_lt
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_115_max_fill_count.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                       clever_115_max_fill_count.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_115_max_fill_count.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_115_max_fill_count.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_ins_inv := insert_sorted_inv acc (l.val[i.toNat]'hi_lt) acc' target h_ins_ok
          obtain ⟨h_acc'_size, h_acc'_count⟩ := h_ins_inv
          have ih_app := ih l (i + 1) acc' r target h_meas h_i1_le hres
          rw [h_i1] at ih_app
          obtain ⟨h_size_eq, h_count_eq⟩ := ih_app
          rw [h_acc'_size] at h_size_eq
          rw [h_acc'_count] at h_count_eq
          rw [h_vec_succ_l] at h_count_eq
          refine ⟨?_, ?_⟩
          · rw [h_size_eq]; omega
          · omega

private theorem sort_at_sorted :
    ∀ (n : Nat) (l : RustSlice u64)
      (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_115_max_fill_count.sort_at l i acc = RustM.ok r →
      sorted_lex acc.val →
      sorted_lex r.val := by
  intro n
  induction n with
  | zero =>
    intro l i acc r hm hi_le hres h_acc_sorted
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [sort_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_sorted
  | succ n ih =>
    intro l i acc r hm hi_le hres h_acc_sorted
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [sort_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      rw [sort_at_step l i acc hi_lt] at hres
      generalize h_ins : clever_115_max_fill_count.insert_sorted acc (l.val[i.toNat]'hi_lt) = ins_res at hres
      cases ins_res with
      | none =>
        exfalso
        have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                       clever_115_max_fill_count.sort_at l (i + 1) acc')
                  = RustM.ok r := hres
        cases hh
      | some res' =>
        cases res' with
        | error e =>
          exfalso
          have hh : (do let acc' ← (some (Except.error e) :
                                      RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_115_max_fill_count.sort_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | ok acc' =>
          have h_ins_ok : clever_115_max_fill_count.insert_sorted acc (l.val[i.toNat]'hi_lt) = RustM.ok acc' := h_ins
          simp only [RustM_ok_bind] at hres
          have h_acc'_sorted : sorted_lex acc'.val :=
            insert_sorted_sorted acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok h_acc_sorted
          exact ih l (i + 1) acc' r h_meas h_i1_le hres h_acc'_sorted

/-! ## Obligation theorems. -/

/-- Anchor: an empty input slice yields a successful empty output. -/
theorem empty_input_yields_empty_output
    (l : RustSlice u64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_115_max_fill_count.sort_by_popcount l = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨(List.nil).toArray, by grind⟩, ?_, ?_⟩
  · unfold clever_115_max_fill_count.sort_by_popcount
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new]
    simp only [RustM_ok_bind]
    have h_zero_le : (0 : usize).toNat = 0 := rfl
    have h_oob : l.val.size ≤ (0 : usize).toNat := by rw [h_zero_le]; omega
    rw [sort_at_oob l (0 : usize) ⟨(List.nil).toArray, by grind⟩ h_oob]
  · rfl

/-- Postcondition (1/2): the output is a permutation of the input. -/
theorem output_is_permutation_of_input
    (l : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_115_max_fill_count.sort_by_popcount l = RustM.ok v)
    (target : u64) :
    vec_count v.val target v.val.size
      = vec_count l.val target l.val.size := by
  unfold clever_115_max_fill_count.sort_by_popcount at hres
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have inv := sort_at_inv l.val.size l (0 : usize)
                ⟨(List.nil).toArray, by grind⟩ v target h_meas h_le hres
  obtain ⟨h_size_eq, h_count_eq⟩ := inv
  rw [h_zero_le] at h_count_eq
  have h_l_zero : vec_count l.val target 0 = 0 := rfl
  have h_empty_size :
      ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
  rw [h_empty_size] at h_count_eq
  have h_empty_count_at_zero :
      vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val target 0 = 0 :=
    rfl
  rw [h_empty_count_at_zero, h_l_zero] at h_count_eq
  omega

/-- Postcondition (2/2): consecutive output entries are non-decreasing
    under the lexicographic key `(popcount, value)`. -/
theorem output_is_sorted_by_popcount_then_value
    (l : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_115_max_fill_count.sort_by_popcount l = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    popcount (v.val[k]'(Nat.lt_of_succ_lt hk))
        < popcount (v.val[k + 1]'hk)
    ∨ (popcount (v.val[k]'(Nat.lt_of_succ_lt hk))
          = popcount (v.val[k + 1]'hk)
        ∧ (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat
            ≤ (v.val[k + 1]'hk).toNat) := by
  unfold clever_115_max_fill_count.sort_by_popcount at hres
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ l.val.size := by rw [h_zero_le]; omega
  have h_empty_sorted : sorted_lex ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_v_sorted : sorted_lex v.val :=
    sort_at_sorted l.val.size l (0 : usize) ⟨(List.nil).toArray, by grind⟩ v
      h_meas h_le hres h_empty_sorted
  exact h_v_sorted k (k + 1) (Nat.lt_of_succ_lt hk) hk (Nat.le_succ _)

end Clever_115_max_fill_countObligations
