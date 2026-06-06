-- Companion obligations file for the `clever_103_unique_digits` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_103_unique_digits

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_103_unique_digitsObligations

/-! ## Specification oracles. -/

/-- Count occurrences of `target` among the first `k` entries of `s`. -/
private def vec_count (s : Array u64) (target : u64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-- Pure spec predicate: `n` has every decimal digit odd.  Matches the
    Rust `all_odd_digits` helper, which returns `false` on `n = 0`. -/
private def all_odd_digits_nat : Nat → Bool
  | 0     => false
  | n + 1 =>
      if (n + 1) % 10 % 2 = 0 then false
      else if (n + 1) / 10 = 0 then true
      else all_odd_digits_nat ((n + 1) / 10)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

/-- Lifted spec: `n : u64` has every decimal digit odd. -/
private def all_odd_digits (n : u64) : Bool := all_odd_digits_nat n.toNat

/-- Non-strict ascending order on a `u64` array. -/
private def sorted_asc (arr : Array u64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ ≤ k₂ → (arr[k₁]'h₁).toNat ≤ (arr[k₂]'h₂).toNat

/-! ## Standard scaffolding. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

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

/-! ## Sortedness lemmas. -/

private theorem sorted_asc_empty : sorted_asc #[] := by
  intro k₁ k₂ h₁ _ _
  have : (#[] : Array u64).size = 0 := rfl
  omega

private theorem sorted_asc_append_singleton (acc : Array u64) (y : u64)
    (h_acc : sorted_asc acc)
    (h_le : ∀ (k : Nat) (hk : k < acc.size), (acc[k]'hk).toNat ≤ y.toNat) :
    sorted_asc (acc ++ #[y]) := by
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
      show (acc[k₁]'h_k1_lt).toNat ≤ y.toNat
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
    exact Nat.le_refl _

/-! ## Correctness of `has_even_digit_at`.

    Boolean oracle that exactly mirrors the Rust function on `Nat`. -/

/-- Pure spec for `has_even_digit_at`: true iff some decimal digit of `n` is even.
    Defined in `if h : 0 < n then ... else ...` form so that `unfold` + `dif_pos`/`dif_neg`
    yields the step equations cleanly. -/
private def has_even_digit_at_nat (n : Nat) : Bool :=
  if h : 0 < n then
    if n % 10 % 2 = 0 then true else has_even_digit_at_nat (n / 10)
  else false
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-- Successor equation for `has_even_digit_at_nat`. -/
private theorem has_even_digit_at_nat_succ_eq (n : Nat) (h : 0 < n) :
    has_even_digit_at_nat n =
      if n % 10 % 2 = 0 then true else has_even_digit_at_nat (n / 10) := by
  conv => lhs; unfold has_even_digit_at_nat
  rw [dif_pos h]

/-- Zero equation for `has_even_digit_at_nat`. -/
private theorem has_even_digit_at_nat_zero_eq (n : Nat) (h : ¬ 0 < n) :
    has_even_digit_at_nat n = false := by
  conv => lhs; unfold has_even_digit_at_nat
  rw [dif_neg h]

private theorem has_even_digit_at_nat_zero : has_even_digit_at_nat 0 = false :=
  has_even_digit_at_nat_zero_eq 0 (by decide)

/-- Unfolding step for `all_odd_digits_nat` at successor. -/
private theorem all_odd_digits_nat_succ_eq (k : Nat) :
    all_odd_digits_nat (k + 1) =
      if (k + 1) % 10 % 2 = 0 then false
      else if (k + 1) / 10 = 0 then true
      else all_odd_digits_nat ((k + 1) / 10) := by
  conv => lhs; unfold all_odd_digits_nat

private theorem all_odd_digits_nat_zero : all_odd_digits_nat 0 = false := by
  conv => lhs; unfold all_odd_digits_nat

/-- For `n > 0`, `has_even_digit_at_nat n = ! all_odd_digits_nat n`. -/
private theorem has_even_digit_at_nat_eq_not_all_odd_aux :
    ∀ (m : Nat) (n : Nat), n ≤ m → 0 < n →
      has_even_digit_at_nat n = ! all_odd_digits_nat n := by
  intro m
  induction m with
  | zero =>
    intro n hm hn; omega
  | succ m ih =>
    intro n hm hn
    have h_succ_eq : has_even_digit_at_nat n =
      if n % 10 % 2 = 0 then true else has_even_digit_at_nat (n / 10) :=
      has_even_digit_at_nat_succ_eq n hn
    cases n with
    | zero => omega
    | succ k =>
      have h_aod_eq := all_odd_digits_nat_succ_eq k
      by_cases h_mod : (k + 1) % 10 % 2 = 0
      · rw [h_succ_eq, if_pos h_mod, h_aod_eq, if_pos h_mod]
        rfl
      · rw [h_succ_eq, if_neg h_mod, h_aod_eq, if_neg h_mod]
        by_cases h_div : (k + 1) / 10 = 0
        · rw [if_pos h_div, h_div, has_even_digit_at_nat_zero]
          rfl
        · rw [if_neg h_div]
          have h_div_pos : 0 < (k + 1) / 10 := Nat.pos_of_ne_zero h_div
          have h_div_lt : (k + 1) / 10 < k + 1 :=
            Nat.div_lt_self (Nat.succ_pos _) (by decide)
          have h_div_le : (k + 1) / 10 ≤ m := by omega
          exact ih ((k + 1) / 10) h_div_le h_div_pos

private theorem has_even_digit_at_nat_eq_not_all_odd
    (n : Nat) (hn : 0 < n) :
    has_even_digit_at_nat n = ! all_odd_digits_nat n :=
  has_even_digit_at_nat_eq_not_all_odd_aux n n (Nat.le_refl _) hn

/-- u64 mod reduction (when the divisor is non-zero). -/
private theorem u64_mod_ok (n d : u64) (hd : d ≠ 0) :
    (n %? d : RustM u64) = RustM.ok (n % d) := by
  show (rust_primitives.ops.arith.Rem.rem n d : RustM u64) = _
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n % d)) = _
  rw [if_neg hd]; rfl

/-- u64 div reduction (when the divisor is non-zero). -/
private theorem u64_div_ok (n d : u64) (hd : d ≠ 0) :
    (n /? d : RustM u64) = RustM.ok (n / d) := by
  show (rust_primitives.ops.arith.Div.div n d : RustM u64) = _
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n / d)) = _
  rw [if_neg hd]; rfl

private theorem u64_toNat_div (a b : u64) : (a / b).toNat = a.toNat / b.toNat :=
  UInt64.toNat_div a b

private theorem u64_toNat_mod (a b : u64) : (a % b).toNat = a.toNat % b.toNat :=
  UInt64.toNat_mod a b

/-- The eq-test on `u64` zero reduces to a `decide`. -/
private theorem u64_eq_zero_test (n : u64) :
    (n ==? (0 : u64) : RustM Bool) = RustM.ok (decide (n = 0)) := by
  show (rust_primitives.cmp.eq n (0 : u64) : RustM Bool) = _
  show pure (n == (0 : u64) : Bool) = _
  rw [show (n == (0 : u64) : Bool) = decide (n = 0) from by
    by_cases h : n = 0
    · rw [h]; decide
    · simp [h]]
  rfl

/-- Helper: derive `0 < n.toNat` from `n ≠ 0`. -/
private theorem u64_toNat_pos_of_ne_zero (n : u64) (h : n ≠ 0) : 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with h_zero | h_pos
  · exfalso; apply h
    have : n.toNat = (0 : u64).toNat := by rw [h_zero]; rfl
    exact UInt64.toNat_inj.mp this
  · exact h_pos

/-- `has_even_digit_at` succeeds for every `u64 n` with the spec value. -/
private theorem has_even_digit_at_correct :
    ∀ (m : Nat) (n : u64),
      n.toNat ≤ m →
      clever_103_unique_digits.has_even_digit_at n
        = RustM.ok (has_even_digit_at_nat n.toNat) := by
  intro m
  induction m with
  | zero =>
    intro n hm
    have h_zero : n.toNat = 0 := by omega
    have h_n_eq : n = 0 := by
      have : n.toNat = (0 : u64).toNat := by rw [h_zero]; rfl
      exact UInt64.toNat_inj.mp this
    rw [h_n_eq]
    show clever_103_unique_digits.has_even_digit_at 0 = _
    unfold clever_103_unique_digits.has_even_digit_at
    have h_eq_zero : ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := by
      show pure ((0 : u64) == (0 : u64) : Bool) = RustM.ok true
      rfl
    simp only [h_eq_zero, RustM_ok_bind, ↓reduceIte]
    have h0 : (0 : u64).toNat = 0 := rfl
    rw [h0, has_even_digit_at_nat_zero]
    rfl
  | succ m ih =>
    intro n hm
    by_cases hn_zero : n = 0
    · rw [hn_zero]
      show clever_103_unique_digits.has_even_digit_at 0 = _
      unfold clever_103_unique_digits.has_even_digit_at
      have h_eq_zero : ((0 : u64) ==? (0 : u64) : RustM Bool) = RustM.ok true := by
        show pure ((0 : u64) == (0 : u64) : Bool) = RustM.ok true
        rfl
      simp only [h_eq_zero, RustM_ok_bind, ↓reduceIte]
      have h0 : (0 : u64).toNat = 0 := rfl
      rw [h0, has_even_digit_at_nat_zero]
      rfl
    · have hn_pos : 0 < n.toNat := u64_toNat_pos_of_ne_zero n hn_zero
      unfold clever_103_unique_digits.has_even_digit_at
      rw [u64_eq_zero_test]
      have h_dec_ne : decide (n = 0) = false := decide_eq_false hn_zero
      simp only [RustM_ok_bind, h_dec_ne, Bool.false_eq_true, ↓reduceIte]
      rw [u64_mod_ok n 10 (by decide)]
      simp only [RustM_ok_bind]
      rw [u64_mod_ok (n % 10) 2 (by decide)]
      simp only [RustM_ok_bind]
      rw [u64_eq_zero_test]
      simp only [RustM_ok_bind]
      have h_mod_nat : ((n % 10) % 2).toNat = n.toNat % 10 % 2 := by
        rw [u64_toNat_mod (n % 10) 2, u64_toNat_mod n 10]
        rfl
      by_cases h_mod : (n % 10) % 2 = 0
      · have h_dec_mod : decide ((n % 10) % 2 = (0 : u64)) = true := decide_eq_true h_mod
        rw [h_dec_mod]
        simp only [↓reduceIte]
        have h_mod_nat_zero : n.toNat % 10 % 2 = 0 := by
          have : ((n % 10) % 2).toNat = (0 : u64).toNat := by rw [h_mod]
          rw [h_mod_nat] at this
          have h0 : (0 : u64).toNat = 0 := rfl
          rw [h0] at this; exact this
        have h_eq : has_even_digit_at_nat n.toNat = true := by
          rw [has_even_digit_at_nat_succ_eq n.toNat hn_pos, if_pos h_mod_nat_zero]
        rw [h_eq]; rfl
      · have h_dec_mod : decide ((n % 10) % 2 = (0 : u64)) = false := decide_eq_false h_mod
        rw [h_dec_mod]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [u64_div_ok n 10 (by decide)]
        simp only [RustM_ok_bind]
        have h_mod_nat_ne : n.toNat % 10 % 2 ≠ 0 := by
          intro hh
          apply h_mod
          have : ((n % 10) % 2).toNat = (0 : u64).toNat := by
            rw [h_mod_nat]
            have h0 : (0 : u64).toNat = 0 := rfl
            rw [h0]; exact hh
          exact UInt64.toNat_inj.mp this
        have h_div_lt : (n / 10).toNat ≤ m := by
          have h_div_lt_n : n.toNat / 10 < n.toNat :=
            Nat.div_lt_self hn_pos (by decide)
          rw [u64_toNat_div n 10]
          have h_ten : (10 : u64).toNat = 10 := rfl
          rw [h_ten]; omega
        have ih_app := ih (n / 10) h_div_lt
        rw [u64_toNat_div n 10] at ih_app
        have h_ten : (10 : u64).toNat = 10 := rfl
        rw [h_ten] at ih_app
        rw [ih_app]
        have h_eq : has_even_digit_at_nat n.toNat =
            has_even_digit_at_nat (n.toNat / 10) := by
          rw [has_even_digit_at_nat_succ_eq n.toNat hn_pos, if_neg h_mod_nat_ne]
        rw [h_eq]

/-- `has_even_digit n` succeeds for every `u64`, returning `! all_odd_digits n`. -/
private theorem has_even_digit_correct (n : u64) :
    clever_103_unique_digits.has_even_digit n
      = RustM.ok (! all_odd_digits n) := by
  unfold clever_103_unique_digits.has_even_digit
  rw [u64_eq_zero_test]
  by_cases hn_zero : n = 0
  · rw [hn_zero]
    have h_dec_zero : decide ((0 : u64) = 0) = true := decide_eq_true rfl
    simp only [RustM_ok_bind, h_dec_zero, ↓reduceIte]
    show RustM.ok true = RustM.ok (! all_odd_digits 0)
    have h_aod_zero : all_odd_digits 0 = false := by
      show all_odd_digits_nat (0 : u64).toNat = false
      have h0 : (0 : u64).toNat = 0 := rfl
      rw [h0, all_odd_digits_nat_zero]
    rw [h_aod_zero]; rfl
  · have h_dec_ne : decide (n = 0) = false := decide_eq_false hn_zero
    simp only [RustM_ok_bind, h_dec_ne, Bool.false_eq_true, ↓reduceIte]
    have hn_pos : 0 < n.toNat := u64_toNat_pos_of_ne_zero n hn_zero
    have h_at := has_even_digit_at_correct n.toNat n (Nat.le_refl _)
    rw [h_at]
    show RustM.ok (has_even_digit_at_nat n.toNat) =
      RustM.ok (! all_odd_digits n)
    show RustM.ok (has_even_digit_at_nat n.toNat) =
      RustM.ok (! all_odd_digits_nat n.toNat)
    rw [has_even_digit_at_nat_eq_not_all_odd n.toNat hn_pos]

/-! ## OOB / step / fail lemmas for `insert_asc_at`.

    Adapted from `clever_087_sort_array` to match the target's "two consecutive
    single-element pushes" pattern in the insert branch (vs. `clever_087`'s
    single 2-element chunk push). -/

private theorem insert_asc_at_oob_inserted (v : RustSlice u64) (e : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_103_unique_digits.insert_asc_at v i e true acc = RustM.ok acc := by
  unfold clever_103_unique_digits.insert_asc_at
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

private theorem insert_asc_at_oob_not_inserted (v : RustSlice u64) (e : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_103_unique_digits.insert_asc_at v i e false acc =
      RustM.ok (push_one acc e h_acc) := by
  unfold clever_103_unique_digits.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size :
      acc.val.size + (#[e] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[e], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc e h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[e] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[e], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  rfl

private theorem insert_asc_at_oob_not_inserted_fail (v : RustSlice u64) (e : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_103_unique_digits.insert_asc_at v i e false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_103_unique_digits.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size_neg :
      ¬ acc.val.size + (#[e] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[e], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte,
             rust_primitives.hax.logical_op.not, Bool.not_false]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[e] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[e], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- In the step-insert branch the function pushes `e`, then pushes `v[i]`, and
    recurses with `done = true`. Two consecutive size-1 extensions. -/
private theorem insert_asc_at_step_insert (v : RustSlice u64) (e : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toNat ≥ e.toNat)
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_103_unique_digits.insert_asc_at v i e false acc =
      clever_103_unique_digits.insert_asc_at v (i + 1) e true
        (push_one (push_one acc e (by omega)) (v.val[i.toNat]'hi)
          (by rw [push_one_size]; omega)) := by
  conv => lhs; unfold clever_103_unique_digits.insert_asc_at
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
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ e)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ e) = (e ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]
    exact h_vi
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_acc_e : acc.val.size + 1 < USize64.size := by omega
  have h_app_size_e :
      acc.val.size + (#[e] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc_e
  have h_extend_e :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[e], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc e h_acc_e) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_e]; rfl
  have h_acc_v : (push_one acc e h_acc_e).val.size + 1 < USize64.size := by
    rw [push_one_size]; omega
  have h_app_size_v :
      (push_one acc e h_acc_e).val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show (push_one acc e h_acc_e).val.size + 1 < USize64.size; exact h_acc_v
  have h_extend_v :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global (push_one acc e h_acc_e)
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi) h_acc_v) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_v]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true,
             Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[e] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[e], one_lt_usize_size⟩ from rfl]
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

/-- Failure variant: first push (of `e`) overflows. -/
private theorem insert_asc_at_step_insert_fail_e (v : RustSlice u64) (e : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toNat ≥ e.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_103_unique_digits.insert_asc_at v i e false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_103_unique_digits.insert_asc_at
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
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ e)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ e) = (e ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]
    exact h_vi
  have h_app_size_neg :
      ¬ acc.val.size + (#[e] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[e], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true,
             Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[e] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[e], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-- Failure variant: first push (of `e`) succeeds, second push (of `v[i]`) overflows. -/
private theorem insert_asc_at_step_insert_fail_v (v : RustSlice u64) (e : u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_vi : (v.val[i.toNat]'hi).toNat ≥ e.toNat)
    (h_acc_e : acc.val.size + 1 < USize64.size)
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_103_unique_digits.insert_asc_at v i e false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_103_unique_digits.insert_asc_at
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
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ e)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ e) = (e ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]
    exact h_vi
  have h_app_size_e :
      acc.val.size + (#[e] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc_e
  have h_extend_e :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[e], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc e h_acc_e) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_e]; rfl
  have h_app_size_v_neg :
      ¬ (push_one acc e h_acc_e).val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    rw [push_one_size]
    show ¬ acc.val.size + 1 + 1 < USize64.size; omega
  have h_extend_v_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global (push_one acc e h_acc_e)
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_v_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true,
             Bool.true_and, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[e] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[e], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_e]
  simp only [RustM_ok_bind]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_v_fail]
  rfl

/-- Pass step: either done=true, or v[i].toNat < e.toNat. Push v[i] once and recurse. -/
private theorem insert_asc_at_step_pass (v : RustSlice u64) (e : u64) (i : usize)
    (done : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : done = true ∨ (v.val[i.toNat]'hi).toNat < e.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_103_unique_digits.insert_asc_at v i e done acc =
      clever_103_unique_digits.insert_asc_at v (i + 1) e done
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_103_unique_digits.insert_asc_at
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
  have h_and_false : ((!done) && decide ((v.val[i.toNat]'hi) ≥ e)) = false := by
    cases h_skip with
    | inl h_done_true => subst h_done_true; rfl
    | inr h_lt =>
      have h_not_ge : ¬ ((v.val[i.toNat]'hi) ≥ e) := by
        rw [show ((v.val[i.toNat]'hi) ≥ e) = (e ≤ (v.val[i.toNat]'hi)) from rfl]
        rw [UInt64.le_iff_toNat_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
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
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and]
  rw [h_and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  simp only [RustM_ok_bind]
  rw [h_add]
  simp only [RustM_ok_bind]

private theorem insert_asc_at_step_pass_fail (v : RustSlice u64) (e : u64) (i : usize)
    (done : Bool) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < v.val.size)
    (h_skip : done = true ∨ (v.val[i.toNat]'hi).toNat < e.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_103_unique_digits.insert_asc_at v i e done acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_103_unique_digits.insert_asc_at
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
  have h_and_false : ((!done) && decide ((v.val[i.toNat]'hi) ≥ e)) = false := by
    cases h_skip with
    | inl h_done_true => subst h_done_true; rfl
    | inr h_lt =>
      have h_not_ge : ¬ ((v.val[i.toNat]'hi) ≥ e) := by
        rw [show ((v.val[i.toNat]'hi) ≥ e) = (e ≤ (v.val[i.toNat]'hi)) from rfl]
        rw [UInt64.le_iff_toNat_le]
        omega
      rw [decide_eq_false h_not_ge]
      exact Bool.and_false _
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
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not,
             rust_primitives.hax.logical_op.and]
  rw [h_and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## Invariants for `insert_asc_at`: size and vec_count. -/

private theorem insert_asc_at_inv :
    ∀ (n : Nat) (v : RustSlice u64) (e : u64) (i : usize) (done : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_103_unique_digits.insert_asc_at v i e done acc = RustM.ok r →
      r.val.size = acc.val.size + (v.val.size - i.toNat) + (if done then 0 else 1) ∧
      vec_count r.val target r.val.size + vec_count v.val target i.toNat =
        vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
          + (if done then 0 else (if e = target then 1 else 0)) := by
  intro n
  induction n with
  | zero =>
    intro v e i done acc r target hm hi_le hres
    have hi_ge : v.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = v.val.size := by omega
    cases done with
    | true =>
      rw [insert_asc_at_oob_inserted v e i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · simp [hi_eq]
      · rw [hi_eq]; simp
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_asc_at_oob_not_inserted v e i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · show (acc.val ++ #[e]).size = acc.val.size + (v.val.size - i.toNat) + 1
          rw [Array.size_append]; simp; omega
        · show vec_count (acc.val ++ #[e]) target (acc.val ++ #[e]).size + vec_count v.val target i.toNat
              = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                + (if e = target then 1 else 0)
          have h_size : (acc.val ++ #[e]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [h_size, vec_count_append_singleton, hi_eq]
          omega
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_asc_at_oob_not_inserted_fail v e i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v e i done acc r target hm hi_le hres
    by_cases hi_ge : v.val.size ≤ i.toNat
    · have hi_eq : i.toNat = v.val.size := by omega
      cases done with
      | true =>
        rw [insert_asc_at_oob_inserted v e i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        refine ⟨?_, ?_⟩
        · simp [hi_eq]
        · rw [hi_eq]; simp
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_oob_not_inserted v e i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          refine ⟨?_, ?_⟩
          · show (acc.val ++ #[e]).size = acc.val.size + (v.val.size - i.toNat) + 1
            rw [Array.size_append]; simp; omega
          · show vec_count (acc.val ++ #[e]) target (acc.val ++ #[e]).size + vec_count v.val target i.toNat
                = vec_count acc.val target acc.val.size + vec_count v.val target v.val.size
                  + (if e = target then 1 else 0)
            have h_size : (acc.val ++ #[e]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            rw [h_size, vec_count_append_singleton, hi_eq]
            omega
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_asc_at_oob_not_inserted_fail v e i acc hi_ge h_big] at hres
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
        · rw [insert_asc_at_step_pass v e i true acc hi_lt (Or.inl rfl) h_acc] at hres
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
          have ih_app := ih v e (i + 1) true (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
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
          rw [insert_asc_at_step_pass_fail v e i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi : (v.val[i.toNat]'hi_lt).toNat ≥ e.toNat
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · have h_acc_e : acc.val.size + 1 < USize64.size := by omega
            have h_acc_v : (push_one acc e h_acc_e).val.size + 1 < USize64.size := by
              rw [push_one_size]; omega
            rw [insert_asc_at_step_insert v e i acc hi_lt h_vi h_acc] at hres
            -- After the step, the new acc is push_one (push_one acc e _) v[i] _
            have h_push2_size :
                (push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val.size
                  = acc.val.size + 2 := by
              rw [push_one_size, push_one_size]
            have h_count_pushed_e :
                vec_count (push_one acc e h_acc_e).val target (acc.val.size + 1) =
                vec_count acc.val target acc.val.size +
                  (if e = target then 1 else 0) := by
              show vec_count (acc.val ++ #[e]) target (acc.val.size + 1) = _
              exact vec_count_append_singleton acc.val e target
            have h_count_pushed_2 :
                vec_count (push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val target
                  (acc.val.size + 2) =
                vec_count acc.val target acc.val.size +
                  (if e = target then 1 else 0) +
                  (if v.val[i.toNat]'hi_lt = target then 1 else 0) := by
              show vec_count ((push_one acc e h_acc_e).val ++ #[v.val[i.toNat]'hi_lt])
                    target (acc.val.size + 2) = _
              have h_p1_size : (push_one acc e h_acc_e).val.size = acc.val.size + 1 :=
                push_one_size acc e h_acc_e
              have h_app_size :
                  ((push_one acc e h_acc_e).val ++ #[v.val[i.toNat]'hi_lt]).size
                    = acc.val.size + 2 := by
                rw [Array.size_append, h_p1_size]; rfl
              have h_lemma :
                  vec_count ((push_one acc e h_acc_e).val ++ #[v.val[i.toNat]'hi_lt])
                    target ((push_one acc e h_acc_e).val.size + 1) =
                  vec_count (push_one acc e h_acc_e).val target (push_one acc e h_acc_e).val.size +
                    (if v.val[i.toNat]'hi_lt = target then 1 else 0) :=
                vec_count_append_singleton (push_one acc e h_acc_e).val (v.val[i.toNat]'hi_lt) target
              rw [h_p1_size] at h_lemma
              rw [h_lemma, h_count_pushed_e]
            have ih_app := ih v e (i + 1) true
              (push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v)
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
          · -- size overflow in the insert branch
            exfalso
            by_cases h_acc_e : acc.val.size + 1 < USize64.size
            · -- first push succeeds, second push overflows
              have h_big : USize64.size ≤ acc.val.size + 2 := by omega
              rw [insert_asc_at_step_insert_fail_v v e i acc hi_lt h_vi h_acc_e h_big] at hres
              cases hres
            · -- first push overflows
              have h_big : USize64.size ≤ acc.val.size + 1 := by omega
              rw [insert_asc_at_step_insert_fail_e v e i acc hi_lt h_vi h_big] at hres
              cases hres
        · have h_lt : (v.val[i.toNat]'hi_lt).toNat < e.toNat := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_pass v e i false acc hi_lt (Or.inr h_lt) h_acc] at hres
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
            have ih_app := ih v e (i + 1) false (push_one acc (v.val[i.toNat]'hi_lt) h_acc) r target
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
            rw [insert_asc_at_step_pass_fail v e i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-! ## Sortedness preservation for `insert_asc_at`. -/

private theorem insert_asc_at_sorted (v : RustSlice u64) (e : u64)
    (h_v_sorted : sorted_asc v.val) :
    ∀ (n : Nat) (i : usize) (done : Bool)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_103_unique_digits.insert_asc_at v i e done acc = RustM.ok r →
      sorted_asc acc.val →
      (∀ (k : Nat) (hk : k < acc.val.size) (hi_lt : i.toNat < v.val.size),
          (acc.val[k]'hk).toNat ≤ (v.val[i.toNat]'hi_lt).toNat) →
      (done = false →
          ∀ (k : Nat) (hk : k < acc.val.size), (acc.val[k]'hk).toNat ≤ e.toNat) →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro i done acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_e
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases done with
    | true =>
      rw [insert_asc_at_oob_inserted v e i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact h_acc_sorted
    | false =>
      by_cases h_acc : acc.val.size + 1 < USize64.size
      · rw [insert_asc_at_oob_not_inserted v e i acc hi_ge h_acc] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        show sorted_asc (acc.val ++ #[e])
        apply sorted_asc_append_singleton acc.val e h_acc_sorted
        exact h_acc_le_e rfl
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_asc_at_oob_not_inserted_fail v e i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro i done acc r hm hi_le hres h_acc_sorted h_acc_le_vi h_acc_le_e
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases done with
      | true =>
        rw [insert_asc_at_oob_inserted v e i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_acc_sorted
      | false =>
        by_cases h_acc : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_oob_not_inserted v e i acc hi_ge h_acc] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          show sorted_asc (acc.val ++ #[e])
          apply sorted_asc_append_singleton acc.val e h_acc_sorted
          exact h_acc_le_e rfl
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_asc_at_oob_not_inserted_fail v e i acc hi_ge h_big] at hres
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
        · rw [insert_asc_at_step_pass v e i true acc hi_lt (Or.inl rfl) h_acc] at hres
          have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
            apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
            intro k hk
            exact h_acc_le_vi k hk hi_lt
          have h_new_le_vi :
              ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                (hi_i1 : (i + 1).toNat < v.val.size),
                ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toNat
                  ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
            intro k hk hi_i1
            rw [Array.size_append] at hk
            have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
            by_cases h_k_lt : k < acc.val.size
            · rw [Array.getElem_append_left h_k_lt]
              have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
              have h_v_step : (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              omega
            · have h_k_ge : acc.val.size ≤ k := by omega
              rw [Array.getElem_append_right h_k_ge]
              have h_idx : k - acc.val.size = 0 := by omega
              have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                rw [h_one]; omega
              rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                      = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
              show (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat
              have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
              exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
          have h_pushed_size : (push_one acc (v.val[i.toNat]'hi_lt) h_acc).val.size = acc.val.size + 1 :=
            push_one_size acc _ h_acc
          exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
            (fun h => by cases h)
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_asc_at_step_pass_fail v e i true acc hi_lt (Or.inl rfl) h_big] at hres
          cases hres
      | false =>
        by_cases h_vi_ge : (v.val[i.toNat]'hi_lt).toNat ≥ e.toNat
        · by_cases h_acc : acc.val.size + 2 < USize64.size
          · have h_acc_e : acc.val.size + 1 < USize64.size := by omega
            have h_acc_v : (push_one acc e h_acc_e).val.size + 1 < USize64.size := by
              rw [push_one_size]; omega
            rw [insert_asc_at_step_insert v e i acc hi_lt h_vi_ge h_acc] at hres
            -- New acc: push_one (push_one acc e _) v[i] _
            -- Step 1 (push e): sorted(acc++[e]) requires acc[k] ≤ e for all k — given by h_acc_le_e false rfl.
            have h_p1 : sorted_asc (acc.val ++ #[e]) := by
              apply sorted_asc_append_singleton acc.val e h_acc_sorted
              exact h_acc_le_e rfl
            -- Step 2 (push v[i]): sorted((acc++[e])++[v[i]]) requires all k in (acc++[e]).size, (acc++[e])[k] ≤ v[i].
            have h_p1_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[e]).size),
                  ((acc.val ++ #[e])[k]'hk).toNat ≤ (v.val[i.toNat]'hi_lt).toNat := by
              intro k hk
              rw [Array.size_append] at hk
              have h_one : (#[e] : Array u64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                exact h_acc_k
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[e] : Array u64).size := by rw [h_one]; omega
                rw [show ((#[e] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[e] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                show e.toNat ≤ (v.val[i.toNat]'hi_lt).toNat
                exact h_vi_ge
            have h_p2_sorted : sorted_asc ((acc.val ++ #[e]) ++ #[v.val[i.toNat]'hi_lt]) :=
              sorted_asc_append_singleton _ _ h_p1 h_p1_le_vi
            -- Translate to push_one form.
            have h_new_sorted :
                sorted_asc (push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val :=
              h_p2_sorted
            -- New acc[k] ≤ v[i+1] for the recursion.
            have h_new_le_vi :
                ∀ (k : Nat)
                  (hk : k < (push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val.size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val[k]'hk).toNat
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
              intro k hk hi_i1
              have h_v_step : (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              -- Translate hk via the explicit `push_one_size` equation.
              have h_pp_size :
                  (push_one (push_one acc e h_acc_e) (v.val[i.toNat]'hi_lt) h_acc_v).val.size
                    = acc.val.size + 2 := by
                rw [push_one_size, push_one_size]
              have hk' : k < acc.val.size + 2 := by rw [h_pp_size] at hk; exact hk
              show (((acc.val ++ #[e]) ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toNat
                  ≤ (v.val[(i + 1).toNat]'hi_i1).toNat
              have h_outer_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              have h_p1_size : (acc.val ++ #[e]).size = acc.val.size + 1 := by
                rw [Array.size_append]; rfl
              by_cases h_k_lt : k < (acc.val ++ #[e]).size
              · rw [Array.getElem_append_left h_k_lt]
                exact Nat.le_trans (h_p1_le_vi k h_k_lt) h_v_step
              · have h_k_ge : (acc.val ++ #[e]).size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - (acc.val ++ #[e]).size = 0 := by
                  rw [h_p1_size]; omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_outer_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - (acc.val ++ #[e]).size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                show (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat
                exact h_v_step
            exact ih (i + 1) true _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi
              (fun h => by cases h)
          · exfalso
            by_cases h_acc_e : acc.val.size + 1 < USize64.size
            · have h_big : USize64.size ≤ acc.val.size + 2 := by omega
              rw [insert_asc_at_step_insert_fail_v v e i acc hi_lt h_vi_ge h_acc_e h_big] at hres
              cases hres
            · have h_big : USize64.size ≤ acc.val.size + 1 := by omega
              rw [insert_asc_at_step_insert_fail_e v e i acc hi_lt h_vi_ge h_big] at hres
              cases hres
        · have h_lt : (v.val[i.toNat]'hi_lt).toNat < e.toNat := by omega
          by_cases h_acc : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_pass v e i false acc hi_lt (Or.inr h_lt) h_acc] at hres
            have h_new_sorted : sorted_asc (acc.val ++ #[v.val[i.toNat]'hi_lt]) := by
              apply sorted_asc_append_singleton acc.val (v.val[i.toNat]'hi_lt) h_acc_sorted
              intro k hk
              exact h_acc_le_vi k hk hi_lt
            have h_new_le_vi :
                ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size)
                  (hi_i1 : (i + 1).toNat < v.val.size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toNat
                    ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
              intro k hk hi_i1
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              have h_v_step : (v.val[i.toNat]'hi_lt).toNat ≤ (v.val[(i + 1).toNat]'hi_i1).toNat := by
                have h_le : i.toNat ≤ (i + 1).toNat := by rw [h_i1]; omega
                exact h_v_sorted i.toNat (i + 1).toNat hi_lt hi_i1 h_le
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                have h_acc_k := h_acc_le_vi k h_k_lt hi_lt
                omega
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                exact h_v_step
            have h_new_le_e :
                false = false → ∀ (k : Nat) (hk : k < (acc.val ++ #[v.val[i.toNat]'hi_lt]).size),
                  ((acc.val ++ #[v.val[i.toNat]'hi_lt])[k]'hk).toNat ≤ e.toNat := by
              intro _ k hk
              rw [Array.size_append] at hk
              have h_one : (#[v.val[i.toNat]'hi_lt] : Array u64).size = 1 := rfl
              by_cases h_k_lt : k < acc.val.size
              · rw [Array.getElem_append_left h_k_lt]
                exact h_acc_le_e rfl k h_k_lt
              · have h_k_ge : acc.val.size ≤ k := by omega
                rw [Array.getElem_append_right h_k_ge]
                have h_idx : k - acc.val.size = 0 := by omega
                have h_zero_lt : (0 : Nat) < (#[v.val[i.toNat]'hi_lt] : Array u64).size := by
                  rw [h_one]; omega
                rw [show ((#[v.val[i.toNat]'hi_lt] : Array u64)[k - acc.val.size]'(by rw [h_idx]; exact h_zero_lt))
                        = (#[v.val[i.toNat]'hi_lt] : Array u64)[0]'h_zero_lt from by simp [h_idx]]
                show (v.val[i.toNat]'hi_lt).toNat ≤ e.toNat
                omega
            exact ih (i + 1) false _ r h_meas h_i1_le hres h_new_sorted h_new_le_vi h_new_le_e
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_asc_at_step_pass_fail v e i false acc hi_lt (Or.inr h_lt) h_big] at hres
            cases hres

/-! ## `insert_asc` wrappers (from empty acc, starting from i = 0). -/

/-- `insert_asc v e` succeeds when `v` is sorted; preserves size+1 and adds 1 to count of e. -/
private theorem insert_asc_inv (v : alloc.vec.Vec u64 alloc.alloc.Global) (e : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64)
    (hres : clever_103_unique_digits.insert_asc v e = RustM.ok r) :
    r.val.size = v.val.size + 1 ∧
    vec_count r.val target r.val.size =
      vec_count v.val target v.val.size + (if e = target then 1 else 0) := by
  unfold clever_103_unique_digits.insert_asc at hres
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
  have inv := insert_asc_at_inv v.val.size v e (0 : usize) false
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

private theorem insert_asc_sorted (v : alloc.vec.Vec u64 alloc.alloc.Global) (e : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_103_unique_digits.insert_asc v e = RustM.ok r)
    (h_v_sorted : sorted_asc v.val) :
    sorted_asc r.val := by
  unfold clever_103_unique_digits.insert_asc at hres
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
  have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_vi :
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size)
        (_ : (0 : usize).toNat < v.val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k]'hk).toNat
        ≤ (v.val[(0 : usize).toNat]'(by assumption)).toNat := by
    intro k hk _
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_empty_le_e : false = false →
      ∀ (k : Nat) (hk : k < ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size),
      (((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val[k]'hk).toNat ≤ e.toNat := by
    intro _ k hk
    have h_empty : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  exact insert_asc_at_sorted v e h_v_sorted v.val.size (0 : usize) false
    ⟨(List.nil).toArray, by grind⟩ r h_meas h_le hres h_empty_sorted h_empty_le_vi h_empty_le_e

/-! ## `filter_at` OOB / step lemmas. -/

private theorem filter_at_oob (l : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_103_unique_digits.filter_at l i acc = RustM.ok acc := by
  unfold clever_103_unique_digits.filter_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Skip step: i in bounds, has_even_digit(l[i]) is true → recurse with same acc. -/
private theorem filter_at_step_skip (l : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (h_hed : clever_103_unique_digits.has_even_digit (l.val[i.toNat]'hi)
              = RustM.ok true) :
    clever_103_unique_digits.filter_at l i acc =
      clever_103_unique_digits.filter_at l (i + 1) acc := by
  conv => lhs; unfold clever_103_unique_digits.filter_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
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
  rw [h_hed]
  simp only [RustM_ok_bind, ↓reduceIte]
  rw [h_add]
  simp only [RustM_ok_bind]

/-- Keep step: i in bounds, has_even_digit(l[i]) = false → recurse on insert_asc(acc, l[i]). -/
private theorem filter_at_step_keep (l : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (h_hed : clever_103_unique_digits.has_even_digit (l.val[i.toNat]'hi)
              = RustM.ok false) :
    clever_103_unique_digits.filter_at l i acc =
      (do
        let acc' ← clever_103_unique_digits.insert_asc acc (l.val[i.toNat]'hi)
        clever_103_unique_digits.filter_at l (i + 1) acc') := by
  conv => lhs; unfold clever_103_unique_digits.filter_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
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
  rw [h_hed]
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte]
  rw [h_add]
  simp only [RustM_ok_bind]

/-! ## Invariants for `filter_at`: size, sortedness, vec_count. -/

/-- `filter_at l i acc` preserves sortedness when the input slice is irrelevant. -/
private theorem filter_at_sorted :
    ∀ (n : Nat) (l : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_103_unique_digits.filter_at l i acc = RustM.ok r →
      sorted_asc acc.val →
      sorted_asc r.val := by
  intro n
  induction n with
  | zero =>
    intro l i acc r hm hi_le hres h_acc_sorted
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [filter_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact h_acc_sorted
  | succ n ih =>
    intro l i acc r hm hi_le hres h_acc_sorted
    by_cases hi_ge : l.val.size ≤ i.toNat
    · rw [filter_at_oob l i acc hi_ge] at hres
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
      -- Decide which branch fired by inspecting has_even_digit.
      have h_hed_eq := has_even_digit_correct (l.val[i.toNat]'hi_lt)
      by_cases h_aod : all_odd_digits (l.val[i.toNat]'hi_lt) = true
      · -- Keep branch: has_even_digit = false.
        have h_hed : clever_103_unique_digits.has_even_digit (l.val[i.toNat]'hi_lt)
                      = RustM.ok false := by
          rw [h_hed_eq, h_aod]; rfl
        rw [filter_at_step_keep l i acc hi_lt h_hed] at hres
        generalize h_ins : clever_103_unique_digits.insert_asc acc (l.val[i.toNat]'hi_lt) = ins_res at hres
        cases ins_res with
        | none =>
          exfalso
          have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_103_unique_digits.filter_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | some res' =>
          cases res' with
          | error e =>
            exfalso
            have hh : (do let acc' ← (some (Except.error e) :
                                        RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                           clever_103_unique_digits.filter_at l (i + 1) acc')
                      = RustM.ok r := hres
            cases hh
          | ok acc' =>
            have h_ins_ok : clever_103_unique_digits.insert_asc acc (l.val[i.toNat]'hi_lt)
                              = RustM.ok acc' := h_ins
            simp only [RustM_ok_bind] at hres
            have h_acc'_sorted : sorted_asc acc'.val :=
              insert_asc_sorted acc (l.val[i.toNat]'hi_lt) acc' h_ins_ok h_acc_sorted
            exact ih l (i + 1) acc' r h_meas h_i1_le hres h_acc'_sorted
      · -- Skip branch: has_even_digit = true.
        have h_aod_false : all_odd_digits (l.val[i.toNat]'hi_lt) = false := by
          rcases Bool.eq_false_or_eq_true (all_odd_digits (l.val[i.toNat]'hi_lt)) with h | h
          · exact absurd h h_aod
          · exact h
        have h_hed : clever_103_unique_digits.has_even_digit (l.val[i.toNat]'hi_lt)
                      = RustM.ok true := by
          rw [h_hed_eq, h_aod_false]; rfl
        rw [filter_at_step_skip l i acc hi_lt h_hed] at hres
        exact ih l (i + 1) acc r h_meas h_i1_le hres h_acc_sorted

/-- vec_count invariant for `filter_at`. -/
private theorem filter_at_count :
    ∀ (n : Nat) (l : RustSlice u64) (i : usize)
      (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (r : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      clever_103_unique_digits.filter_at l i acc = RustM.ok r →
      vec_count r.val target r.val.size +
        (if all_odd_digits target then vec_count l.val target i.toNat else 0)
        = vec_count acc.val target acc.val.size +
            (if all_odd_digits target then vec_count l.val target l.val.size else 0) := by
  intro n
  induction n with
  | zero =>
    intro l i acc r target hm hi_le hres
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have hi_eq : i.toNat = l.val.size := by omega
    rw [filter_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    rw [hi_eq]
  | succ n ih =>
    intro l i acc r target hm hi_le hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [filter_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      rw [hi_eq]
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
      have h_hed_eq := has_even_digit_correct (l.val[i.toNat]'hi_lt)
      by_cases h_aod : all_odd_digits (l.val[i.toNat]'hi_lt) = true
      · -- Keep branch: has_even_digit = false. acc grows by inserting l[i].
        have h_hed : clever_103_unique_digits.has_even_digit (l.val[i.toNat]'hi_lt)
                      = RustM.ok false := by
          rw [h_hed_eq, h_aod]; rfl
        rw [filter_at_step_keep l i acc hi_lt h_hed] at hres
        generalize h_ins : clever_103_unique_digits.insert_asc acc (l.val[i.toNat]'hi_lt) = ins_res at hres
        cases ins_res with
        | none =>
          exfalso
          have hh : (do let acc' ← (none : RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                         clever_103_unique_digits.filter_at l (i + 1) acc')
                    = RustM.ok r := hres
          cases hh
        | some res' =>
          cases res' with
          | error e =>
            exfalso
            have hh : (do let acc' ← (some (Except.error e) :
                                        RustM (alloc.vec.Vec u64 alloc.alloc.Global));
                           clever_103_unique_digits.filter_at l (i + 1) acc')
                      = RustM.ok r := hres
            cases hh
          | ok acc' =>
            have h_ins_ok : clever_103_unique_digits.insert_asc acc (l.val[i.toNat]'hi_lt)
                              = RustM.ok acc' := h_ins
            simp only [RustM_ok_bind] at hres
            have h_ins_inv := insert_asc_inv acc (l.val[i.toNat]'hi_lt) acc' target h_ins_ok
            obtain ⟨h_acc'_size, h_acc'_count⟩ := h_ins_inv
            have ih_app := ih l (i + 1) acc' r target h_meas h_i1_le hres
            rw [h_i1] at ih_app
            rw [h_vec_succ_l] at ih_app
            rw [h_acc'_count] at ih_app
            by_cases h_aod_t : all_odd_digits target = true
            · rw [if_pos h_aod_t] at ih_app
              rw [if_pos h_aod_t]
              omega
            · have h_aod_t_false : all_odd_digits target = false := by
                rcases Bool.eq_false_or_eq_true (all_odd_digits target) with h | h
                · exact absurd h h_aod_t
                · exact h
              have h_li_ne_t : l.val[i.toNat]'hi_lt ≠ target := by
                intro h_eq
                have hh : all_odd_digits (l.val[i.toNat]'hi_lt) = all_odd_digits target := by
                  rw [h_eq]
                rw [h_aod_t_false] at hh
                rw [hh] at h_aod
                exact Bool.false_ne_true h_aod
              rw [if_neg h_li_ne_t] at ih_app
              rw [if_neg (by rw [h_aod_t_false]; decide)] at ih_app
              rw [if_neg (by rw [h_aod_t_false]; decide)]
              omega
      · have h_aod_false : all_odd_digits (l.val[i.toNat]'hi_lt) = false := by
          rcases Bool.eq_false_or_eq_true (all_odd_digits (l.val[i.toNat]'hi_lt)) with h | h
          · exact absurd h h_aod
          · exact h
        have h_hed : clever_103_unique_digits.has_even_digit (l.val[i.toNat]'hi_lt)
                      = RustM.ok true := by
          rw [h_hed_eq, h_aod_false]; rfl
        rw [filter_at_step_skip l i acc hi_lt h_hed] at hres
        have ih_app := ih l (i + 1) acc r target h_meas h_i1_le hres
        rw [h_i1] at ih_app
        rw [h_vec_succ_l] at ih_app
        by_cases h_aod_t : all_odd_digits target = true
        · have h_li_ne_t : l.val[i.toNat]'hi_lt ≠ target := by
            intro h_eq
            rw [h_eq] at h_aod_false
            rw [h_aod_false] at h_aod_t
            cases h_aod_t
          rw [if_neg h_li_ne_t] at ih_app
          rw [if_pos h_aod_t] at ih_app
          rw [if_pos h_aod_t]
          omega
        · have h_aod_t_false : all_odd_digits target = false := by
            rcases Bool.eq_false_or_eq_true (all_odd_digits target) with h | h
            · exact absurd h h_aod_t
            · exact h
          rw [if_neg (by rw [h_aod_t_false]; decide)] at ih_app
          rw [if_neg (by rw [h_aod_t_false]; decide)]
          exact ih_app

/-! ## Obligation placeholders (to be closed later). -/

/-- Anchor: `unique_digits` succeeds on an empty input slice and returns
    an empty `Vec`. -/
theorem empty_input_yields_empty_output
    (x : RustSlice u64) (hempty : x.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_103_unique_digits.unique_digits x = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨(List.nil).toArray, by grind⟩, ?_, ?_⟩
  · unfold clever_103_unique_digits.unique_digits
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new]
    simp only [RustM_ok_bind]
    have h_zero_le : (0 : usize).toNat = 0 := rfl
    have h_oob : x.val.size ≤ (0 : usize).toNat := by rw [h_zero_le]; omega
    rw [filter_at_oob x (0 : usize) ⟨(List.nil).toArray, by grind⟩ h_oob]
  · rfl

theorem output_is_sorted
    (x : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_103_unique_digits.unique_digits x = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat ≤ (v.val[k + 1]'hk).toNat := by
  unfold clever_103_unique_digits.unique_digits at hres
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : x.val.size - (0 : usize).toNat ≤ x.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ x.val.size := by rw [h_zero_le]; omega
  have h_empty_sorted : sorted_asc ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val := by
    intro k₁ k₂ h₁ _ _
    have : ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
    omega
  have h_v_sorted : sorted_asc v.val :=
    filter_at_sorted x.val.size x (0 : usize) ⟨(List.nil).toArray, by grind⟩ v
      h_meas h_le hres h_empty_sorted
  exact h_v_sorted k (k + 1) (Nat.lt_of_succ_lt hk) hk (Nat.le_succ _)

theorem output_count_equals_filtered_count
    (x : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_103_unique_digits.unique_digits x = RustM.ok v)
    (t : u64) :
    vec_count v.val t v.val.size
      = (if all_odd_digits t then vec_count x.val t x.val.size else 0) := by
  unfold clever_103_unique_digits.unique_digits at hres
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : x.val.size - (0 : usize).toNat ≤ x.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ x.val.size := by rw [h_zero_le]; omega
  have h_count := filter_at_count x.val.size x (0 : usize)
                    ⟨(List.nil).toArray, by grind⟩ v t h_meas h_le hres
  rw [h_zero_le] at h_count
  have h_empty_size :
      ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val.size = 0 := rfl
  have h_empty_count :
      vec_count ((⟨(List.nil).toArray, by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global)).val t 0 = 0 := rfl
  rw [h_empty_size, h_empty_count] at h_count
  have h_l_zero : vec_count x.val t 0 = 0 := rfl
  rw [h_l_zero] at h_count
  -- h_count : vec_count v t v.size + (if all_odd_digits t then 0 else 0) = 0 + (if all_odd_digits t then vec_count x t x.size else 0)
  by_cases h_aod : all_odd_digits t = true
  · simp only [h_aod, ↓reduceIte] at h_count
    simp only [h_aod, ↓reduceIte]
    omega
  · have h_aod_false : all_odd_digits t = false := by
      rcases Bool.eq_false_or_eq_true (all_odd_digits t) with h | h
      · exact absurd h h_aod
      · exact h
    simp only [h_aod_false, Bool.false_eq_true, ↓reduceIte] at h_count
    simp only [h_aod_false, Bool.false_eq_true, ↓reduceIte]
    omega

end Clever_103_unique_digitsObligations
