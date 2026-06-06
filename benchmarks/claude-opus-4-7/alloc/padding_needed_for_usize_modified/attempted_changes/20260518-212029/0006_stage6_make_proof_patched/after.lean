-- Companion obligations file for the `padding_needed_for_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import padding_needed_for_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Padding_needed_for_usizeObligations

/-- A `usize` is a valid alignment iff it is a power of two. This is the
    mathematical meaning of Rust's `usize::is_power_of_two`; the extracted
    `is_power_of_two_usize` computes it via the bit-trick
    `n != 0 && (n & (n - 1)) == 0`, and the short-circuit `&&` guards the
    `n - 1` against underflow at `n = 0`. A power of two is `≥ 1`, so this
    also discharges the `align -? 1` no-underflow side condition.

    Definitionally identical to `Nat.isPowerOfTwo a.toNat` (`∃ k, n = 2^k`),
    so Lean core's power-of-two bit-trick lemmas apply directly. -/
def IsPow2 (a : usize) : Prop := ∃ k : Nat, a.toNat = 2 ^ k

/-! ## Generic partial-operator / bit-mask infrastructure

These helpers are ported verbatim from the primary reference
`pad_to_align_usize` — the target's else-branch is the *exact* inlined inner
computation `(size + (align-1)) & !(align-1)`, so the same machinery
(`mask_clear`, `result_toNat`, the `toNat`/complement bridges) is reused. -/

/-- Definitional unfolding of the partial `usize` addition: `x +? y` is, by
    `rfl`, the overflow-guarded `if`. -/
private theorem hax_add_def_usize (x y : usize) :
    x +? y = if USize64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-- Definitional unfolding of the partial `usize` subtraction. -/
private theorem hax_sub_def_usize (x y : usize) :
    x -? y = if USize64.subOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl

/-- `RustM.ok` is, definitionally, the monad's `pure`. Stated so `simp` can
    normalise `RustM.ok _ >>= _` chains through `pure_bind` (the discrimination
    key for `pure_bind` does not see through the reducible `RustM.ok`). -/
private theorem rustM_ok_eq_pure {α : Type} (a : α) :
    (RustM.ok a : RustM α) = pure a := rfl

/-- A panicked computation absorbs any continuation. -/
private theorem rustM_fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e) >>= f = RustM.fail e := rfl

/-- Bridge: `USize64` bitwise-and projects through to `Nat.land` of the
    `toNat`s. -/
private theorem usize_toNat_and (a b : usize) :
    (a &&& b).toNat = a.toNat &&& b.toNat := by
  have h : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_and]

/-- Bridge: `USize64` complement projects through to the 64-bit `BitVec`
    complement value `2^64 - 1 - n`. -/
private theorem usize_toNat_compl (a : usize) :
    (~~~ a).toNat = 2 ^ 64 - 1 - a.toNat := by
  have h : (~~~ a).toBitVec = ~~~ a.toBitVec := rfl
  unfold USize64.toNat
  rw [h, BitVec.toNat_not]

/-- Power-of-two bitmask round-down identity at the `Nat` level: masking off
    the low `k` bits (anding with the 64-bit high mask `2^64 - 2^k`) of any
    value `< 2^64` equals clearing the low `k` bits, i.e. `2^k * (sn / 2^k)`.
    Proved by bit extensionality. -/
private theorem mask_clear (sn k : Nat) (hsn : sn < 2 ^ 64) (hk : k ≤ 64) :
    sn &&& (2 ^ 64 - 2 ^ k) = 2 ^ k * (sn / 2 ^ k) := by
  have hfac : (2 : Nat) ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    have hpow : (2 : Nat) ^ (64 - k) * 2 ^ k = 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.sub_mul, Nat.one_mul, hpow]
  rw [hfac]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
             Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow, ge_iff_le]
  by_cases hkj : k ≤ j
  · have d1 : decide (k ≤ j) = true := decide_eq_true hkj
    have d3 : j - k + k = j := by omega
    rw [d1, d3]
    simp only [Bool.true_and]
    by_cases hb : sn.testBit j = true
    · have hj : j < 64 := by
        have hge2 : sn ≥ 2 ^ j := Nat.ge_two_pow_of_testBit hb
        have hlt2 : (2 : Nat) ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt hge2 hsn
        exact (Nat.pow_lt_pow_iff_right (by decide)).mp hlt2
      rw [hb]
      simp only [Bool.true_and, decide_eq_true_eq]
      omega
    · simp only [Bool.not_eq_true] at hb
      simp [hb]
  · have d1 : decide (k ≤ j) = false := decide_eq_false hkj
    rw [d1]
    simp only [Bool.false_and, Bool.and_false]

/-- The exact `Nat` value of the rounded size, under the invariant. -/
private theorem result_toNat (s a : usize) (k : Nat)
    (hk : a.toNat = 2 ^ k)
    (hnof : s.toNat + (a.toNat - 1) < 2 ^ 64) :
    ((s + (a - 1)) &&& ~~~(a - 1)).toNat
      = 2 ^ k * ((s.toNat + (2 ^ k - 1)) / 2 ^ k) := by
  have hk64 : k ≤ 64 := by
    have hlt : a.toNat < 2 ^ 64 := a.toNat_lt
    rw [hk] at hlt
    have hk' : k < 64 := (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
    omega
  have hone : (1 : usize).toNat = 1 := by decide
  have hle1 : (1 : usize) ≤ a := by
    rw [USize64.le_iff_toNat_le, hone, hk]
    exact Nat.one_le_two_pow
  have ham1 : (a - (1 : usize)).toNat = 2 ^ k - 1 := by
    rw [USize64.toNat_sub_of_le _ _ hle1, hone, hk]
  have hbnd : s.toNat + (a - (1 : usize)).toNat < 2 ^ 64 := by
    rw [ham1]
    have hz : a.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  have hSeq : (s + (a - 1)).toNat = s.toNat + (2 ^ k - 1) := by
    rw [USize64.toNat_add_of_lt hbnd, ham1]
  have hCeq : (~~~ (a - (1 : usize))).toNat = 2 ^ 64 - 2 ^ k := by
    rw [usize_toNat_compl, ham1]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk64
    omega
  have hsn' : s.toNat + (2 ^ k - 1) < 2 ^ 64 := by
    have hz : a.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  rw [usize_toNat_and, hSeq, hCeq]
  exact mask_clear (s.toNat + (2 ^ k - 1)) k hsn' hk64

/-! ## Power-of-two decision (`is_power_of_two_usize`) bridge

The target *computes and branches on* the power-of-two predicate via the
bit-trick `n != 0 && (n & (n-1)) == 0`. Lean core's
`Nat.and_sub_one_eq_zero_iff_isPowerOfTwo` characterises exactly this trick,
so the bridge is: reduce the do-block to `(n &&& (n-1)) == 0` (for `n ≠ 0`),
push through the `toNat`/`land` bridges, then apply the core lemma. -/

/-- `IsPow2` is, by definition, `Nat.isPowerOfTwo` applied to `toNat`. -/
private theorem isPow2_iff (a : usize) : IsPow2 a ↔ Nat.isPowerOfTwo a.toNat :=
  Iff.rfl

/-- A power of two is positive. -/
private theorem pos_of_isPow2 (a : usize) (h : IsPow2 a) : 0 < a.toNat :=
  Nat.pos_of_isPowerOfTwo ((isPow2_iff a).mp h)

/-- A power of two is nonzero (as a `usize`). -/
private theorem ne_zero_of_isPow2 (a : usize) (h : IsPow2 a) : a ≠ (0 : usize) := by
  intro h0
  have hpos := pos_of_isPow2 a h
  rw [h0, USize64.toNat_zero] at hpos
  omega

/-- `n.toNat ≠ 0` whenever `n ≠ 0`. -/
private theorem toNat_ne_zero_of_ne_zero (n : usize) (hn : n ≠ (0 : usize)) :
    n.toNat ≠ 0 := by
  intro h
  exact hn (USize64.toNat_inj.mp (by rw [h, USize64.toNat_zero]))

/-- `(1 : usize) ≤ n` whenever `n ≠ 0`. -/
private theorem one_le_of_ne_zero (n : usize) (hn : n ≠ (0 : usize)) :
    (1 : usize) ≤ n := by
  rw [USize64.le_iff_toNat_le, (by decide : (1 : usize).toNat = 1)]
  have := toNat_ne_zero_of_ne_zero n hn
  omega

/-- Core reduction of the `is_power_of_two_usize` do-block for `n ≠ 0`: the
    `!=? 0` guard is `true` and the `-? 1` does not underflow, so the result
    is exactly the bit-trick boolean `(n &&& (n - 1)) == 0`. -/
private theorem ipo2_core (n : usize) (hn : n ≠ (0 : usize)) :
    padding_needed_for_usize.is_power_of_two_usize n
      = RustM.ok ((n &&& (n - 1)) == (0 : usize)) := by
  have hsub_no : ¬ USize64.subOverflow n (1 : usize) := by
    rw [USize64.subOverflow_iff, (by decide : (1 : usize).toNat = 1)]
    have := toNat_ne_zero_of_ne_zero n hn
    omega
  have hne0 : (n != (0 : usize)) = true := by
    simp [bne, hn]
  unfold padding_needed_for_usize.is_power_of_two_usize
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and]
  rw [hax_sub_def_usize, if_neg hsub_no]
  simp only [pure_bind]
  rw [hne0]
  simp only [Bool.true_and]
  rfl

/-- `is_power_of_two_usize` returns `true` on a genuine power of two. -/
private theorem ipo2_true_of_pow2 (n : usize) (h : IsPow2 n) :
    padding_needed_for_usize.is_power_of_two_usize n = RustM.ok true := by
  have hn : n ≠ (0 : usize) := ne_zero_of_isPow2 n h
  have hnz : n.toNat ≠ 0 := (Nat.pos_iff.mp (pos_of_isPow2 n h)).ne'
  have key : n &&& (n - 1) = (0 : usize) := by
    apply USize64.toNat_inj.mp
    rw [USize64.toNat_zero, usize_toNat_and,
        USize64.toNat_sub_of_le _ _ (one_le_of_ne_zero n hn),
        (by decide : (1 : usize).toNat = 1)]
    exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hnz).mpr ((isPow2_iff n).mp h)
  have hb : ((n &&& (n - 1)) == (0 : usize)) = true := by rw [key]; rfl
  rw [ipo2_core n hn, hb]

/-- `is_power_of_two_usize` returns `false` on a non-power-of-two `n ≠ 0`. -/
private theorem ipo2_false_of_not_pow2 (n : usize) (hn : n ≠ (0 : usize))
    (h : ¬ IsPow2 n) :
    padding_needed_for_usize.is_power_of_two_usize n = RustM.ok false := by
  have hnz : n.toNat ≠ 0 := toNat_ne_zero_of_ne_zero n hn
  have hb : ((n &&& (n - 1)) == (0 : usize)) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have key : n &&& (n - 1) = (0 : usize) := by
      have := hc
      simpa using of_decide_eq_true (by simpa using hc)
    have hnat : n.toNat &&& (n.toNat - 1) = 0 := by
      have hcong := congrArg USize64.toNat key
      rw [usize_toNat_and, USize64.toNat_zero,
          USize64.toNat_sub_of_le _ _ (one_le_of_ne_zero n hn),
          (by decide : (1 : usize).toNat = 1)] at hcong
      exact hcong
    exact h ((isPow2_iff n).mpr ((Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hnz).mp hnat))
  rw [ipo2_core n hn, hb]

/-- Extraction-infidelity witness: at `n = 0` the extracted
    `is_power_of_two_usize` *panics* (the Hax model of Rust's short-circuit
    `&&` is strict, so the `n -? 1` underflow is reached even though Rust
    would short-circuit on `0 != 0`). Real Rust returns `false` here. This
    machine-checked lemma pins the exact divergence and is the reason the
    `align = 0` sub-case of `padding_needed_for_non_power_of_two` cannot
    close. -/
private theorem ipo2_zero :
    padding_needed_for_usize.is_power_of_two_usize (0 : usize)
      = RustM.fail Error.integerOverflow := by
  have hsub : USize64.subOverflow (0 : usize) (1 : usize) := by
    rw [USize64.subOverflow_iff]; decide
  unfold padding_needed_for_usize.is_power_of_two_usize
  simp only [rust_primitives.cmp.ne]
  rw [hax_sub_def_usize, if_pos hsub]
  simp only [pure_bind]
  rfl

/-! ## Inlined round-up computation spec -/

/-- `size_rounded_up_to_custom_align` succeeds and returns the masked round-up
    `(size + (align-1)) & ~(align-1)` under the `Layout` invariant. Mirrors
    the primary reference's `pad_to_align_spec`. -/
private theorem sruca_spec (size align : usize) (k : Nat)
    (hk : align.toNat = 2 ^ k)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    padding_needed_for_usize.size_rounded_up_to_custom_align size align
      = RustM.ok ((size + (align - 1)) &&& ~~~(align - 1)) := by
  have hone : (1 : usize).toNat = 1 := by decide
  have hsub_no : ¬ USize64.subOverflow align (1 : usize) := by
    rw [USize64.subOverflow_iff, hone, hk]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hle1 : (1 : usize) ≤ align := by
    rw [USize64.le_iff_toNat_le, hone, hk]
    exact Nat.one_le_two_pow
  have ham1 : (align - (1 : usize)).toNat = 2 ^ k - 1 := by
    rw [USize64.toNat_sub_of_le _ _ hle1, hone, hk]
  have hadd_no : ¬ USize64.addOverflow size (align - (1 : usize)) := by
    rw [USize64.addOverflow_iff, ham1]
    have hz : align.toNat - 1 = 2 ^ k - 1 := by rw [hk]
    omega
  unfold padding_needed_for_usize.size_rounded_up_to_custom_align
  rw [hax_sub_def_usize, if_neg hsub_no]
  simp only [pure_bind]
  rw [hax_add_def_usize, if_neg hadd_no]
  simp only [pure_bind]
  rfl

/-- `len_rounded_up ≥ size`: the rounded value never drops below `size`, so
    the trailing `len_rounded_up -? size` cannot underflow. -/
private theorem len_ge_size (size align : usize) (k : Nat)
    (hk : align.toNat = 2 ^ k)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    size.toNat ≤ ((size + (align - 1)) &&& ~~~(align - 1)).toNat := by
  rw [result_toNat size align k hk hnof]
  have hdm := Nat.div_add_mod (size.toNat + (2 ^ k - 1)) (2 ^ k)
  have hmod : (size.toNat + (2 ^ k - 1)) % 2 ^ k < 2 ^ k :=
    Nat.mod_lt _ (Nat.two_pow_pos k)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- Master spec for the power-of-two branch: under the `Layout` invariant the
    function succeeds and returns `((size+(align-1)) & ~(align-1)) - size`.
    The per-clause obligations project out of this one equation. -/
private theorem padding_spec (size align : usize) (k : Nat)
    (hk : align.toNat = 2 ^ k)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    padding_needed_for_usize.padding_needed_for size align
      = RustM.ok (((size + (align - 1)) &&& ~~~(align - 1)) - size) := by
  have hpow : IsPow2 align := ⟨k, hk⟩
  have hsub_no :
      ¬ USize64.subOverflow ((size + (align - 1)) &&& ~~~(align - 1)) size := by
    rw [USize64.subOverflow_iff]
    have := len_ge_size size align k hk hnof
    omega
  unfold padding_needed_for_usize.padding_needed_for
  rw [ipo2_true_of_pow2 align hpow]
  simp only [pure_bind, rust_primitives.hax.logical_op.not]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
  rw [sruca_spec size align k hk hnof]
  simp only [pure_bind]
  rw [hax_sub_def_usize, if_neg hsub_no]
  rfl

/-! ## Obligations -/

/-- Special-case / failure clause — captures the Rust property test
    `prop_non_power_of_two_returns_max`: when `align` is not a power of two
    (this includes `align == 0`), `padding_needed_for` returns `usize::MAX`
    (inlined to the 64-bit literal `18446744073709551615`) regardless of
    `size`.

    **Extraction infidelity at `align = 0` (one `sorry`, isolated).** In real
    Rust, `is_power_of_two_usize(0)` short-circuits on `0 != 0` and returns
    `false`, so the function returns `usize::MAX`. The Hax Lean model of
    Rust's short-circuit `&&` is *strict* (`&&?` is `pure (a && b)` and the
    `do`-block sequences `n -? 1` unconditionally), so
    `is_power_of_two_usize (0:usize)` **panics** at the `0 -? 1` underflow
    (machine-checked: see `ipo2_zero`). Hence
    `padding_needed_for size 0 = RustM.fail Error.integerOverflow`, and the
    stuck sub-goal after reduction is the literally-false
    `RustM.fail Error.integerOverflow = RustM.ok 18446744073709551615`.
    Structural unblock: this is not a tactic gap — it requires the Hax
    extraction to emit a short-circuiting encoding for Rust's `&&` (e.g. a
    `RustM`-level `if`/lazy boolean-bind) so that `is_power_of_two_usize 0`
    returns `false` instead of panicking; alternatively the obligation must
    exclude `align = 0` since the extracted function genuinely diverges from
    Rust there. The `align ≠ 0` case (the entire rest of the contract clause)
    is proved in full below. -/
theorem padding_needed_for_non_power_of_two (size align : usize)
    (h : ¬ IsPow2 align) :
    padding_needed_for_usize.padding_needed_for size align
      = RustM.ok (18446744073709551615 : usize) := by
  by_cases h0 : align = (0 : usize)
  · -- Extraction-infidelity branch: extracted fn panics, real Rust returns MAX.
    subst h0
    have hreduce :
        padding_needed_for_usize.padding_needed_for size (0 : usize)
          = RustM.fail Error.integerOverflow := by
      unfold padding_needed_for_usize.padding_needed_for
      rw [ipo2_zero]
      rfl
    rw [hreduce]
    -- Stuck (false) goal: `RustM.fail Error.integerOverflow = RustM.ok …`.
    sorry
  · -- Faithful branch: non-power-of-two, nonzero ⇒ returns MAX.
    have hfalse := ipo2_false_of_not_pow2 align h0 h
    unfold padding_needed_for_usize.padding_needed_for
    rw [hfalse]
    simp only [pure_bind, rust_primitives.hax.logical_op.not]
    simp only [Bool.not_false, Bool.true_eq_true, if_true, pure_bind]
    rfl

/-- Concrete anchor — captures the Rust unit test `doc_example` (the doc
    comment's worked example): the padding after a block of size 9 for
    alignment 4 is 3. -/
theorem padding_needed_for_doc_example :
    padding_needed_for_usize.padding_needed_for (9 : usize) (4 : usize)
      = RustM.ok (3 : usize) := by
  refine (padding_spec (9 : usize) (4 : usize) 2 (by decide) (by decide)).trans ?_
  rfl

/-- Postcondition clause A — captures the Rust property test
    `prop_result_aligns_size_up`: for a power-of-two `align`, the returned
    padding `r` rounds `size` up so the following address is aligned, i.e.
    `(size + r) % align == 0`. `hnof` is the function's implicit
    precondition — `size + (align - 1)` does not overflow `usize` — which
    the property test enforces by keeping `size < 1000`. -/
theorem padding_needed_for_result_aligns_size_up (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    ∃ r : usize,
      padding_needed_for_usize.padding_needed_for size align = RustM.ok r
      ∧ (size.toNat + r.toNat) % align.toNat = 0 := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, padding_spec size align k hk hnof, ?_⟩
  have hge := len_ge_size size align k hk hnof
  have hle : size ≤ ((size + (align - 1)) &&& ~~~(align - 1)) := by
    rw [USize64.le_iff_toNat_le]; exact hge
  show (size.toNat
        + (((size + (align - 1)) &&& ~~~(align - 1)) - size).toNat)
        % align.toNat = 0
  rw [USize64.toNat_sub_of_le _ _ hle, result_toNat size align k hk hnof, hk]
  have hge' : size.toNat ≤ 2 ^ k * ((size.toNat + (2 ^ k - 1)) / 2 ^ k) := by
    rw [result_toNat size align k hk hnof] at hge; exact hge
  have hsimp :
      size.toNat + (2 ^ k * ((size.toNat + (2 ^ k - 1)) / 2 ^ k) - size.toNat)
        = 2 ^ k * ((size.toNat + (2 ^ k - 1)) / 2 ^ k) := by omega
  rw [hsimp]
  exact Nat.mul_mod_right _ _

/-- Postcondition clause B (minimality) — captures the Rust property test
    `prop_padding_is_minimal`: for a power-of-two `align`, the padding is the
    *smallest* value with property A, i.e. strictly less than `align`. -/
theorem padding_needed_for_padding_is_minimal (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    ∃ r : usize,
      padding_needed_for_usize.padding_needed_for size align = RustM.ok r
      ∧ r.toNat < align.toNat := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨_, padding_spec size align k hk hnof, ?_⟩
  have hge := len_ge_size size align k hk hnof
  have hle : size ≤ ((size + (align - 1)) &&& ~~~(align - 1)) := by
    rw [USize64.le_iff_toNat_le]; exact hge
  show (((size + (align - 1)) &&& ~~~(align - 1)) - size).toNat < align.toNat
  rw [USize64.toNat_sub_of_le _ _ hle, result_toNat size align k hk hnof, hk]
  have hdm := Nat.div_add_mod (size.toNat + (2 ^ k - 1)) (2 ^ k)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hge' : size.toNat ≤ 2 ^ k * ((size.toNat + (2 ^ k - 1)) / 2 ^ k) := by
    rw [result_toNat size align k hk hnof] at hge; exact hge
  omega

/-- Totality / no-panic under the implicit precondition. For a power-of-two
    `align` (hence `≥ 1`, so `align - 1` does not underflow) with
    `size + (align - 1)` not overflowing, the function returns successfully.
    (The non-power-of-two branch is unconditionally total for `align ≠ 0`;
    see `padding_needed_for_non_power_of_two`.) -/
theorem padding_needed_for_total (size align : usize)
    (hpow : IsPow2 align)
    (hnof : size.toNat + (align.toNat - 1) < 2 ^ 64) :
    ∃ r : usize,
      padding_needed_for_usize.padding_needed_for size align = RustM.ok r := by
  obtain ⟨k, hk⟩ := hpow
  exact ⟨_, padding_spec size align k hk hnof⟩

end Padding_needed_for_usizeObligations
