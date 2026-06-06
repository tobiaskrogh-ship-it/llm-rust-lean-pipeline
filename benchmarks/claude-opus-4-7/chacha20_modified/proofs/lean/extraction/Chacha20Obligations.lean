-- Companion obligations file for the `chacha20` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import chacha20

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Chacha20Obligations

/-! ## Contract clauses derived from `src/lib.rs` property tests.

Four `proptest!` cases + one RFC 8439 KAT unit test give the contract:

  1. `output_length_equals_input_length` — `chacha20` preserves byte length.
  2. `encryption_is_involution`           — `chacha20` is its own inverse.
  3. `encrypt_block_matches_full_chacha20`
                                          — `chacha20_encrypt_block` agrees
                                            with `chacha20` on a single
                                            64-byte block (ctr = 0).
  4. `encrypt_last_matches_full_chacha20_for_short_input`
                                          — `chacha20_encrypt_last` agrees
                                            with `chacha20` on inputs of
                                            length ≤ 64 (ctr = 0).
  5. `rfc8439_test_vector`                — concrete RFC 8439 §2.4.2 KAT.

All preconditions in `RustSlice`/`RustArray` carry their own
`size_lt_usizeSize` invariant, and the intermediate Vec lengths never
exceed `m.val.size < 2 ^ 64`, so each `extend_from_slice` is in range.
No additional totality precondition is needed for clauses 1–3; clause 4
needs `plain.val.size ≤ 64` (the explicit Rust precondition). -/

/--
Postcondition: `chacha20` succeeds on every input, and the result has
exactly the same number of bytes as the input slice. Covers the
`output_length_equals_input_length` proptest (which also subsumes the
empty / single-block / partial-block / multi-block paths).

**Status (proof stage):** I tried this proof and could not finish it.
Because there are no `h_init`/`h_last`-style success hypotheses on the
sub-calls (the theorem itself asserts the totality of `chacha20`), the
proof must construct the success witness from scratch. That requires
totality proofs for:

  - **`chacha20_init`** — drives `to_le_u32s_8` and `to_le_u32s_3`,
    each a `fold_range` loop over (resp.) 8 and 3 indices that internally
    succeeds at every step (`try_into` on a 4-byte slice, `from_le_bytes`,
    `update_at_usize` with in-range index).
  - **`chacha20_encrypt_block`** — composes `chacha20_core` (with a
    nested 10-round `partial_fixpoint` for `chacha20_rounds_at`, itself
    composing 8 `chacha20_quarter_round` calls per double round) with
    `to_le_u32s_16`, `xor_state`, and `u32s_to_le_bytes` (all `fold_range`
    loops with in-range indexing).
  - **`chacha20_update_blocks`** — strong induction over the descending
    `num_blocks - i` measure, where each recursive step depends on
    `chacha20_encrypt_block`'s totality plus an `extend_from_slice`
    no-overflow argument (acc.size + 64 < 2^64, derived from the input
    slice's `size_lt_usizeSize` invariant).
  - **`chacha20_update`** — combines `update_blocks` with the partial-
    block branch via `chacha20_encrypt_last` (when `remainder ≠ 0`).

The stuck sub-goal is the very first one: `fold_range_spec_int_usize`
in the prelude is stated as a Hoare triple, not as a `∃ r, … = .ok r`
equality, so transferring its conclusion into the existential form
requires either a `triple_to_exists_ok` bridge lemma or a hand-rolled
strong-induction lemma for each `fold_range` shape. The proof would
need ~6 such per-`fold_range` lemmas plus a strong-induction lemma for
`chacha20_rounds_at` and one for `chacha20_update_blocks` — estimated
several hundred lines of mechanical reduction analogous to the
clever_025 reference (~1100 lines for one comparable shape).

**Structural unblock:** Hax prelude lemmas of the form
`fold_range_totality : (∀ acc i, s ≤ i → i < e → ∃ acc', body acc i = pure acc')
    → ∃ r, fold_range s e _ init body = pure r`
and a `partial_fixpoint`-totality lemma
`chacha20_rounds_at_total : ∀ st i, ∃ r, chacha20_rounds_at st i = pure r`
would let the proof compose `RustM.ok` witnesses without per-loop
unfolding. I am incapable of completing this proof in a single session
at the depth needed.
-/
theorem chacha20_length_eq_input
    (m : RustSlice u8)
    (key : RustArray u8 32) (iv : RustArray u8 12) (ctr : u32) :
    ∃ r : alloc.vec.Vec u8 alloc.alloc.Global,
      chacha20.chacha20 m key iv ctr = RustM.ok r
      ∧ r.val.size = m.val.size := by
  sorry

/--
Postcondition: `chacha20` is an involution — encrypting the ciphertext
with the same `(key, iv, ctr)` recovers the plaintext. Covers the
`encryption_is_involution` proptest.

`RustSlice u8`, `alloc.vec.Vec u8 alloc.alloc.Global`, and
`rust_primitives.sequence.Seq u8` are all the same underlying type
(abbreviations), so feeding the ciphertext back into `chacha20` is well
typed without an explicit cast.

**Status (proof stage):** I tried this proof and could not finish it.
The involution depends on **four interlocking arguments**:

  1. **Totality** (chacha20_length_eq_input above) so that
     `chacha20 c key iv ctr` produces a `RustM.ok` value at all.
  2. **Keystream determinism** — `chacha20_init`, `chacha20_core`, and
     `chacha20_encrypt_block` are pure functions of their inputs, so the
     keystream block produced for index `i` depends only on
     `(key, iv, ctr, i)`, not on the plaintext bytes. This requires
     showing that the encrypt_block branch reads the plaintext only via
     the final `xor_state`, never affecting the keystream computation
     (which routes through `to_le_u32s_16(plain)`, then
     `xor_state(keystream, plain_words)`, then `u32s_to_le_bytes`).
  3. **Byte-level XOR involution** — `(b XOR k) XOR k = b` for every
     `b, k : u8`. Standard but needs a Hax-prelude lemma we don't see;
     would have to derive from `BitVec.xor_assoc` + `BitVec.xor_self`.
  4. **`to_le_u32s_16 ∘ u32s_to_le_bytes = id`** on 64-byte sequences
     (round-trip lemma over the little-endian word packing). This
     requires `from_le_bytes ∘ to_le_bytes = id` plus the analogous
     fold-correctness over 16 words.

The stuck sub-goal is the keystream-determinism argument: even at the
top level, `chacha20_encrypt_block(st0, ctr, c[64*i..64*i+64])` and
`chacha20_encrypt_block(st0, ctr, m[64*i..64*i+64])` must produce
ciphertext bytes that XOR back to the plaintext, but the function
intermixes the plaintext word array with the keystream via a single
`xor_state` call — extracting "the keystream" as a separate object
requires a refactoring lemma that the Hax prelude does not provide.

**Structural unblock:** a private lemma
`chacha20_encrypt_block_is_xor : ∀ st0 ctr blk keystream b_out,
    chacha20_core ctr st0 = RustM.ok st_core →
    keystream = u32s_to_le_bytes(st_core) →
    chacha20_encrypt_block st0 ctr blk = RustM.ok b_out →
    b_out.val[i] = blk.val[i] XOR keystream.val[i]`
together with `xor_self_involution : ∀ a b : u8, a XOR b XOR b = a`
would make the involution provable by element-wise byte equality. I am
incapable of completing this proof in a single session at the depth of
mechanical detail needed; cryptographic involution requires four
separate proof streams that each individually exceed theorem 3's
~90-line reduction.
-/
theorem chacha20_involution
    (m : RustSlice u8)
    (key : RustArray u8 32) (iv : RustArray u8 12) (ctr : u32) :
    ∃ c : alloc.vec.Vec u8 alloc.alloc.Global,
      chacha20.chacha20 m key iv ctr = RustM.ok c
      ∧ chacha20.chacha20 c key iv ctr = RustM.ok m := by
  sorry

/--
Postcondition: on a single 64-byte block, `chacha20_encrypt_block`
applied to the initial state and counter 0 produces exactly the same
ciphertext as `chacha20` on the same block. Covers the
`encrypt_block_matches_full_chacha20` proptest.

The four hypotheses package "all calls succeed" — totality of the
individual calls is captured by `chacha20_length_eq_input` and the
`@[spec]` totality of `chacha20_init` / `chacha20_encrypt_block`.

Proved by an explicit reduction chain: unfold `chacha20.chacha20` and
`chacha20.chacha20_update`, substitute `h_init` and use a local
`pure_bind`-style lemma stated by `rfl` to walk the `RustM` bind chain,
compute slice-length / div / mod / Vec.new / cast_op / +? / *? at the
concrete values 64, 1, 0, unfold `chacha20_update_blocks.eq_def` at
`(i=0, num_blocks=1)` and at `(i=1, num_blocks=1)` (terminating
branch), reduce `try_into RustSlice → RustArray u8 64` (length matches),
`Impl.unwrap (Result.Ok …)`, `unsize`, and `extend_from_slice` on an
empty Vec, substitute `h_blk` to fold in the encrypt result, and close
the outer `if remainder_len ≠ 0` with `0 !=? 0 = false`. Final
injection on `RustM.ok` yields `m_out = ⟨b_out.toVec.toArray, _⟩`.
-/
theorem chacha20_encrypt_block_matches_full
    (key : RustArray u8 32) (iv : RustArray u8 12) (ctr : u32)
    (block : RustArray u8 64)
    (st0 : RustArray u32 16) (blk_slice : RustSlice u8)
    (b_out : RustArray u8 64) (m_out : alloc.vec.Vec u8 alloc.alloc.Global)
    (h_init   : chacha20.chacha20_init key iv ctr = RustM.ok st0)
    (h_unsize : rust_primitives.unsize block = RustM.ok blk_slice)
    (h_blk    : chacha20.chacha20_encrypt_block st0 (0 : u32) block
                  = RustM.ok b_out)
    (h_full   : chacha20.chacha20 blk_slice key iv ctr = RustM.ok m_out) :
    b_out.toVec.toArray = m_out.val := by
  -- rfl-based bind reduction packaged as a local lemma.
  have h_bind : ∀ {α β} (x : α) (f : α → RustM β),
      ((RustM.ok x : RustM α) >>= f) = f x := fun _ _ => rfl
  unfold chacha20.chacha20 at h_full
  rw [h_init, h_bind] at h_full
  -- h_full : chacha20_update st0 blk_slice = RustM.ok m_out
  -- Extract blk_slice's structure from h_unsize.
  have h_blk_slice : blk_slice = ⟨block.toVec.toArray, by grind⟩ := by
    unfold rust_primitives.unsize at h_unsize
    have h2 : (RustM.ok ⟨block.toVec.toArray, by grind⟩ : RustM (RustSlice u8))
                = RustM.ok blk_slice := h_unsize
    injection h2 with h3
    injection h3 with h4
    exact h4.symm
  have h_size : blk_slice.val.size = 64 := by
    rw [h_blk_slice]
    simp
  -- Now unfold chacha20_update step by step.
  unfold chacha20.chacha20_update at h_full
  -- core_models.slice.Impl.len u8 blk_slice reduces to pure (.ofNat 64)
  have h_len_eq :
      core_models.slice.Impl.len u8 blk_slice
        = (pure (USize64.ofNat 64) : RustM usize) := by
    unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
    rw [h_size]
  rw [h_len_eq] at h_full
  -- Reduce the pure-bind: pure (.ofNat 64) >>= f = f (.ofNat 64).
  -- Note pure = RustM.ok up to defeq via the monad instance.
  have h_pure_bind : ∀ {α β} (x : α) (f : α → RustM β),
      ((pure x : RustM α) >>= f) = f x := fun _ _ => rfl
  rw [h_pure_bind] at h_full
  -- Compute USize64.ofNat 64 /? 64 = pure 1.
  have h_div64 : (USize64.ofNat 64 /? (64 : usize) : RustM usize) = pure 1 := by
    show (rust_primitives.ops.arith.Div.div (USize64.ofNat 64) (64 : usize) : RustM usize)
           = pure 1
    show (if (64 : usize) = 0 then (.fail .divisionByZero : RustM usize)
            else pure (USize64.ofNat 64 / (64 : usize))) = pure 1
    rw [if_neg (by decide)]
    rfl
  rw [h_div64, h_pure_bind] at h_full
  rw [h_pure_bind] at h_full  -- remainder_len ← __do_lift %? 64 with __do_lift = .ofNat 64
  -- compute 64 %? 64 = pure 0
  have h_mod64 : (USize64.ofNat 64 %? (64 : usize) : RustM usize) = pure 0 := by
    show (rust_primitives.ops.arith.Rem.rem (USize64.ofNat 64) (64 : usize) : RustM usize)
           = pure 0
    show (if (64 : usize) = 0 then (.fail .divisionByZero : RustM usize)
            else pure (USize64.ofNat 64 % (64 : usize))) = pure 0
    rw [if_neg (by decide)]
    rfl
  rw [h_mod64, h_pure_bind] at h_full
  -- alloc.vec.Impl.new u8 _ = pure ⟨#[], _⟩
  have h_new : (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
                = pure ⟨#[], by decide⟩ := rfl
  rw [h_new, h_pure_bind] at h_full
  -- Unfold chacha20_update_blocks for one step at (i=0, num_blocks=1)
  -- via the equation produced by `partial_fixpoint`.
  rw [chacha20.chacha20_update_blocks.eq_def st0 blk_slice 0 1 ⟨#[], by decide⟩]
    at h_full
  -- Reduce `0 >=? 1` to `pure false` and step into the else-branch.
  have h_ge_01 : ((0 : usize) >=? (1 : usize) : RustM Bool) = pure false := by
    show (rust_primitives.cmp.ge (0 : usize) (1 : usize) : RustM Bool) = pure false
    rfl
  rw [h_ge_01, h_pure_bind] at h_full
  -- Reduce 64 *? 0 = pure 0 (this rewrites both occurrences at once).
  have h_mul_640 : ((64 : usize) *? (0 : usize) : RustM usize) = pure 0 := rfl
  have h_add_064 : ((0 : usize) +? (64 : usize) : RustM usize) = pure 64 := rfl
  rw [h_mul_640, h_pure_bind, h_pure_bind, h_add_064, h_pure_bind] at h_full
  -- Drop the `if false = true` branch.
  simp only [Bool.false_eq_true, ↓reduceIte] at h_full
  -- Reduce blk_slice[Range 0 64]_? to pure ⟨blk_slice.val, _⟩.
  have h_slice : (blk_slice[(core_models.ops.range.Range.mk
                  (start := (0 : usize)) (_end := (64 : usize)))]_?
                  : RustM (RustSlice u8))
                = pure blk_slice := by
    show (if (0 : usize) ≤ (64 : usize) && (64 : usize).toNat ≤ blk_slice.val.size
            then pure (⟨blk_slice.val.extract 0 64, by grind⟩ : RustSlice u8)
            else RustM.fail .arrayOutOfBounds) = pure blk_slice
    rw [h_size]
    have h_cond : (decide ((0 : usize) ≤ (64 : usize))
                    && decide ((64 : usize).toNat ≤ (64 : Nat))) = true := by decide
    rw [show ((0 : usize) ≤ (64 : usize) && (64 : usize).toNat ≤ (64 : Nat))
            = ((decide ((0 : usize) ≤ (64 : usize)))
                && decide ((64 : usize).toNat ≤ (64 : Nat)))
          from rfl, h_cond]
    simp only [↓reduceIte]
    congr 1
    have h_ext : blk_slice.val.extract 0 64 = blk_slice.val := by
      rw [show (64 : Nat) = blk_slice.val.size from h_size.symm]
      simp
    show (⟨blk_slice.val.extract 0 64, by grind⟩ : RustSlice u8) = blk_slice
    obtain ⟨val, sz⟩ := blk_slice
    simp only at h_ext
    congr 1
  rw [h_slice, h_pure_bind] at h_full
  -- Substitute blk_slice = ⟨block.toVec.toArray, _⟩ everywhere
  subst h_blk_slice
  -- Now try_into has known shape since block.toVec.toArray.size = 64.
  have h_try : (core_models.convert.TryInto.try_into (RustSlice u8) (RustArray u8 64)
                  ⟨block.toVec.toArray, by grind⟩
                  : RustM (core_models.result.Result (RustArray u8 64) core_models.array.TryFromSliceError))
                = pure (.Ok block) := by
    have hsz : block.toVec.toArray.size = (64 : usize).toNat := by simp
    show pure (if h : (⟨block.toVec.toArray, by grind⟩
                          : RustSlice u8).val.size = (64 : usize).toNat then
                  core_models.result.Result.Ok
                    (RustArray.ofVec ((⟨block.toVec.toArray, by grind⟩
                                          : RustSlice u8).val.toVector.cast h))
                else
                  .Err core_models.array.TryFromSliceError.mk)
          = pure (.Ok block)
    rw [dif_pos hsz]
    cases block with
    | ofVec v => rfl
  rw [h_try, h_pure_bind] at h_full
  -- Reduce Impl.unwrap (Result.Ok x) = pure x.
  have h_unwrap : ∀ (x : RustArray u8 64),
      (core_models.result.Impl.unwrap (RustArray u8 64)
        core_models.array.TryFromSliceError (.Ok x) : RustM (RustArray u8 64))
        = pure x := fun _ => rfl
  rw [h_unwrap, h_pure_bind] at h_full
  -- Reduce cast_op (0 : usize) : RustM u32 = pure 0
  have h_cast_0 : (rust_primitives.hax.cast_op (0 : usize) : RustM u32) = pure 0 := rfl
  rw [h_cast_0, h_pure_bind] at h_full
  -- Substitute h_blk to reduce chacha20_encrypt_block.
  rw [h_blk] at h_full
  rw [h_bind] at h_full
  -- Reduce unsize b_out
  have h_uns_b : (rust_primitives.unsize b_out : RustM (rust_primitives.sequence.Seq u8))
                  = pure ⟨b_out.toVec.toArray, by grind⟩ := rfl
  rw [h_uns_b, h_pure_bind] at h_full
  -- Reduce extend_from_slice of empty Vec by b_out.toVec.toArray.
  have h_b_out_size : b_out.toVec.toArray.size < USize64.size := by
    simp; decide
  have h_size_ext : (⟨#[], by decide⟩ : alloc.vec.Vec u8 alloc.alloc.Global).val.size
                      + (⟨b_out.toVec.toArray, by grind⟩
                          : rust_primitives.sequence.Seq u8).val.size < USize64.size := by
    show (0 : Nat) + b_out.toVec.toArray.size < USize64.size
    rw [Nat.zero_add]
    exact h_b_out_size
  have h_ext : (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
                  ⟨#[], by decide⟩ ⟨b_out.toVec.toArray, by grind⟩
                    : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
                = pure ⟨b_out.toVec.toArray, by grind⟩ := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_size_ext]
    -- Goal: pure ⟨#[].append b_out.toVec.toArray, _⟩ = pure ⟨b_out.toVec.toArray, _⟩
    -- The two Vecs differ only in the val field, and the val fields are equal
    -- since `#[] ++ x = x`.
    congr 1
    have h_app : (⟨#[], by decide⟩ : alloc.vec.Vec u8 alloc.alloc.Global).val.append
                  (⟨b_out.toVec.toArray, by grind⟩
                      : rust_primitives.sequence.Seq u8).val
                = b_out.toVec.toArray := by
      show (#[] : Array u8).append b_out.toVec.toArray = b_out.toVec.toArray
      simp
    -- Now do val-based equality on the structure.
    apply (show ∀ (a b : alloc.vec.Vec u8 alloc.alloc.Global),
                a.val = b.val → a = b by
              intros a b h
              cases a; cases b; congr) _ _ h_app
  rw [h_ext, h_pure_bind] at h_full
  -- Reduce 0 +? 1 = pure 1
  have h_add_01 : ((0 : usize) +? (1 : usize) : RustM usize) = pure 1 := rfl
  rw [h_add_01, h_pure_bind] at h_full
  -- Unfold chacha20_update_blocks at (i=1, num_blocks=1) — terminating branch.
  rw [chacha20.chacha20_update_blocks.eq_def st0
        ⟨block.toVec.toArray, by grind⟩ 1 1 ⟨b_out.toVec.toArray, by grind⟩] at h_full
  have h_ge_11 : ((1 : usize) >=? (1 : usize) : RustM Bool) = pure true := by
    show (rust_primitives.cmp.ge (1 : usize) (1 : usize) : RustM Bool) = pure true
    rfl
  rw [h_ge_11, h_pure_bind] at h_full
  -- The `if true then pure acc` reduces to `pure acc`.
  simp only [↓reduceIte] at h_full
  -- 0 !=? 0 reduces to pure false.
  have h_ne_00 : ((0 : usize) !=? (0 : usize) : RustM Bool) = pure false := by
    show (rust_primitives.cmp.ne (0 : usize) (0 : usize) : RustM Bool) = pure false
    rfl
  rw [h_pure_bind, h_ne_00, h_pure_bind] at h_full
  -- The `if false = true then ... else pure blocks_out` reduces to `pure blocks_out`.
  simp only [Bool.false_eq_true, ↓reduceIte] at h_full
  -- And `do let y ← pure x; pure y` reduces to `pure x`.
  rw [h_pure_bind] at h_full
  -- Now h_full : pure ⟨b_out.toVec.toArray, _⟩ = RustM.ok m_out.
  -- Extract via injection.
  have h_final : (⟨b_out.toVec.toArray, by grind⟩ : alloc.vec.Vec u8 alloc.alloc.Global) = m_out := by
    have h2 : (RustM.ok ⟨b_out.toVec.toArray, by grind⟩
                : RustM (alloc.vec.Vec u8 alloc.alloc.Global)) = RustM.ok m_out := h_full
    injection h2 with h3
    injection h3
  rw [← h_final]

/--
Postcondition: on a partial final block of length ≤ 64,
`chacha20_encrypt_last` applied to the initial state and counter 0
produces exactly the same ciphertext as `chacha20`. Covers the
`encrypt_last_matches_full_chacha20_for_short_input` proptest.

Precondition `plain.val.size ≤ 64` matches the Rust function's documented
contract ("Caller must pass plain.len() ≤ 64").

**Status (proof stage):** I tried this proof and could not finish it.
The proof structure requires a 3-way case analysis on `plain.val.size`:

  - **(A) `plain.val.size = 0`** — `chacha20` returns `Vec::new()` (no
    blocks, no remainder); `chacha20_encrypt_last` returns
    `b[0..0].to_vec() = []` after `update_array` runs a 0-iteration
    `fold_range`. Both produce `last_out.val = m_out.val = #[]`.
  - **(B) `0 < plain.val.size < 64`** — `chacha20` reduces to
    `extend_from_slice(empty, chacha20_encrypt_last(st0, 0, plain[…]))`,
    where `plain[0..plain.val.size]_?` reduces to `plain`. After
    substituting `h_last`, this yields `m_out.val = last_out.val`.
  - **(C) `plain.val.size = 64`** — `chacha20` instead routes through
    `chacha20_update_blocks` with `num_blocks = 1`, calling
    `chacha20_encrypt_block(st0, 0, plain_as_RustArray)`, whereas
    `chacha20_encrypt_last(st0, 0, plain)` for size 64 internally does
    `update_array [0;64] plain` then `chacha20_encrypt_block`. Equating
    these requires proving `update_array [0;64] plain = plain_as_RustArray`
    when `plain.val.size = 64`, a 64-step `fold_range` correctness lemma.

The stuck sub-goal in each case is the explicit reduction chain through
the `RustM` monad's bind structure (analogous to theorem 3's ~90-line
reduction); each case would require ~80–150 lines of similar
`rfl`/`simp only`/`rw` plumbing, and case (C) additionally needs a
`fold_range` correctness lemma for `update_array` that the Hax prelude
does not currently provide.

**Structural unblock:** a separately-verified private lemma
`update_array_full_overwrites : ∀ (b : RustArray u8 64) (p : RustSlice u8),
    p.val.size = 64 →
    chacha20.hacspec_helper.update_array b p
      = RustM.ok (RustArray.ofVec ⟨p.val.toVector.cast …, …⟩)`
in either the Hax prelude or this file would close case (C); a generic
`fold_range_terminates_at_start s e init body : s = e → fold_range s e _
    init body = pure init` and a `chacha20_update_blocks_base : i ≥ n →
    chacha20_update_blocks st0 m i n acc = pure acc` would close (A) and (B).
-/
theorem chacha20_encrypt_last_matches_full
    (key : RustArray u8 32) (iv : RustArray u8 12) (ctr : u32)
    (plain : RustSlice u8)
    (h_pre : plain.val.size ≤ 64)
    (st0 : RustArray u32 16)
    (last_out m_out : alloc.vec.Vec u8 alloc.alloc.Global)
    (h_init : chacha20.chacha20_init key iv ctr = RustM.ok st0)
    (h_last : chacha20.chacha20_encrypt_last st0 (0 : u32) plain
                = RustM.ok last_out)
    (h_full : chacha20.chacha20 plain key iv ctr = RustM.ok m_out) :
    last_out.val = m_out.val := by
  sorry

/-! ### RFC 8439 §2.4.2 known-answer test vector

This is the canonical ChaCha20 KAT: it pins the algorithm to the actual
RFC 8439 constants (rotation amounts, sigma "expand 32-byte k" words,
quarter-round indices). Length preservation, involution, and the
block/last agreement above are satisfied by *any* XOR-based stream
cipher; the KAT is what distinguishes ChaCha20 from a different
permutation. -/

private def rfc_key : RustArray u8 32 :=
  RustArray.ofVec #v[
    (0x00 : u8), (0x01 : u8), (0x02 : u8), (0x03 : u8),
    (0x04 : u8), (0x05 : u8), (0x06 : u8), (0x07 : u8),
    (0x08 : u8), (0x09 : u8), (0x0a : u8), (0x0b : u8),
    (0x0c : u8), (0x0d : u8), (0x0e : u8), (0x0f : u8),
    (0x10 : u8), (0x11 : u8), (0x12 : u8), (0x13 : u8),
    (0x14 : u8), (0x15 : u8), (0x16 : u8), (0x17 : u8),
    (0x18 : u8), (0x19 : u8), (0x1a : u8), (0x1b : u8),
    (0x1c : u8), (0x1d : u8), (0x1e : u8), (0x1f : u8)]

private def rfc_iv : RustArray u8 12 :=
  RustArray.ofVec #v[
    (0x00 : u8), (0x00 : u8), (0x00 : u8), (0x00 : u8),
    (0x00 : u8), (0x00 : u8), (0x00 : u8), (0x4a : u8),
    (0x00 : u8), (0x00 : u8), (0x00 : u8), (0x00 : u8)]

/-- Plaintext bytes for `"Ladies and Gentlemen of the class of '99: If I
could offer you only one tip for the future, sunscreen would be it."`. -/
private def rfc_plaintext_bytes : Array u8 :=
  #[(0x4c : u8), (0x61 : u8), (0x64 : u8), (0x69 : u8), (0x65 : u8),
    (0x73 : u8), (0x20 : u8), (0x61 : u8), (0x6e : u8), (0x64 : u8),
    (0x20 : u8), (0x47 : u8), (0x65 : u8), (0x6e : u8), (0x74 : u8),
    (0x6c : u8), (0x65 : u8), (0x6d : u8), (0x65 : u8), (0x6e : u8),
    (0x20 : u8), (0x6f : u8), (0x66 : u8), (0x20 : u8), (0x74 : u8),
    (0x68 : u8), (0x65 : u8), (0x20 : u8), (0x63 : u8), (0x6c : u8),
    (0x61 : u8), (0x73 : u8), (0x73 : u8), (0x20 : u8), (0x6f : u8),
    (0x66 : u8), (0x20 : u8), (0x27 : u8), (0x39 : u8), (0x39 : u8),
    (0x3a : u8), (0x20 : u8), (0x49 : u8), (0x66 : u8), (0x20 : u8),
    (0x49 : u8), (0x20 : u8), (0x63 : u8), (0x6f : u8), (0x75 : u8),
    (0x6c : u8), (0x64 : u8), (0x20 : u8), (0x6f : u8), (0x66 : u8),
    (0x66 : u8), (0x65 : u8), (0x72 : u8), (0x20 : u8), (0x79 : u8),
    (0x6f : u8), (0x75 : u8), (0x20 : u8), (0x6f : u8), (0x6e : u8),
    (0x6c : u8), (0x79 : u8), (0x20 : u8), (0x6f : u8), (0x6e : u8),
    (0x65 : u8), (0x20 : u8), (0x74 : u8), (0x69 : u8), (0x70 : u8),
    (0x20 : u8), (0x66 : u8), (0x6f : u8), (0x72 : u8), (0x20 : u8),
    (0x74 : u8), (0x68 : u8), (0x65 : u8), (0x20 : u8), (0x66 : u8),
    (0x75 : u8), (0x74 : u8), (0x75 : u8), (0x72 : u8), (0x65 : u8),
    (0x2c : u8), (0x20 : u8), (0x73 : u8), (0x75 : u8), (0x6e : u8),
    (0x73 : u8), (0x63 : u8), (0x72 : u8), (0x65 : u8), (0x65 : u8),
    (0x6e : u8), (0x20 : u8), (0x77 : u8), (0x6f : u8), (0x75 : u8),
    (0x6c : u8), (0x64 : u8), (0x20 : u8), (0x62 : u8), (0x65 : u8),
    (0x20 : u8), (0x69 : u8), (0x74 : u8), (0x2e : u8)]

private theorem rfc_plaintext_bytes_size :
    rfc_plaintext_bytes.size < USize64.size := by
  unfold rfc_plaintext_bytes
  decide

private def rfc_plaintext : RustSlice u8 :=
  ⟨rfc_plaintext_bytes, rfc_plaintext_bytes_size⟩

private def rfc_expected_bytes : Array u8 :=
  #[(0x6e : u8), (0x2e : u8), (0x35 : u8), (0x9a : u8), (0x25 : u8),
    (0x68 : u8), (0xf9 : u8), (0x80 : u8), (0x41 : u8), (0xba : u8),
    (0x07 : u8), (0x28 : u8), (0xdd : u8), (0x0d : u8), (0x69 : u8),
    (0x81 : u8), (0xe9 : u8), (0x7e : u8), (0x7a : u8), (0xec : u8),
    (0x1d : u8), (0x43 : u8), (0x60 : u8), (0xc2 : u8), (0x0a : u8),
    (0x27 : u8), (0xaf : u8), (0xcc : u8), (0xfd : u8), (0x9f : u8),
    (0xae : u8), (0x0b : u8), (0xf9 : u8), (0x1b : u8), (0x65 : u8),
    (0xc5 : u8), (0x52 : u8), (0x47 : u8), (0x33 : u8), (0xab : u8),
    (0x8f : u8), (0x59 : u8), (0x3d : u8), (0xab : u8), (0xcd : u8),
    (0x62 : u8), (0xb3 : u8), (0x57 : u8), (0x16 : u8), (0x39 : u8),
    (0xd6 : u8), (0x24 : u8), (0xe6 : u8), (0x51 : u8), (0x52 : u8),
    (0xab : u8), (0x8f : u8), (0x53 : u8), (0x0c : u8), (0x35 : u8),
    (0x9f : u8), (0x08 : u8), (0x61 : u8), (0xd8 : u8), (0x07 : u8),
    (0xca : u8), (0x0d : u8), (0xbf : u8), (0x50 : u8), (0x0d : u8),
    (0x6a : u8), (0x61 : u8), (0x56 : u8), (0xa3 : u8), (0x8e : u8),
    (0x08 : u8), (0x8a : u8), (0x22 : u8), (0xb6 : u8), (0x5e : u8),
    (0x52 : u8), (0xbc : u8), (0x51 : u8), (0x4d : u8), (0x16 : u8),
    (0xcc : u8), (0xf8 : u8), (0x06 : u8), (0x81 : u8), (0x8c : u8),
    (0xe9 : u8), (0x1a : u8), (0xb7 : u8), (0x79 : u8), (0x37 : u8),
    (0x36 : u8), (0x5a : u8), (0xf9 : u8), (0x0b : u8), (0xbf : u8),
    (0x74 : u8), (0xa3 : u8), (0x5b : u8), (0xe6 : u8), (0xb4 : u8),
    (0x0b : u8), (0x8e : u8), (0xed : u8), (0xf2 : u8), (0x78 : u8),
    (0x5e : u8), (0x42 : u8), (0x87 : u8), (0x4d : u8)]

/--
RFC 8439 §2.4.2 known-answer test vector: with the published
`(key, iv, plaintext, ctr = 1)`, `chacha20` produces the published
ciphertext byte-for-byte.

Proved by `native_decide` once a local `DecidableEq (Seq u8)` is in
scope. The default `RustM` `DecidableEq` instance needs the value type
to be decidably-equal, and `Seq u8` is a structure with a `Prop` field
(`size_lt_usizeSize`), which the default deriving handler does not
pick up; the helper instance above closes that gap. With it,
`native_decide` compiles and runs the 20-round ChaCha20 stream on the
concrete 114-byte plaintext and verifies the result matches RFC 8439
§2.4.2 byte-for-byte.
-/
private instance : DecidableEq (rust_primitives.sequence.Seq u8) := fun a b =>
  if h : a.val = b.val then
    .isTrue (by cases a; cases b; congr)
  else
    .isFalse (fun heq => h (by rw [heq]))

theorem chacha20_rfc8439_kat :
    ∃ c : alloc.vec.Vec u8 alloc.alloc.Global,
      chacha20.chacha20 rfc_plaintext rfc_key rfc_iv (1 : u32) = RustM.ok c
      ∧ c.val = rfc_expected_bytes := by
  refine ⟨⟨rfc_expected_bytes, by decide⟩, ?_, rfl⟩
  native_decide

end Chacha20Obligations
