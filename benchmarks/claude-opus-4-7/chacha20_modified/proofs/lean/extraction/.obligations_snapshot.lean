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

/-- Postcondition: `chacha20` succeeds on every input, and the result has
exactly the same number of bytes as the input slice. Covers the
`output_length_equals_input_length` proptest (which also subsumes the
empty / single-block / partial-block / multi-block paths). -/
theorem chacha20_length_eq_input
    (m : RustSlice u8)
    (key : RustArray u8 32) (iv : RustArray u8 12) (ctr : u32) :
    ∃ r : alloc.vec.Vec u8 alloc.alloc.Global,
      chacha20.chacha20 m key iv ctr = RustM.ok r
      ∧ r.val.size = m.val.size := by
  sorry

/-- Postcondition: `chacha20` is an involution — encrypting the ciphertext
with the same `(key, iv, ctr)` recovers the plaintext. Covers the
`encryption_is_involution` proptest.

`RustSlice u8`, `alloc.vec.Vec u8 alloc.alloc.Global`, and
`rust_primitives.sequence.Seq u8` are all the same underlying type
(abbreviations), so feeding the ciphertext back into `chacha20` is well
typed without an explicit cast. -/
theorem chacha20_involution
    (m : RustSlice u8)
    (key : RustArray u8 32) (iv : RustArray u8 12) (ctr : u32) :
    ∃ c : alloc.vec.Vec u8 alloc.alloc.Global,
      chacha20.chacha20 m key iv ctr = RustM.ok c
      ∧ chacha20.chacha20 c key iv ctr = RustM.ok m := by
  sorry

/-- Postcondition: on a single 64-byte block, `chacha20_encrypt_block`
applied to the initial state and counter 0 produces exactly the same
ciphertext as `chacha20` on the same block. Covers the
`encrypt_block_matches_full_chacha20` proptest.

The four hypotheses package "all calls succeed" — totality of the
individual calls is captured by `chacha20_length_eq_input` and the
`@[spec]` totality of `chacha20_init` / `chacha20_encrypt_block`. -/
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
  sorry

/-- Postcondition: on a partial final block of length ≤ 64,
`chacha20_encrypt_last` applied to the initial state and counter 0
produces exactly the same ciphertext as `chacha20`. Covers the
`encrypt_last_matches_full_chacha20_for_short_input` proptest.

Precondition `plain.val.size ≤ 64` matches the Rust function's documented
contract ("Caller must pass plain.len() ≤ 64"). -/
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

/-- RFC 8439 §2.4.2 known-answer test vector: with the published
`(key, iv, plaintext, ctr = 1)`, `chacha20` produces the published
ciphertext byte-for-byte. -/
theorem chacha20_rfc8439_kat :
    ∃ c : alloc.vec.Vec u8 alloc.alloc.Global,
      chacha20.chacha20 rfc_plaintext rfc_key rfc_iv (1 : u32) = RustM.ok c
      ∧ c.val = rfc_expected_bytes := by
  sorry

end Chacha20Obligations
