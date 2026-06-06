mod hacspec_helper;
use hacspec_helper::*;

pub type State = [u32; 16];
pub type Block = [u8; 64];
pub type ChaChaIV = [u8; 12];
pub type ChaChaKey = [u8; 32];

// One ARX line of a ChaCha20 quarter round. Caller must pass a, b, d < 16.
fn chacha20_line(a: usize, b: usize, d: usize, s: u32, m: State) -> State {
    let mut state = m;
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}

/// Quarter round operating on four state words. Caller must pass a, b, c, d < 16.
pub fn chacha20_quarter_round(
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    state: State,
) -> State {
    let state = chacha20_line(a, b, d, 16, state);
    let state = chacha20_line(c, d, b, 12, state);
    let state = chacha20_line(a, b, d, 8, state);
    chacha20_line(c, d, b, 7, state)
}

// One double round = 4 column quarter rounds + 4 diagonal quarter rounds.
fn chacha20_double_round(state: State) -> State {
    let state = chacha20_quarter_round(0, 4, 8, 12, state);
    let state = chacha20_quarter_round(1, 5, 9, 13, state);
    let state = chacha20_quarter_round(2, 6, 10, 14, state);
    let state = chacha20_quarter_round(3, 7, 11, 15, state);

    let state = chacha20_quarter_round(0, 5, 10, 15, state);
    let state = chacha20_quarter_round(1, 6, 11, 12, state);
    let state = chacha20_quarter_round(2, 7, 8, 13, state);
    chacha20_quarter_round(3, 4, 9, 14, state)
}

// Recursive helper for chacha20_rounds: `for _ in 0..10` doesn't extract
// cleanly through hax's fold typeclass.
fn chacha20_rounds_at(state: State, i: u32) -> State {
    if i >= 10 {
        state
    } else {
        chacha20_rounds_at(chacha20_double_round(state), i + 1)
    }
}

pub fn chacha20_rounds(state: State) -> State {
    chacha20_rounds_at(state, 0)
}

pub fn chacha20_core(ctr: u32, st0: State) -> State {
    let mut state = st0;
    state[12] = state[12].wrapping_add(ctr);
    let k = chacha20_rounds(state);
    add_state(state, k)
}

pub fn chacha20_init(key: &ChaChaKey, iv: &ChaChaIV, ctr: u32) -> State {
    let key_u32: [u32; 8] = to_le_u32s_8(key);
    let iv_u32: [u32; 3] = to_le_u32s_3(iv);
    [
        0x6170_7865,
        0x3320_646e,
        0x7962_2d32,
        0x6b20_6574,
        key_u32[0],
        key_u32[1],
        key_u32[2],
        key_u32[3],
        key_u32[4],
        key_u32[5],
        key_u32[6],
        key_u32[7],
        ctr,
        iv_u32[0],
        iv_u32[1],
        iv_u32[2],
    ]
}

pub fn chacha20_key_block(state: State) -> Block {
    let state = chacha20_core(0u32, state);
    u32s_to_le_bytes(&state)
}

pub fn chacha20_key_block0(key: &ChaChaKey, iv: &ChaChaIV) -> Block {
    let state = chacha20_init(key, iv, 0u32);
    chacha20_key_block(state)
}

pub fn chacha20_encrypt_block(st0: State, ctr: u32, plain: &Block) -> Block {
    let st = chacha20_core(ctr, st0);
    let pl: State = to_le_u32s_16(plain);
    let encrypted = xor_state(st, pl);
    u32s_to_le_bytes(&encrypted)
}

/// Encrypt a partial final block. Caller must pass plain.len() <= 64.
pub fn chacha20_encrypt_last(st0: State, ctr: u32, plain: &[u8]) -> Vec<u8> {
    let mut b: Block = [0; 64];
    b = update_array(b, plain);
    b = chacha20_encrypt_block(st0, ctr, &b);
    b[0..plain.len()].to_vec()
}

// Recursive helper for chacha20_update: full-block loop. `for i in 0..num_blocks`
// with a Vec accumulator doesn't extract cleanly without hax assume! annotations.
fn chacha20_update_blocks(
    st0: State,
    m: &[u8],
    i: usize,
    num_blocks: usize,
    acc: Vec<u8>,
) -> Vec<u8> {
    if i >= num_blocks {
        acc
    } else {
        let block: [u8; 64] = m[64 * i..(64 * i + 64)].try_into().unwrap();
        let b = chacha20_encrypt_block(st0, i as u32, &block);
        let mut acc = acc;
        acc.extend_from_slice(&b);
        chacha20_update_blocks(st0, m, i + 1, num_blocks, acc)
    }
}

pub fn chacha20_update(st0: State, m: &[u8]) -> Vec<u8> {
    let num_blocks = m.len() / 64;
    let remainder_len = m.len() % 64;
    let mut blocks_out = chacha20_update_blocks(st0, m, 0, num_blocks, Vec::new());
    if remainder_len != 0 {
        let b = chacha20_encrypt_last(st0, num_blocks as u32, &m[64 * num_blocks..m.len()]);
        blocks_out.extend_from_slice(&b);
    }
    blocks_out
}

pub fn chacha20(m: &[u8], key: &ChaChaKey, iv: &ChaChaIV, ctr: u32) -> Vec<u8> {
    let state = chacha20_init(key, iv, ctr);
    chacha20_update(state, m)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // RFC 8439 §2.4.2 test vector — the canonical ChaCha20 KAT.
    #[test]
    fn rfc8439_test_vector() {
        let key: ChaChaKey = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
            0x1c, 0x1d, 0x1e, 0x1f,
        ];
        let iv: ChaChaIV = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00, 0x00, 0x00,
        ];
        let plaintext: &[u8] = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        let expected: Vec<u8> = vec![
            0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80, 0x41, 0xba, 0x07, 0x28, 0xdd, 0x0d,
            0x69, 0x81, 0xe9, 0x7e, 0x7a, 0xec, 0x1d, 0x43, 0x60, 0xc2, 0x0a, 0x27, 0xaf, 0xcc,
            0xfd, 0x9f, 0xae, 0x0b, 0xf9, 0x1b, 0x65, 0xc5, 0x52, 0x47, 0x33, 0xab, 0x8f, 0x59,
            0x3d, 0xab, 0xcd, 0x62, 0xb3, 0x57, 0x16, 0x39, 0xd6, 0x24, 0xe6, 0x51, 0x52, 0xab,
            0x8f, 0x53, 0x0c, 0x35, 0x9f, 0x08, 0x61, 0xd8, 0x07, 0xca, 0x0d, 0xbf, 0x50, 0x0d,
            0x6a, 0x61, 0x56, 0xa3, 0x8e, 0x08, 0x8a, 0x22, 0xb6, 0x5e, 0x52, 0xbc, 0x51, 0x4d,
            0x16, 0xcc, 0xf8, 0x06, 0x81, 0x8c, 0xe9, 0x1a, 0xb7, 0x79, 0x37, 0x36, 0x5a, 0xf9,
            0x0b, 0xbf, 0x74, 0xa3, 0x5b, 0xe6, 0xb4, 0x0b, 0x8e, 0xed, 0xf2, 0x78, 0x5e, 0x42,
            0x87, 0x4d,
        ];
        let ciphertext = chacha20(plaintext, &key, &iv, 1u32);
        assert_eq!(ciphertext, expected);
        let decrypted = chacha20(&ciphertext, &key, &iv, 1u32);
        assert_eq!(decrypted, plaintext);
    }

    proptest! {
        // Postcondition: output length equals input length (covers all paths:
        // empty, partial-block-only, single-full-block, multi-block-plus-tail).
        #[test]
        fn output_length_equals_input_length(
            msg in prop::collection::vec(any::<u8>(), 0..200),
            key in prop::array::uniform32(any::<u8>()),
            iv in prop::array::uniform12(any::<u8>()),
            ctr in any::<u32>(),
        ) {
            let c = chacha20(&msg, &key, &iv, ctr);
            prop_assert_eq!(c.len(), msg.len());
        }

        // Postcondition: chacha20 is its own inverse (stream cipher property).
        // Encrypting the ciphertext under the same (key, iv, ctr) recovers
        // the plaintext.
        #[test]
        fn encryption_is_involution(
            msg in prop::collection::vec(any::<u8>(), 0..200),
            key in prop::array::uniform32(any::<u8>()),
            iv in prop::array::uniform12(any::<u8>()),
            ctr in any::<u32>(),
        ) {
            let c = chacha20(&msg, &key, &iv, ctr);
            let m2 = chacha20(&c, &key, &iv, ctr);
            prop_assert_eq!(m2, msg);
        }

        // chacha20_encrypt_block matches the first-block prefix of chacha20.
        #[test]
        fn encrypt_block_matches_full_chacha20(
            block_vec in prop::collection::vec(any::<u8>(), 64..=64),
            key in prop::array::uniform32(any::<u8>()),
            iv in prop::array::uniform12(any::<u8>()),
            ctr in any::<u32>(),
        ) {
            let block: Block = block_vec.as_slice().try_into().unwrap();
            let st0 = chacha20_init(&key, &iv, ctr);
            let block_out = chacha20_encrypt_block(st0, 0u32, &block);
            let chacha_out = chacha20(&block, &key, &iv, ctr);
            prop_assert_eq!(&block_out[..], &chacha_out[..]);
        }

        // chacha20_encrypt_last (precondition: plain.len() <= 64) matches the
        // first-`plain.len()` prefix of chacha20.
        #[test]
        fn encrypt_last_matches_full_chacha20_for_short_input(
            plain in prop::collection::vec(any::<u8>(), 0..=64),
            key in prop::array::uniform32(any::<u8>()),
            iv in prop::array::uniform12(any::<u8>()),
            ctr in any::<u32>(),
        ) {
            let st0 = chacha20_init(&key, &iv, ctr);
            let last_out = chacha20_encrypt_last(st0, 0u32, &plain);
            let chacha_out = chacha20(&plain, &key, &iv, ctr);
            prop_assert_eq!(last_out, chacha_out);
        }
    }
}
