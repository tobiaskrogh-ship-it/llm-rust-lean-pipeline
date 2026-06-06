//! Unsupported (likely): `let`-chains in `if` conditions
//! (`if let Some(a) = x && let Some(b) = y`). Stabilised in Rust 1.88
//! / edition 2024; the construct desugars into a nested pattern that
//! Hax's expression printer doesn't yet emit cleanly.

pub fn sum_options(x: Option<u32>, y: Option<u32>) -> u32 {
    if let Some(a) = x && let Some(b) = y {
        a + b
    } else {
        0
    }
}
