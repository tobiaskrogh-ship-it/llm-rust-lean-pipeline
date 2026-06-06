//! Unsupported: `async fn`. The async desugaring (state machines,
//! `Future` polling, generators) has no Lean encoding. Hax targets
//! pure functional translation.

pub async fn double(x: u64) -> u64 {
    x * 2
}
