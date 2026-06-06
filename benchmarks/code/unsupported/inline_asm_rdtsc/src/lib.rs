//! Unsupported: inline assembly. Opaque to all source-level analysis;
//! Hax cannot model `asm!` any more than it can model `unsafe`.
//! This crate is x86_64-only. On other targets the body is gated out so
//! the crate compiles but doesn't exercise the `asm!` path.

#[cfg(target_arch = "x86_64")]
pub fn rdtsc() -> u64 {
    let lo: u32;
    let hi: u32;
    unsafe {
        core::arch::asm!("rdtsc", out("eax") lo, out("edx") hi);
    }
    ((hi as u64) << 32) | (lo as u64)
}

#[cfg(not(target_arch = "x86_64"))]
pub fn rdtsc() -> u64 {
    0
}
