//! Unsupported: FFI / `extern "C"` blocks. External-language linkage
//! has nothing for Hax to translate — there's no Rust body to extract.

unsafe extern "C" {
    pub fn libc_strlen(s: *const u8) -> usize;
}

pub unsafe fn len(s: *const u8) -> usize {
    unsafe { libc_strlen(s) }
}
