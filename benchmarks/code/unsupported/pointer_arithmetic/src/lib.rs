//! Unsupported: raw pointer arithmetic. `p.add(1)` advances `p` by one
//! element-stride; Hax has no model of pointer addresses.

pub unsafe fn next(p: *const u64) -> *const u64 {
    unsafe { p.add(1) }
}
