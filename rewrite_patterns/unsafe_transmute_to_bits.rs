// unsupported: `unsafe` blocks reinterpreting one type's bytes as another's
// via raw pointer casts (`*(p as *const f64 as *const u64)`) or
// `core::mem::transmute`. Hax has no model for raw pointer reinterpretation;
// extraction either fails or produces Lean that doesn't compile.

// before

fn from_slice_f64(numbers: &mut [f64]) {
    if cfg!(target_endian = "little") {
        for n in numbers {
            let int = unsafe { *(n as *const f64 as *const u64) };
            let swapped = int.to_be();
            *n = unsafe { *(&swapped as *const u64 as *const f64) };
        }
    }
}

// after

fn from_slice_f64(numbers: &mut [f64]) {
    if cfg!(target_endian = "little") {
        for n in numbers {
            let int = n.to_bits();
            *n = f64::from_bits(int.to_be());
        }
    }
}
