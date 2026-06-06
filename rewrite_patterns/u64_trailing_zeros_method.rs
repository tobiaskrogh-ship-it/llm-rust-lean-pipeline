// unsupported: `u64::trailing_zeros` (and the sibling `leading_zeros`,
// `count_ones`, `count_zeros`, `swap_bytes`, etc. on integer impl blocks
// without a Hax model). Extraction succeeds and emits a call to
// `core_models.num.Impl_9.trailing_zeros`, but the Hax Lean prelude has
// no definition for that identifier, so `lake build` fails with
// `Unknown identifier 'core_models.num.Impl_9.trailing_zeros'`.
// Workaround: inline a primitive Rust implementation using a shift-and-count
// `while` loop. `>>` / `&` / `==` over `u64` and `u32` all have Hax models.

// before

fn gcd_u64(x: u64, y: u64) -> u64 {
    let mut m = x;
    let mut n = y;
    if m == 0 || n == 0 {
        return m | n;
    }
    let shift = (m | n).trailing_zeros();
    m >>= m.trailing_zeros();
    n >>= n.trailing_zeros();
    while m != n {
        if m > n {
            m -= n;
            m >>= m.trailing_zeros();
        } else {
            n -= m;
            n >>= n.trailing_zeros();
        }
    }
    m << shift
}

// after

fn trailing_zeros_u64(x: u64) -> u32 {
    if x == 0 {
        return 64;
    }
    let mut y = x;
    let mut count: u32 = 0;
    while y & 1 == 0 {
        y >>= 1;
        count = count + 1;
    }
    count
}

fn gcd_u64(x: u64, y: u64) -> u64 {
    let mut m = x;
    let mut n = y;
    if m == 0 || n == 0 {
        return m | n;
    }
    let shift = trailing_zeros_u64(m | n);
    m >>= trailing_zeros_u64(m);
    n >>= trailing_zeros_u64(n);
    while m != n {
        if m > n {
            m -= n;
            m >>= trailing_zeros_u64(m);
        } else {
            n -= m;
            n >>= trailing_zeros_u64(n);
        }
    }
    m << shift
}
