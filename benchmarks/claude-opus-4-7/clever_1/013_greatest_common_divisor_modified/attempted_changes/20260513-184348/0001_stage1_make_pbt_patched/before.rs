/// Return the greatest common divisor of two non-negative integers.
pub fn greatest_common_divisor(a: u64, b: u64) -> u64 {
    let mut a = a;
    let mut b = b;
    while b != 0 {
        hax_lib::loop_decreases!(b);
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
