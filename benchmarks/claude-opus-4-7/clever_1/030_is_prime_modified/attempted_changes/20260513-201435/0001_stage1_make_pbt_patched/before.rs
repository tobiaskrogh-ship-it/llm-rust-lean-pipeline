/// Return true iff n is prime. (Return type corrected from CLEVER's
/// auto-defaulted `u64` to `bool` to match the docstring.)
fn has_divisor_at(n: u64, d: u64) -> bool {
    if d * d > n {
        false
    } else if n % d == 0 {
        true
    } else {
        has_divisor_at(n, d + 1)
    }
}

pub fn is_prime(n: u64) -> bool {
    if n < 2 {
        false
    } else {
        !has_divisor_at(n, 2)
    }
}
