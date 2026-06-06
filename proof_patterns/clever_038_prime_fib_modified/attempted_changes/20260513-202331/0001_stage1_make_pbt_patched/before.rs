/// Return the n-th prime Fibonacci number (n is 0-indexed: 0 → 2, 1 → 3,
/// 2 → 5, 3 → 13, …). CLEVER's Note(George) flags this depends on an
/// open conjecture about infinitely many prime Fibs.
fn has_divisor_at(n: u64, d: u64) -> bool {
    if d * d > n {
        false
    } else if n % d == 0 {
        true
    } else {
        has_divisor_at(n, d + 1)
    }
}

fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        false
    } else {
        !has_divisor_at(n, 2)
    }
}

fn prime_fib_at(target: u64, a: u64, b: u64, count: u64) -> u64 {
    let c = a + b;
    if is_prime_u64(c) {
        if count == target {
            c
        } else {
            prime_fib_at(target, b, c, count + 1)
        }
    } else {
        prime_fib_at(target, b, c, count)
    }
}

pub fn prime_fib(n: u64) -> u64 {
    prime_fib_at(n, 1, 1, 0)
}
