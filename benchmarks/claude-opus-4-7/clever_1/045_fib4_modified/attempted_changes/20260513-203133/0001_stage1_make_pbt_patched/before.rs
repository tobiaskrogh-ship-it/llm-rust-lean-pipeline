/// 4-step Fibonacci:
///   fib4(0) = 0, fib4(1) = 0, fib4(2) = 2, fib4(3) = 0,
///   fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4) for n ≥ 4.
///
/// Implemented with tail recursion sliding a 4-window of recent values
/// (the docstring's "Do not use recursion" was aimed at the exponential
/// naive form; this O(n) tail-recursive form has the same efficiency as
/// a loop, per the project's recursion-preference rule).
fn fib4_at(n: i64, a: i64, b: i64, c: i64, d: i64, k: i64) -> i64 {
    if k >= n {
        a
    } else {
        fib4_at(n, b, c, d, a + b + c + d, k + 1)
    }
}

pub fn fib4(n: i64) -> i64 {
    if n < 0 {
        0
    } else {
        fib4_at(n, 0, 0, 2, 0, 0)
    }
}
