pub fn apply_twice<T, F>(x: T, f: F) -> T
where
    T: Copy,
    F: Fn(T) -> T,
{
    f(f(x))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Postcondition: apply_twice(x, f) == f(f(x)).
    // Checked over a range of inputs with an additive f.
    // This single property captures the entire contract; testing with
    // an additive f distinguishes apply_twice from neighboring buggy
    // implementations that would return x (0 applications), f(x) (1),
    // or f(f(f(x))) (3) — since with f = (+1) those produce x, x+1, x+3
    // respectively, all different from the expected x+2.
    #[test]
    fn returns_f_applied_twice_additive() {
        let f = |n: i64| n + 1;
        for x in -1000i64..=1000 {
            assert_eq!(apply_twice(x, f), f(f(x)));
        }
    }

    // Same postcondition with a multiplicative f. This guards against
    // implementations that happen to be correct only for additive f
    // (e.g. an off-by-one in the number of applications that coincidentally
    // matches an additive f under some bug, or an implementation that
    // returns x + (f(x) - x) * 2 instead of f(f(x))).
    #[test]
    fn returns_f_applied_twice_multiplicative() {
        let f = |n: i32| n * 3;
        for x in -100i32..=100 {
            assert_eq!(apply_twice(x, f), f(f(x)));
        }
    }
}
