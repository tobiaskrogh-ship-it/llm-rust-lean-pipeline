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

    #[test]
    fn doubles_correctly_via_closure() {
        assert_eq!(apply_twice(3u64, |x| x + 1), 5);
    }

    #[test]
    fn squaring_via_function_pointer() {
        fn sq(n: i64) -> i64 {
            n * n
        }
        assert_eq!(apply_twice(2i64, sq), 16);
    }
}
