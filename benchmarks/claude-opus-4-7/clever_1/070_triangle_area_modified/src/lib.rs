/// HumanEval/71 / CLEVER 070 — `triangle_area(a, b, c)`.  Return the area
/// of the triangle with sides `a`, `b`, `c`, rounded to two decimal
/// places, IF the sides form a valid triangle.  Otherwise return `-1`.
///
/// "Valid triangle" iff the sum of any two sides is strictly greater
/// than the third.
///
/// Integer adaptation: the canonical signature returns `i64`, so we
/// encode the "rounded to 2 decimal places" area as `floor(100 * area)`.
/// Heron's formula gives `16 * area² = (a+b+c)(b+c-a)(a-b+c)(a+b-c)`,
/// so `100 * area = floor(sqrt(s2 * 10000) / 4)` where
/// `s2 = (a+b+c)(b+c-a)(a-b+c)(a+b-c)`.
///
/// `isqrt` uses binary search on the recursion structure, so the
/// recursion depth is O(log n) — well inside any test-thread stack
/// limit even at the upper end of the test input range.
fn isqrt_bin(n: i64, lo: i64, hi: i64) -> i64 {
    if hi - lo <= 1 {
        lo
    } else {
        let mid = (lo + hi) / 2;
        if mid * mid <= n {
            isqrt_bin(n, mid, hi)
        } else {
            isqrt_bin(n, lo, mid)
        }
    }
}

fn isqrt(n: i64) -> i64 {
    if n <= 0 {
        0
    } else {
        // `floor(sqrt(i64::MAX)) = 3_037_000_499`.  Starting `hi` at the
        // smallest value > floor(sqrt(i64::MAX)) ensures `mid * mid`
        // inside the binary search never overflows `i64`.
        isqrt_bin(n, 0, 3_037_000_500)
    }
}

pub fn triangle_area(a: i64, b: i64, c: i64) -> i64 {
    if a + b <= c || a + c <= b || b + c <= a {
        -1
    } else {
        let s2 = (a + b + c) * (b + c - a) * (a - b + c) * (a + b - c);
        isqrt(s2 * 10000) / 4
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(a: i64, b: i64, c: i64) -> i64 {
        if a + b <= c || a + c <= b || b + c <= a {
            return -1;
        }
        // Use f64 then take floor of 100*area as the oracle.
        let s = (a + b + c) as f64 / 2.0;
        let area = (s * (s - a as f64) * (s - b as f64) * (s - c as f64)).sqrt();
        (area * 100.0).floor() as i64
    }

    #[test]
    fn known_cases() {
        // 3-4-5 right triangle has area = 6.00 → 600
        assert_eq!(triangle_area(3, 4, 5), 600);
        // 6-8-10 right triangle has area = 24.00 → 2400
        assert_eq!(triangle_area(6, 8, 10), 2400);
        // Degenerate / invalid
        assert_eq!(triangle_area(1, 2, 10), -1);
        assert_eq!(triangle_area(1, 2, 3), -1);  // a+b == c
    }

    proptest! {
        /// Matches f64 oracle up to floor-rounding, on a bounded range.
        #[test]
        fn matches_oracle(a in 1i64..=30, b in 1i64..=30, c in 1i64..=30) {
            let r = triangle_area(a, b, c);
            let o = naive(a, b, c);
            if r == -1 {
                prop_assert_eq!(o, -1);
            } else {
                // floor-of-sqrt may differ by 1 from the f64 oracle due to
                // rounding direction; accept r in [o-1, o+1].
                prop_assert!((r - o).abs() <= 1, "r={} o={}", r, o);
            }
        }

        /// Returns -1 iff the triangle is invalid.
        #[test]
        fn invalid_iff_minus_one(a in 1i64..=30, b in 1i64..=30, c in 1i64..=30) {
            let valid = a + b > c && a + c > b && b + c > a;
            let r = triangle_area(a, b, c);
            if valid { prop_assert!(r >= 0); }
            else     { prop_assert_eq!(r, -1); }
        }
    }
}
