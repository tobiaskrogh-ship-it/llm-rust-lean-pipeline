/// HumanEval/130 / CLEVER 129 — `tri(n)`.  Return the first `n + 1`
/// terms of the recurrence:
///   tri(1) = 3,  tri(n)     = 1 + n/2  if n is even,
///                tri(n)     = tri(n-1) + tri(n-2) + tri(n+1)  if n is odd.
/// Non-negative `n`, so use `u64`.
///
/// The trick: for odd n, expanding the recurrence and tri(n+1) (even)
/// gives a closed form so this is computable without forward references.
/// tri(0) is unspecified; we return 3 (matches Python solutions in the wild).
pub fn tri(n: u64) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::new();
    let mut i = 0u64;
    while i <= n {
        let v = if i == 0 {
            3
        } else if i == 1 {
            3
        } else if i % 2 == 0 {
            1 + i / 2
        } else {
            // For odd i ≥ 3: tri(i) = tri(i-1) + tri(i-2) + tri(i+1)
            //   tri(i-1) = 1 + (i-1)/2
            //   tri(i-2) = previous odd's value (already computed → out[i-2])
            //   tri(i+1) = 1 + (i+1)/2
            // Simplify: tri(i) = 1 + (i-1)/2 + out[(i-2) as usize] + 1 + (i+1)/2.
            let prev_odd = out[(i - 2) as usize];
            let a = 1 + (i - 1) / 2;
            let b = 1 + (i + 1) / 2;
            a + prev_odd + b
        };
        out.push(v);
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        // tri(3) = tri(2) + tri(1) + tri(4) = 2 + 3 + 3 = 8
        // tri(2) = 1 + 2/2 = 2; tri(4) = 1 + 4/2 = 3
        let r = tri(4);
        assert_eq!(r[1], 3);    // tri(1)
        assert_eq!(r[2], 2);    // tri(2)
        assert_eq!(r[3], 8);    // tri(3)
        assert_eq!(r[4], 3);    // tri(4)
    }
}
