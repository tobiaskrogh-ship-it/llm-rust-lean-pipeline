/// HumanEval/77 — `iscube(n)`.  Return true iff `n` is a perfect cube.
/// Negative inputs map by `-n = m^3` ⇔ `n = (-m)^3`, so a negative
/// `n` is a cube iff `|n|` is.
fn cube_walks_to(n: i64, k: i64) -> bool {
    let cube = k * k * k;
    if cube == n {
        true
    } else if cube > n {
        false
    } else {
        cube_walks_to(n, k + 1)
    }
}

pub fn iscube(n: i64) -> bool {
    if n < 0 {
        // `-n` could overflow at i64::MIN; the property tests stay well
        // inside that range.
        cube_walks_to(-n, 0)
    } else {
        cube_walks_to(n, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force oracle.
    fn naive_iscube(n: i64) -> bool {
        let target = if n < 0 { -n } else { n } as i128;
        let mut k: i128 = 0;
        while k * k * k < target {
            k += 1;
        }
        k * k * k == target
    }

    /// Known cases.
    #[test]
    fn small_cases() {
        assert!(iscube(0));
        assert!(iscube(1));
        assert!(iscube(8));
        assert!(iscube(27));
        assert!(iscube(64));
        assert!(iscube(125));
        assert!(iscube(-1));
        assert!(iscube(-8));
        assert!(iscube(-27));
        assert!(!iscube(2));
        assert!(!iscube(9));
        assert!(!iscube(26));
        assert!(!iscube(28));
    }

    proptest! {
        /// Postcondition: matches brute-force oracle.
        /// Bounded so `k*k*k` fits in i64.
        #[test]
        fn matches_brute_force(n in -(1i64 << 30)..=(1i64 << 30)) {
            prop_assert_eq!(iscube(n), naive_iscube(n));
        }

        /// Soundness: if reported true, exists `k` with `k^3 == n`.
        #[test]
        fn soundness(n in -(1i64 << 30)..=(1i64 << 30)) {
            if iscube(n) {
                let target = if n < 0 { -n } else { n };
                let mut found = false;
                for k in 0i64..=2048 {
                    if k * k * k == target {
                        found = true;
                        break;
                    }
                    if k * k * k > target {
                        break;
                    }
                }
                prop_assert!(found);
            }
        }

        /// Completeness: every cube `k^3` (positive or negative) is recognized.
        /// `|k| <= 1024` keeps `k*k*k` within the i64 range used elsewhere
        /// and ensures random draws actually land on cubes (which is
        /// vanishingly unlikely under `matches_brute_force`'s uniform draw).
        #[test]
        fn completeness(k in -1024i64..=1024) {
            prop_assert!(iscube(k * k * k));
        }
    }
}
