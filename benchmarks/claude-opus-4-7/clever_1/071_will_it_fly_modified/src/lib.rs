/// HumanEval/72 / CLEVER 071 — `will_it_fly(q, w)`.  Return true iff
/// `q` is a palindromic list AND `sum(q) ≤ w`.  Empty list is trivially
/// palindromic; its sum is 0.
fn sum_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() {
        acc
    } else {
        sum_at(l, i + 1, acc + l[i])
    }
}

fn is_palindrome_at(q: &[i64], i: usize, j: usize) -> bool {
    if i >= j {
        true
    } else if q[i] != q[j] {
        false
    } else {
        is_palindrome_at(q, i + 1, j - 1)
    }
}

pub fn will_it_fly(q: &[i64], w: i64) -> bool {
    if sum_at(q, 0, 0) > w {
        false
    } else if q.is_empty() {
        true
    } else {
        is_palindrome_at(q, 0, q.len() - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn is_palindrome(q: &[i64]) -> bool {
        let r: Vec<i64> = q.iter().rev().copied().collect();
        q == r.as_slice()
    }

    #[test]
    fn small_cases() {
        assert!(will_it_fly(&[], 0));
        assert!(will_it_fly(&[1], 1));
        assert!(!will_it_fly(&[1], 0));         // sum > w
        assert!(will_it_fly(&[1, 2, 1], 5));    // palindrome, sum=4 ≤ 5
        assert!(!will_it_fly(&[1, 2, 1], 3));   // palindrome but sum=4 > 3
        assert!(!will_it_fly(&[1, 2, 3], 100)); // sum OK but not palindrome
        assert!(will_it_fly(&[3, 2, 3], 10));
    }

    proptest! {
        // Contract clause 1 (necessity of weight bound):
        // sum(q) > w  ⇒  will_it_fly(q, w) = false.
        #[test]
        fn sum_exceeds_w_means_false(
            q in proptest::collection::vec(-100i64..=100, 0..10),
            w in -1000i64..=1000,
        ) {
            let s: i64 = q.iter().sum();
            prop_assume!(s > w);
            prop_assert!(!will_it_fly(&q, w));
        }

        // Contract clause 2 (necessity of palindrome):
        // ¬palindrome(q)  ⇒  will_it_fly(q, w) = false,
        // regardless of w.  Length ≥ 2 because lists of length 0 or 1 are
        // always palindromic and would just be rejected by the assumption.
        #[test]
        fn nonpalindrome_means_false(
            q in proptest::collection::vec(-100i64..=100, 2..10),
            w in -1000i64..=1000,
        ) {
            prop_assume!(!is_palindrome(&q));
            prop_assert!(!will_it_fly(&q, w));
        }

        // Contract clause 3 (sufficiency):
        // palindrome(q) ∧ sum(q) ≤ w  ⇒  will_it_fly(q, w) = true.
        // We construct a palindrome of the form  half ++ [middle?] ++ rev(half)
        // so this branch is actually exercised — random vectors of length ≥ 3
        // are palindromes only by accident.
        #[test]
        fn palindrome_with_room_is_true(
            half in proptest::collection::vec(-100i64..=100, 0..5),
            include_middle in any::<bool>(),
            middle in -100i64..=100,
            extra in 0i64..=1000,
        ) {
            let mut q = half.clone();
            if include_middle {
                q.push(middle);
            }
            for &x in half.iter().rev() {
                q.push(x);
            }
            // q is a palindrome by construction.
            let s: i64 = q.iter().sum();
            let w = s.saturating_add(extra); // sum ≤ w by construction
            prop_assert!(will_it_fly(&q, w));
        }
    }
}
