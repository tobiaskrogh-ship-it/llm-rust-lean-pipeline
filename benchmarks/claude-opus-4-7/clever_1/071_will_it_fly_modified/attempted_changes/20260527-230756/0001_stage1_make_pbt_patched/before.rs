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

    fn naive(q: &[i64], w: i64) -> bool {
        let s: i64 = q.iter().sum();
        if s > w { return false; }
        let r: Vec<i64> = q.iter().rev().copied().collect();
        q.to_vec() == r
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
        #[test]
        fn matches_brute_force(
            q in proptest::collection::vec(-100i64..=100, 0..10),
            w in -1000i64..=1000,
        ) {
            prop_assert_eq!(will_it_fly(&q, w), naive(&q, w));
        }
    }
}
