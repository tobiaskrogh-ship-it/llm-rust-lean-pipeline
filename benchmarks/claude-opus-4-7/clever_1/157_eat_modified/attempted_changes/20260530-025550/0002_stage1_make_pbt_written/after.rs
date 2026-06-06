/// HumanEval/159 / CLEVER 157 — `eat(number, need, remaining)`.
/// You've already eaten `number` carrots, you need to eat `need` more.
/// Return `[total_eaten, remaining_after]`.  If `remaining < need`,
/// you eat all remaining carrots.
pub fn eat(number: u64, need: u64, remaining: u64) -> Vec<u64> {
    let mut result: Vec<u64> = Vec::new();
    if remaining >= need {
        result.push(number + need);
        result.push(remaining - need);
    } else {
        result.push(number + remaining);
        result.push(0);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(eat(5, 6, 10), vec![11, 4]);
        assert_eq!(eat(4, 8, 9), vec![12, 1]);
        assert_eq!(eat(1, 10, 10), vec![11, 0]);
        assert_eq!(eat(2, 11, 5), vec![7, 0]);
        assert_eq!(eat(4, 5, 7), vec![9, 2]);
        assert_eq!(eat(4, 5, 1), vec![5, 0]);
    }

    // Inputs are bounded so `number + need` and `number + remaining`
    // never overflow u64 (precondition of the function).
    proptest! {
        // Shape: the returned vector always has exactly two elements.
        #[test]
        fn length_is_two(
            number in 0u64..1_000_000,
            need in 0u64..1_000_000,
            remaining in 0u64..1_000_000,
        ) {
            let r = eat(number, need, remaining);
            prop_assert_eq!(r.len(), 2);
        }

        // Conservation: total carrots eaten plus carrots left equals
        // the carrots that were eaten before plus the carrots that
        // were available. No carrots are created or destroyed.
        #[test]
        fn conservation(
            number in 0u64..1_000_000,
            need in 0u64..1_000_000,
            remaining in 0u64..1_000_000,
        ) {
            let r = eat(number, need, remaining);
            prop_assert_eq!(r[0] + r[1], number + remaining);
        }

        // You never un-eat (r[0] >= number) and you eat at most `need`
        // carrots this round (r[0] - number <= need).
        #[test]
        fn eat_at_most_need(
            number in 0u64..1_000_000,
            need in 0u64..1_000_000,
            remaining in 0u64..1_000_000,
        ) {
            let r = eat(number, need, remaining);
            prop_assert!(r[0] >= number);
            prop_assert!(r[0] - number <= need);
        }

        // You eat as much as possible: either your full `need` was
        // satisfied (r[0] == number + need), or no carrots are left
        // (r[1] == 0). Together with conservation and "eat at most
        // need" this forces r[0] - number == min(need, remaining).
        #[test]
        fn sated_or_finished(
            number in 0u64..1_000_000,
            need in 0u64..1_000_000,
            remaining in 0u64..1_000_000,
        ) {
            let r = eat(number, need, remaining);
            prop_assert!(r[0] == number + need || r[1] == 0);
        }
    }
}
