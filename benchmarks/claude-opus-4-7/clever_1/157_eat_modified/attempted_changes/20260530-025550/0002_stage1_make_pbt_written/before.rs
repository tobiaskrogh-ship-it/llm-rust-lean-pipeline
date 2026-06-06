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
    #[test]
    fn known() {
        assert_eq!(eat(5, 6, 10), vec![11, 4]);
        assert_eq!(eat(4, 8, 9), vec![12, 1]);
        assert_eq!(eat(1, 10, 10), vec![11, 0]);
        assert_eq!(eat(2, 11, 5), vec![7, 0]);
        assert_eq!(eat(4, 5, 7), vec![9, 2]);
        assert_eq!(eat(4, 5, 1), vec![5, 0]);
    }
}
