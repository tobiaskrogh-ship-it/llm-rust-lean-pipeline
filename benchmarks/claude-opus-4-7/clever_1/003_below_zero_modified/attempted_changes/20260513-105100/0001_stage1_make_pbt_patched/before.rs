/// Given a list of deposit and withdrawal operations on an account that
/// starts at zero, return true iff the balance ever falls below zero.
pub fn below_zero(operations: &[i64]) -> bool {
    let mut balance: i64 = 0;
    for &op in operations {
        balance += op;
        if balance < 0 {
            return true;
        }
    }
    false
}
