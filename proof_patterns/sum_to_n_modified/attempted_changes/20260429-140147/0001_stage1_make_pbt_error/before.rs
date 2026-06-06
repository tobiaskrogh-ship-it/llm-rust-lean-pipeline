fn sum_to_n(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        n + sum_to_n(n - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
