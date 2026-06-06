fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
