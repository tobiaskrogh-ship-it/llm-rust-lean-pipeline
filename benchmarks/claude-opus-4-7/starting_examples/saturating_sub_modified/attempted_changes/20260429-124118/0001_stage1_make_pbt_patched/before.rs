pub fn saturating_sub(a: u8, b: u8) -> u8 {
    if a > b { a - b } else { 0 }
}


#[cfg(test)]
mod tests {
    use super::*;

}
