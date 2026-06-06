pub fn clamp(x: u8, lo: u8, hi: u8) -> u8 {
    if x < lo { lo } else if x > hi { hi } else { x }
}

#[cfg(test)]
mod tests {
    use super::*;

}
