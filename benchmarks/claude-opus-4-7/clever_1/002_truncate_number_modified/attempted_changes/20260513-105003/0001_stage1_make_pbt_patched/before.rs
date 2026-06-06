/// Given a positive floating point number, return its decimal part
/// (the leftover after subtracting the largest integer smaller than it).
pub fn truncate_number(number: f64) -> f64 {
    number - number.floor()
}
