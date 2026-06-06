/// Area of a triangle given base length `a` and height `h`.
/// Integer arithmetic — fractional results are truncated to floor.
pub fn triangle_area(a: i64, h: i64) -> i64 {
    a * h / 2
}
