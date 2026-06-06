/// HumanEval/157 / CLEVER 155 — `right_angle_triangle(a, b, c)`.
/// Return true iff one of the three squared-side equations holds:
/// `a² + b² == c²`, `a² + c² == b²`, or `b² + c² == a²`.
pub fn right_angle_triangle(a: u64, b: u64, c: u64) -> bool {
    let a2 = a * a;
    let b2 = b * b;
    let c2 = c * c;
    a2 + b2 == c2 || a2 + c2 == b2 || b2 + c2 == a2
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known() {
        assert!(right_angle_triangle(3, 4, 5));
        assert!(right_angle_triangle(5, 12, 13));
        assert!(right_angle_triangle(13, 5, 12));     // any permutation
        assert!(!right_angle_triangle(1, 2, 3));
        assert!(!right_angle_triangle(2, 2, 2));
    }
}
