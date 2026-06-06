/// Given a non-negative integer interpreted as a fixed-point number with
/// 3 fractional digits (so `1000` represents the float `1.0`), return the
/// fractional part — i.e. the value strictly less than `1000`.
///
/// Note: CLEVER's reference signature is `(number: float) -> float`,
/// returning `number - floor(number)`. Translated to a `u64` fixed-point
/// formulation because the Hax Lean prelude has gaps in `f64` support
/// (missing `Impl.abs`, `PartialOrd`, `Neg`, and a broken `Sub.sub` for
/// non-integer types). The body has no iteration, so no recursive form
/// applies — the function is a single arithmetic expression.
pub fn truncate_number(number: u64) -> u64 {
    number % 1000
}
