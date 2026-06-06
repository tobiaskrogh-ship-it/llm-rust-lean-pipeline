//! Unsupported: const generics interacting with trait bounds. The
//! `[u64; N]: Default` bound depends on the const parameter `N`, and
//! Hax's printer support for const-arithmetic-in-bounds is incomplete
//! at the time of writing.

pub fn first_or_zero<const N: usize>(arr: [u64; N]) -> u64
where
    [u64; N]: Default,
{
    if N == 0 {
        0
    } else {
        arr[0]
    }
}
