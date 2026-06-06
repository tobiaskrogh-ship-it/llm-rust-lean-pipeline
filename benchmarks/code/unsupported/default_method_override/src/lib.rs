//! Unsupported: default trait method with override at the impl site.
//! Hax's monomorphisation must pick the override when one exists, but
//! some default-method shapes still surface a printer-level error
//! depending on whether the default body uses `Self`. Worth a real
//! `cargo hax into lean` to see which category this falls into for the
//! current Hax version.

pub trait Tag {
    fn tag(&self) -> u64 { 0 }
}

pub struct A;
pub struct B;

impl Tag for A {}              // uses the default
impl Tag for B {
    fn tag(&self) -> u64 { 42 } // override
}

pub fn tag_both(a: &A, b: &B) -> u64 {
    a.tag() + b.tag()
}
