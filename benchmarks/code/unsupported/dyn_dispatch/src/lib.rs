//! Unsupported: trait objects (`dyn Trait`). Dynamic dispatch via vtables
//! has no model in Lean's static type system; Hax targets first-order
//! monomorphised code.

pub trait Greet {
    fn greet(&self) -> u64;
}

pub struct A;
pub struct B;

impl Greet for A {
    fn greet(&self) -> u64 { 1 }
}

impl Greet for B {
    fn greet(&self) -> u64 { 2 }
}

pub fn run(g: &dyn Greet) -> u64 {
    g.greet()
}
