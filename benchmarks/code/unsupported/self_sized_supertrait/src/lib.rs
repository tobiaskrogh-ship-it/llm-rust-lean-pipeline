//! Unsupported: subtraiting with `Self: Sized` constraint where the
//! subtrait's default body calls a supertrait method. The combination of
//! object-safety bound (`Self: Sized`) + supertrait method call exercises
//! parts of Hax's trait elaboration that the Lean printer struggles with.

pub trait A {
    fn a(&self) -> u64;
}

pub trait B: A
where
    Self: Sized,
{
    fn b(&self) -> u64 {
        self.a() + 1
    }
}

pub struct Foo;

impl A for Foo {
    fn a(&self) -> u64 { 10 }
}

impl B for Foo {}

pub fn run(f: &Foo) -> u64 {
    f.b()
}
