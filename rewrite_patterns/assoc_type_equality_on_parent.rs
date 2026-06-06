// unsupported: equality constraints on associated types of a parent trait
// (here implicit via `T: Integer`, whose parent traits carry their own
// associated types) — Hax frontend accepts the bound but the Lean printer
// emits `error: [HAX0001] Unsupported equality constraints on associated
// types of parent trait`. Issue: hacspec/hax#1923.

// before

fn fixpoint<T, F>(mut x: T, f: F) -> T
where
    T: Integer + PartialOrd + Clone,
    F: Fn(&T) -> T,
{
    let mut xn = f(&x);
    while x > xn {
        x = xn;
        xn = f(&x);
    }
    x
}

// after

fn fixpoint_u64(mut x: u64, f: fn(u64) -> u64) -> u64 {
    let mut xn = f(x);
    while x > xn {
        x = xn;
        xn = f(x);
    }
    x
}
