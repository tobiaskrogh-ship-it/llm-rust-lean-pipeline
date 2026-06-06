// unsupported: `return <expr>;` inside a `while` loop. Hax extracts the
// loop into `rust_primitives.hax.while_loop_return` (a variant that carries
// an early-exit value), but only `rust_primitives.hax.while_loop` is
// defined in the Hax Lean prelude. `lake build` fails with:
//   Unknown identifier `rust_primitives.hax.while_loop_return`
// Workaround: eliminate the early `return` by introducing a boolean
// `found`/`done` flag and folding it into the loop condition. Hax then
// extracts the loop with the supported `while_loop` combinator.

// before

pub fn has_close_elements(numbers: &[f64], threshold: f64) -> bool {
    let n = numbers.len();
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            if i != j {
                let diff = (numbers[i] - numbers[j]).abs();
                if diff < threshold {
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    false
}

// after

pub fn has_close_elements(numbers: &[f64], threshold: f64) -> bool {
    let n = numbers.len();
    let mut found = false;
    let mut i = 0;
    while i < n && !found {
        let mut j = 0;
        while j < n && !found {
            if i != j {
                let diff = (numbers[i] - numbers[j]).abs();
                if diff < threshold {
                    found = true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    found
}
