// unsupported: casting `bool` to an integer via `as u64` (or any `as <int>`)
// — extracts to a `Cast Bool u64` typeclass call, but the Hax Lean prelude
// has no `Cast Bool <integer>` instance, so `lake build` fails with
// `error: failed to synthesize instance of type class Cast Bool u64`.

// before

let mut s = (n >> shift) + (a > 0) as u64;

// after

let mut s = (n >> shift) + if a > 0 { 1u64 } else { 0u64 };
