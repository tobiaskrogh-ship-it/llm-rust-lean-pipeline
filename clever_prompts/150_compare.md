# compare

## Signature

```rust
pub fn compare(scores: &[i64], guesses: &[i64]) -> Vec<i64>
```

## Docstring

I think we all remember that feeling when the result of some long-awaited
event is finally known. The feelings and thoughts you have at that moment are
definitely worth noting down and comparing.
Your task is to determine if a person correctly guessed the results of a number of matches.
You are given two arrays of scores and guesses of equal length, where each index shows a match.
Return an array of the same length denoting how far off each guess was. If they have guessed correctly,
the value is 0, and if not, the value is the absolute difference between the guess and the score.

Note: to reviewer, the reason for not using |.| to get the absolute value is to avoid leaking the implementation.

