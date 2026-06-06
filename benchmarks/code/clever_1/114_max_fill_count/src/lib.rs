/// HumanEval/115 / CLEVER 114 — `max_fill_count(grid, capacity)`.  Each
/// row of `grid` is a well; cells contain `0` or `1` (water units).
/// Buckets all have `capacity`.  Return the total number of bucket
/// trips needed to empty every well (ceil(ones_in_row / capacity)).
fn count_row_at(row: &[u64], j: usize, acc: u64) -> u64 {
    if j >= row.len() { acc }
    else if row[j] != 0 { count_row_at(row, j + 1, acc + 1) }
    else { count_row_at(row, j + 1, acc) }
}

fn rows_at(grid: &[&[u64]], capacity: u64, i: usize, acc: u64) -> u64 {
    if i >= grid.len() { acc }
    else {
        let w = count_row_at(grid[i], 0, 0);
        let trips = (w + capacity - 1) / capacity;
        rows_at(grid, capacity, i + 1, acc + trips)
    }
}

pub fn max_fill_count(grid: &[&[u64]], capacity: u64) -> u64 {
    if capacity == 0 { 0 } else { rows_at(grid, capacity, 0, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        let r0: &[u64] = &[0, 0, 1, 0];
        let r1: &[u64] = &[0, 1, 0, 0];
        let r2: &[u64] = &[1, 1, 1, 1];
        let g: &[&[u64]] = &[r0, r1, r2];
        // ones per row: 1, 1, 4. capacity 1 → trips 1+1+4 = 6.
        assert_eq!(max_fill_count(g, 1), 6);
        // capacity 2 → ceil(1/2)+ceil(1/2)+ceil(4/2) = 1+1+2 = 4.
        assert_eq!(max_fill_count(g, 2), 4);
    }

    // Reference spec: sum over rows of ceil(count_nonzero(row) / capacity).
    // Used by the `matches_spec` property below.
    fn spec(grid: &[&[u64]], capacity: u64) -> u64 {
        if capacity == 0 {
            return 0;
        }
        let mut total: u64 = 0;
        for row in grid.iter() {
            let ones: u64 = row.iter().filter(|&&x| x != 0).count() as u64;
            total += (ones + capacity - 1) / capacity;
        }
        total
    }

    proptest! {
        // Failure-avoidance clause: capacity == 0 must short-circuit to 0
        // for *any* grid (otherwise the inner `(w + capacity - 1) / capacity`
        // would divide by zero).
        #[test]
        fn capacity_zero_returns_zero(
            grid_data in prop::collection::vec(
                prop::collection::vec(any::<u64>(), 0..8),
                0..8,
            ),
        ) {
            let refs: Vec<&[u64]> = grid_data.iter().map(|r| r.as_slice()).collect();
            prop_assert_eq!(max_fill_count(&refs, 0), 0);
        }

        // Base case: an empty grid has no wells, hence no trips, for every
        // capacity (including 0).
        #[test]
        fn empty_grid_returns_zero(capacity in any::<u64>()) {
            let empty: &[&[u64]] = &[];
            prop_assert_eq!(max_fill_count(empty, capacity), 0);
        }

        // Main postcondition: when capacity > 0, the result equals
        // sum_{row in grid} ceil(count_nonzero(row) / capacity).
        // Bounds on the inputs are chosen so the reference spec itself
        // does not overflow u64.
        #[test]
        fn matches_spec(
            grid_data in prop::collection::vec(
                prop::collection::vec(any::<u64>(), 0..8),
                0..8,
            ),
            capacity in 1u64..1_000_000,
        ) {
            let refs: Vec<&[u64]> = grid_data.iter().map(|r| r.as_slice()).collect();
            prop_assert_eq!(max_fill_count(&refs, capacity), spec(&refs, capacity));
        }
    }
}
