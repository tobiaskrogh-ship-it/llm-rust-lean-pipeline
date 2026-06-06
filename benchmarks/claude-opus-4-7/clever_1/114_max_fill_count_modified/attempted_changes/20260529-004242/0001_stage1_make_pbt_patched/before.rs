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
}
