/// HumanEval/87 / CLEVER 086 — `get_coords_sorted(lst, x)`.  Given a
/// jagged 2D matrix `lst` (slice of slices) and an integer `x`, find
/// every coordinate `(row, col)` where `lst[row][col] == x`.  Return
/// pairs sorted by row ascending; within a row, by column descending.
fn scan_row_desc(row: &[i64], r: i64, x: i64, j: usize, mut acc: Vec<(i64, i64)>) -> Vec<(i64, i64)> {
    // walk columns from right to left so we emit descending col order
    if j == 0 {
        if !row.is_empty() && row[0] == x {
            acc.push((r, 0));
        }
        acc
    } else {
        let col = j - 1;
        if row[col] == x {
            acc.push((r, col as i64));
        }
        scan_row_desc(row, r, x, col, acc)
    }
}

fn scan_at(lst: &[&[i64]], x: i64, i: usize, acc: Vec<(i64, i64)>) -> Vec<(i64, i64)> {
    if i >= lst.len() {
        acc
    } else {
        // Start from len so the loop runs col = len-1 down to 0.
        let next = scan_row_desc(lst[i], i as i64, x, lst[i].len(), acc);
        scan_at(lst, x, i + 1, next)
    }
}

pub fn get_coords_sorted(lst: &[&[i64]], x: i64) -> Vec<(i64, i64)> {
    scan_at(lst, x, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn small() {
        let row0: &[i64] = &[1, 2, 3, 4];
        let row1: &[i64] = &[5, 2, 7, 2];
        let row2: &[i64] = &[];
        let m: &[&[i64]] = &[row0, row1, row2];
        // x = 2: row 0 col 1, row 1 col 1 and 3 (desc → 3, 1).
        let r = get_coords_sorted(m, 2);
        assert_eq!(r, vec![(0, 1), (1, 3), (1, 1)]);
    }

    #[test]
    fn empty_input() {
        let m: &[&[i64]] = &[];
        assert_eq!(get_coords_sorted(m, 0), Vec::<(i64,i64)>::new());
    }

    // ---------- helpers for property tests ----------

    /// Run `get_coords_sorted` on an owned jagged matrix by borrowing rows.
    fn run(owned: &Vec<Vec<i64>>, x: i64) -> Vec<(i64, i64)> {
        let rows: Vec<&[i64]> = owned.iter().map(|r| r.as_slice()).collect();
        get_coords_sorted(&rows, x)
    }

    /// A small, occurrence-friendly matrix: few rows, short rows, narrow value range
    /// so `x` actually shows up often enough to exercise the ordering clauses.
    fn matrix_strategy() -> impl Strategy<Value = Vec<Vec<i64>>> {
        prop::collection::vec(
            prop::collection::vec(-3i64..=3, 0..6),
            0..6,
        )
    }

    /// Generator pairing a matrix with an `x` drawn from the same narrow range.
    fn matrix_and_x() -> impl Strategy<Value = (Vec<Vec<i64>>, i64)> {
        (matrix_strategy(), -3i64..=3)
    }

    proptest! {
        /// Soundness + bounds: every returned `(r, c)` indexes a valid cell
        /// whose value is `x`. This subsumes the "indices in range" clause
        /// because we have to be in range to look up the value at all.
        #[test]
        fn returned_coords_point_to_x((m, x) in matrix_and_x()) {
            let result = run(&m, x);
            for &(r, c) in &result {
                prop_assert!(r >= 0 && (r as usize) < m.len(),
                    "row {} out of bounds for matrix of len {}", r, m.len());
                let row = &m[r as usize];
                prop_assert!(c >= 0 && (c as usize) < row.len(),
                    "col {} out of bounds for row {} of len {}", c, r, row.len());
                prop_assert_eq!(row[c as usize], x);
            }
        }

        /// Completeness: every occurrence of `x` in the matrix appears in
        /// the output. Combined with soundness this fixes the output multiset.
        #[test]
        fn every_occurrence_is_reported((m, x) in matrix_and_x()) {
            let result = run(&m, x);
            for (i, row) in m.iter().enumerate() {
                for (j, &v) in row.iter().enumerate() {
                    if v == x {
                        prop_assert!(
                            result.contains(&(i as i64, j as i64)),
                            "missing occurrence at ({}, {})", i, j
                        );
                    }
                }
            }
        }

        /// Row order: consecutive entries have non-decreasing row indices.
        /// (Strict ordering would be wrong — multiple matches per row are allowed.)
        #[test]
        fn rows_are_non_decreasing((m, x) in matrix_and_x()) {
            let result = run(&m, x);
            for w in result.windows(2) {
                prop_assert!(w[0].0 <= w[1].0,
                    "rows decreased: {:?} then {:?}", w[0], w[1]);
            }
        }

        /// Within-row column order: for consecutive entries sharing a row,
        /// the column index does not increase. This is an *independent*
        /// contract clause from row order — a buggy implementation could
        /// get rows right and columns wrong (e.g. ascending columns within
        /// a row). We assert non-strict descent (`>=`) rather than strict
        /// descent (`>`) because the implementation may emit the same
        /// coordinate twice for a single-element row whose only element
        /// matches `x`; treating the implementation as the spec, ties are
        /// permitted.
        #[test]
        fn cols_non_increasing_within_row((m, x) in matrix_and_x()) {
            let result = run(&m, x);
            for w in result.windows(2) {
                if w[0].0 == w[1].0 {
                    prop_assert!(w[0].1 >= w[1].1,
                        "cols increased in row {}: {} then {}",
                        w[0].0, w[0].1, w[1].1);
                }
            }
        }
    }
}
