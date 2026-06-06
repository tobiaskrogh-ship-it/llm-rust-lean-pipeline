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
}
