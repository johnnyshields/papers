//! Cell sets, profiles and connected skew diagrams.
//!
//! Cells are (i, j) with i increasing to the south and j to the east; the content of (i, j) is
//! j - i.  A cell set is a sorted, duplicate-free vector.  A diagram is normalized when its least
//! row and least column are 0.  These conventions are those of the paper and of `skew_core.py`.

use rustc_hash::FxHashSet;

pub type Cell = (i16, i16);
pub type Cells = Vec<Cell>;

/// A profile (row lengths top to bottom; gaps = shared columns minus one).
pub type Profile = (Vec<u8>, Vec<u8>);

pub fn sorted(mut v: Cells) -> Cells {
    v.sort_unstable();
    v.dedup();
    v
}

pub fn normalize(v: Cells) -> Cells {
    let mut v = sorted(v);
    if v.is_empty() {
        return v;
    }
    let i0 = v[0].0;
    let j0 = v.iter().map(|c| c.1).min().unwrap();
    for c in v.iter_mut() {
        c.0 -= i0;
        c.1 -= j0;
    }
    v
}

/// Translation preserves the lexicographic order.
pub fn shift(s: &[Cell], v: Cell) -> Cells {
    s.iter().map(|&(i, j)| (i + v.0, j + v.1)).collect()
}

pub fn contains(s: &[Cell], c: Cell) -> bool {
    s.binary_search(&c).is_ok()
}

pub fn minus(a: &[Cell], b: &[Cell]) -> Cells {
    a.iter().copied().filter(|c| !contains(b, *c)).collect()
}

pub fn is_subset(a: &[Cell], b: &[Cell]) -> bool {
    a.iter().all(|c| contains(b, *c))
}

pub fn disjoint(a: &[Cell], b: &[Cell]) -> bool {
    a.iter().all(|c| !contains(b, *c))
}

pub fn set(s: &[Cell]) -> FxHashSet<Cell> {
    s.iter().copied().collect()
}

/// Row intervals (row, lo, hi) in increasing row order, or None when a row is not an interval.
pub fn row_intervals(s: &[Cell]) -> Option<Vec<(i16, i16, i16)>> {
    let mut out: Vec<(i16, i16, i16)> = Vec::new();
    let mut k = 0;
    while k < s.len() {
        let i = s[k].0;
        let lo = s[k].1;
        let mut hi = lo;
        k += 1;
        while k < s.len() && s[k].0 == i {
            if s[k].1 != hi + 1 {
                return None;
            }
            hi = s[k].1;
            k += 1;
        }
        out.push((i, lo, hi));
    }
    Some(out)
}

/// Nonempty, rows are intervals in consecutive rows, both ends weakly decreasing downward, and
/// consecutive rows share a column.
pub fn is_connected_skew(s: &[Cell]) -> bool {
    if s.is_empty() {
        return false;
    }
    let Some(ri) = row_intervals(s) else { return false };
    for w in ri.windows(2) {
        let (ia, la, ha) = w[0];
        let (ib, lb, hb) = w[1];
        if ib != ia + 1 || lb > la || hb > ha || hb < la {
            return false;
        }
    }
    true
}

/// Southwesternmost cell: greatest row, least column in it.
pub fn sw_cell(s: &[Cell]) -> Cell {
    let i = s[s.len() - 1].0;
    *s.iter().find(|c| c.0 == i).unwrap()
}

/// Northeasternmost cell: least row, greatest column in it.
pub fn ne_cell(s: &[Cell]) -> Cell {
    let i = s[0].0;
    *s.iter().rev().find(|c| c.0 == i).unwrap()
}

pub fn rotate(s: &[Cell]) -> Cells {
    normalize(s.iter().map(|&(i, j)| (-i, -j)).collect())
}

pub fn transpose(s: &[Cell]) -> Cells {
    normalize(s.iter().map(|&(i, j)| (j, i)).collect())
}

pub fn antitranspose(s: &[Cell]) -> Cells {
    normalize(s.iter().map(|&(i, j)| (-j, -i)).collect())
}

pub fn content(c: Cell) -> i16 {
    c.1 - c.0
}

pub fn min_content(s: &[Cell]) -> i16 {
    s.iter().map(|&c| content(c)).min().unwrap()
}

/// Number of occupied diagonals.
pub fn nd(s: &[Cell]) -> i16 {
    if s.is_empty() {
        return 0;
    }
    let lo = min_content(s);
    let hi = s.iter().map(|&c| content(c)).max().unwrap();
    hi - lo + 1
}

/// Number of cells on each content, from the least content upward.
pub fn height_seq(s: &[Cell]) -> Vec<i16> {
    let lo = min_content(s);
    let mut h = vec![0i16; nd(s) as usize];
    for &c in s {
        h[(content(c) - lo) as usize] += 1;
    }
    h
}

/// Cells of a profile, normalized (`skew_core.cells`).
pub fn cells_of(rows: &[u8], gaps: &[u8]) -> Cells {
    let n = rows.len();
    let mut x = vec![0i16; n];
    let mut y = vec![0i16; n];
    x[n - 1] = rows[n - 1] as i16;
    for i in (0..n - 1).rev() {
        y[i] = x[i + 1] - gaps[i] as i16;
        x[i] = y[i] + rows[i] as i16;
    }
    let mut out = Vec::new();
    for i in 0..n {
        for c in y[i]..x[i] {
            out.push((i as i16, c + i as i16));
        }
    }
    normalize(out)
}

/// Profile of a connected skew diagram (`skew_core.profile_of_cells`).
pub fn profile_of(s: &[Cell]) -> Profile {
    let ri = row_intervals(s).expect("row is not an interval");
    let rows: Vec<u8> = ri.iter().map(|r| (r.2 - r.1 + 1) as u8).collect();
    let gaps: Vec<u8> = ri.windows(2).map(|w| (w[1].2 - w[0].1) as u8).collect();
    for (k, w) in ri.windows(2).enumerate() {
        assert_eq!(w[1].0, w[0].0 + 1, "empty row");
        assert!(gaps[k] < rows[k].min(rows[k + 1]), "illegal profile");
    }
    (rows, gaps)
}

/// A compact hashable key for a connected skew diagram: rows then gaps.
pub fn key_of(p: &Profile) -> Box<[u8]> {
    let mut v = Vec::with_capacity(1 + p.0.len() + p.1.len());
    v.push(p.0.len() as u8);
    v.extend_from_slice(&p.0);
    v.extend_from_slice(&p.1);
    v.into_boxed_slice()
}

pub fn profile_from_key(k: &[u8]) -> Profile {
    let n = k[0] as usize;
    (k[1..1 + n].to_vec(), k[1 + n..].to_vec())
}

pub fn rot_profile(p: &Profile) -> Profile {
    (p.0.iter().rev().copied().collect(), p.1.iter().rev().copied().collect())
}

/// Every composition of n into parts.
pub fn compositions(n: usize) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut cur = Vec::new();
    fn rec(left: usize, cur: &mut Vec<u8>, out: &mut Vec<Vec<u8>>) {
        if left == 0 {
            out.push(cur.clone());
            return;
        }
        for p in 1..=left {
            cur.push(p as u8);
            rec(left - p, cur, out);
            cur.pop();
        }
    }
    rec(n, &mut cur, &mut out);
    out
}

/// Every gap sequence legal for the row sequence.
pub fn for_each_gaps(rows: &[u8], mut f: impl FnMut(&[u8])) {
    let n = rows.len();
    let mut g = vec![0u8; n.saturating_sub(1)];
    if n <= 1 {
        f(&g);
        return;
    }
    loop {
        f(&g);
        let mut k = n - 1;
        loop {
            if k == 0 {
                return;
            }
            k -= 1;
            g[k] += 1;
            if g[k] < rows[k].min(rows[k + 1]) {
                break;
            }
            g[k] = 0;
        }
    }
}

/// Number of connected diagrams of each area 0..=n (the recurrence of the paper).
pub fn area_counts(n: usize) -> Vec<u64> {
    let mut f = vec![vec![0u64; n + 1]; n + 1];
    for r in 1..=n {
        f[r][r] = 1;
    }
    for a in 1..=n {
        for last in 1..=a {
            let c = f[a][last];
            if c == 0 {
                continue;
            }
            for r in 1..=n - a {
                f[a + r][r] += c * (last.min(r) as u64);
            }
        }
    }
    f.iter().map(|row| row.iter().sum()).collect()
}
