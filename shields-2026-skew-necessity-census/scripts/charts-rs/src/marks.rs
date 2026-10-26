//! Legal marks (Hypotheses I--IV), mark rotation and marked inners up to rotation.
//!
//! Port of `marks`, `attachment_case`, `hyp_IV`, `rotate_mark`, `vertical_empty_mark`,
//! `canon_marked` and `is_symmetric_marked` of the pinned `skew_compose.py`.  The one change is
//! how candidate copies are found.  The Python enumerates every connected subdiagram of E and keeps
//! those containing the southwesternmost (northeasternmost) cell.  Here only those subdiagrams are
//! generated, row by row from that cell, and only on the contents that Hypothesis II permits.  The
//! restriction loses nothing: a nonempty W_- contains the least-content cell of E, so it occupies
//! the contents [0, w-1] (relative to E), its translate W_+ occupies [N_E-w, N_E-1], and Hypothesis
//! II needs N_E - w >= w + 1.  Every subdiagram that Hypothesis I compares with W_- has the same
//! content range, so it is generated too.

use crate::diagram::*;
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Mark {
    pub b: Cells,
    pub t: Cells,
    /// b'a', b'b', b'c' or b'd'.
    pub case: u8,
    pub v: Cell,
    pub q: i16,
}

fn horizontal_empty(e: &[Cell]) -> Mark {
    let (ne, sw) = (ne_cell(e), sw_cell(e));
    Mark { b: vec![], t: vec![], case: b'a', v: (ne.0 - sw.0, ne.1 - sw.1 + 1), q: nd(e) }
}

/// The vertical edge reading of the empty W (displacement v_H - e), used only for the gauge.
pub fn vertical_empty(e: &[Cell]) -> Mark {
    let (ne, sw) = (ne_cell(e), sw_cell(e));
    Mark { b: vec![], t: vec![], case: b'b', v: (ne.0 - sw.0 - 1, ne.1 - sw.1), q: nd(e) }
}

fn attachment_case(b: &[Cell], t: &[Cell], o: &[Cell]) -> Option<u8> {
    let (oi, oj) = sw_cell(o);
    let lo_h = contains(b, (oi, oj - 1));
    let lo_v = contains(b, (oi + 1, oj));
    let (ni, nj) = ne_cell(o);
    let up_h = contains(t, (ni, nj + 1));
    let up_v = contains(t, (ni - 1, nj));
    if lo_h == lo_v || up_h == up_v {
        return None;
    }
    Some(match (lo_h, up_h) {
        (true, true) => b'a',
        (false, false) => b'b',
        (true, false) => b'c',
        (false, true) => b'd',
    })
}

/// Hypothesis IV on the eight-copy amalgamation; the interior copies of O-hat see exactly their
/// infinite neighborhood because 2q > N_E.
fn hyp_iv(e: &[Cell], b: &[Cell], t: &[Cell], v: Cell) -> bool {
    const K: i16 = 8;
    let o = minus(&minus(e, b), t);
    let mut ebar: FxHashSet<Cell> = FxHashSet::default();
    for s in 0..K {
        for &(i, j) in e {
            ebar.insert((i + s * v.0, j + s * v.1));
        }
    }
    let mut oh: Vec<FxHashSet<Cell>> = Vec::new();
    for s in 2..K - 2 {
        let ot: FxHashSet<Cell> = o.iter().map(|&(i, j)| (i + s * v.0, j + s * v.1)).collect();
        oh.push(ot.iter().copied().filter(|&(i, j)| ot.contains(&(i + 1, j + 1))).collect());
    }
    let mut wh: Vec<FxHashSet<Cell>> = Vec::new();
    for s in 1..K {
        let wt: FxHashSet<Cell> = b.iter().map(|&(i, j)| (i + s * v.0, j + s * v.1)).collect();
        let mut w: FxHashSet<Cell> = FxHashSet::default();
        for &(i, j) in &wt {
            if ebar.contains(&(i - 1, j - 1)) {
                w.insert((i - 1, j - 1));
            }
            if ebar.contains(&(i + 1, j + 1)) {
                w.insert((i, j));
            }
        }
        wh.push(w);
    }
    for o in &oh {
        for w in &wh {
            for &(i, j) in o {
                if w.contains(&(i, j))
                    || w.contains(&(i + 1, j))
                    || w.contains(&(i - 1, j))
                    || w.contains(&(i, j + 1))
                    || w.contains(&(i, j - 1))
                {
                    return false;
                }
            }
        }
    }
    true
}

/// Connected subdiagrams of E containing its southwesternmost cell, with every relative content
/// at most `cmax`.  Built from the bottom row upward: an upper interval (pl, pr) above a lower one
/// (l, r) satisfies l <= pl <= r <= pr.
fn bottoms(ri: &[(i16, i16, i16)], c0: i16, cmax: i16, out: &mut Vec<Cells>) {
    let last = ri.len() - 1;
    let (row, lo, hi) = ri[last];
    let mut acc: Cells = Vec::new();
    fn up(
        ri: &[(i16, i16, i16)],
        k: usize,
        l: i16,
        r: i16,
        c0: i16,
        cmax: i16,
        acc: &mut Cells,
        out: &mut Vec<Cells>,
    ) {
        if k == 0 {
            return;
        }
        let (row, lo, hi) = ri[k - 1];
        for pl in l.max(lo)..=r.min(hi) {
            for pr in r.max(pl)..=hi {
                if pr - row - c0 > cmax {
                    break;
                }
                let n = acc.len();
                acc.extend((pl..=pr).map(|j| (row, j)));
                out.push(sorted(acc.clone()));
                up(ri, k - 1, pl, pr, c0, cmax, acc, out);
                acc.truncate(n);
            }
        }
    }
    for r in lo..=hi {
        if r - row - c0 > cmax {
            break;
        }
        acc.clear();
        acc.extend((lo..=r).map(|j| (row, j)));
        out.push(sorted(acc.clone()));
        up(ri, last, lo, r, c0, cmax, &mut acc, out);
    }
}

/// Connected subdiagrams of E containing its northeasternmost cell, with every relative content at
/// least `cmin`.  Built from the top row downward: a lower interval (l, r) below (pl, pr) satisfies
/// l <= pl <= r <= pr.
fn tops(ri: &[(i16, i16, i16)], c0: i16, cmin: i16, out: &mut Vec<Cells>) {
    let (row, lo, hi) = ri[0];
    fn down(
        ri: &[(i16, i16, i16)],
        k: usize,
        pl: i16,
        pr: i16,
        c0: i16,
        cmin: i16,
        acc: &mut Cells,
        out: &mut Vec<Cells>,
    ) {
        if k + 1 >= ri.len() {
            return;
        }
        let (row, lo, hi) = ri[k + 1];
        for r in (pl.max(lo)..=pr.min(hi)).rev() {
            for l in (lo..=pl.min(r)).rev() {
                if l - row - c0 < cmin {
                    break;
                }
                let n = acc.len();
                acc.extend((l..=r).map(|j| (row, j)));
                out.push(sorted(acc.clone()));
                down(ri, k + 1, l, r, c0, cmin, acc, out);
                acc.truncate(n);
            }
        }
    }
    let mut acc: Cells = Vec::new();
    for l in (lo..=hi).rev() {
        if l - row - c0 < cmin {
            break;
        }
        acc.clear();
        acc.extend((l..=hi).map(|j| (row, j)));
        out.push(sorted(acc.clone()));
        down(ri, 0, l, hi, c0, cmin, &mut acc, out);
    }
}

/// Every legal mark of the normalized connected diagram E: the empty mark (horizontal reading)
/// first, then every nonempty W satisfying Hypotheses I--IV.
pub fn marks(e: &[Cell]) -> Vec<Mark> {
    let ne_ = nd(e);
    let mut out = vec![horizontal_empty(e)];
    let wcap = (ne_ - 1) / 2;
    if e.len() >= 3 && wcap >= 1 {
        let ri = row_intervals(e).unwrap();
        let c0 = min_content(e);
        let mut bs = Vec::new();
        bottoms(&ri, c0, wcap - 1, &mut bs);
        let mut ts = Vec::new();
        tops(&ri, c0, ne_ - wcap, &mut ts);
        let top_of: FxHashMap<Cells, Cells> =
            ts.into_iter().map(|t| (normalize(t.clone()), t)).collect();
        let mut pairs = Vec::new();
        let mut lying: FxHashMap<i16, Vec<Cells>> = FxHashMap::default();
        for s in bs {
            if let Some(t) = top_of.get(&normalize(s.clone())) {
                let width = nd(&s);
                if disjoint(&s, t) {
                    pairs.push((s.clone(), t.clone()));
                }
                lying.entry(width).or_default().push(s);
            }
        }
        for (b, t) in pairs {
            let width = nd(&b);
            // Hypothesis I: no strictly larger W' on the same contents lies in the top and bottom.
            if lying[&width].iter().any(|b2| b2.len() > b.len() && is_subset(&b, b2)) {
                continue;
            }
            // Hypothesis II holds by the content restriction; assert it anyway.
            let max_b = b.iter().map(|&c| content(c)).max().unwrap();
            let min_t = t.iter().map(|&c| content(c)).min().unwrap();
            assert!(min_t > max_b + 1);
            let o = minus(&minus(e, &b), &t);
            if !is_connected_skew(&o) {
                continue;
            }
            // Hypothesis III.
            if !(is_connected_skew(&minus(e, &t)) && is_connected_skew(&minus(e, &b))) {
                continue;
            }
            let Some(case) = attachment_case(&b, &t, &o) else { continue };
            let v = (t[0].0 - b[0].0, t[0].1 - b[0].1);
            assert_eq!(shift(&b, v), t);
            if !hyp_iv(e, &b, &t, v) {
                continue;
            }
            out.push(Mark { b, t, case, v, q: v.1 - v.0 });
        }
    }
    for m in &out {
        assert!(2 * m.q > ne_ && m.q <= ne_, "every legal mark has N_E < 2q");
    }
    out
}

/// (E*, mark*): rotation exchanges the copies and the cases (c), (d).
pub fn rotate_mark(e: &[Cell], m: &Mark) -> (Cells, Mark) {
    let di = e.iter().map(|c| c.0).max().unwrap();
    let dj = e.iter().map(|c| c.1).max().unwrap();
    let er = sorted(e.iter().map(|&(i, j)| (di - i, dj - j)).collect());
    if m.b.is_empty() {
        let r = if m.case == b'a' { horizontal_empty(&er) } else { vertical_empty(&er) };
        return (er, r);
    }
    let br = sorted(m.t.iter().map(|&(i, j)| (di - i, dj - j)).collect());
    let tr = sorted(m.b.iter().map(|&(i, j)| (di - i, dj - j)).collect());
    let case = match m.case {
        b'c' => b'd',
        b'd' => b'c',
        c => c,
    };
    let v = (tr[0].0 - br[0].0, tr[0].1 - br[0].1);
    (er, Mark { b: br, t: tr, case, v, q: v.1 - v.0 })
}

/// The marked inner as a comparable tuple (E, W_-, W_+, case).
pub type MarkedTuple = (Cells, Cells, Cells, u8);

pub fn canon_marked(e: &[Cell], m: &Mark) -> MarkedTuple {
    let a = (e.to_vec(), m.b.clone(), m.t.clone(), m.case);
    let (er, mr) = rotate_mark(e, m);
    let b = (er, mr.b, mr.t, mr.case);
    a.min(b)
}

pub fn is_symmetric_marked(e: &[Cell], m: &Mark) -> bool {
    let (er, mr) = rotate_mark(e, m);
    e == er.as_slice() && m.b == mr.b && m.t == mr.t && m.case == mr.case
}
