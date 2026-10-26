//! Marked composition (cell form of McNamara--van Willigenburg Def. 3.11) and the two complete
//! chart searches.  Port of `offsets`, `compose`, `outer_from_rows`, `shapes_with_heights`,
//! `outer_heights`, `finder_subdiagram` and `finder_band` of the pinned `skew_compose.py`.

use crate::diagram::*;
use crate::marks::{Mark, marks};
use rustc_hash::{FxHashMap, FxHashSet};

/// A chart (D, marked inner); the period is `m.q`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Chart {
    pub d: Cells,
    pub e: Cells,
    pub m: Mark,
}

/// D o_W E as a normalized cell set, or None once it has more than `limit` cells.
pub fn compose_limited(d: &[Cell], e: &[Cell], m: &Mark, limit: usize) -> Option<Cells> {
    let cmin = min_content(d);
    let span = nd(d) as usize;
    let mut lo = vec![i16::MAX; span];
    let mut hi = vec![i16::MIN; span];
    for &(i, j) in d {
        let t = (j - i - cmin) as usize;
        lo[t] = lo[t].min(i);
        hi[t] = hi[t].max(i);
    }
    let v = m.v;
    let offset = |i: i16, j: i16| -> Cell {
        let t = j - i;
        let ti = (t - cmin) as usize;
        let k = match m.case {
            b'a' => i,
            b'b' => -i,
            b'c' => i - lo[ti],
            _ => -(hi[ti] - i),
        };
        (t * v.0 + k, t * v.1 + k)
    };
    let mut out: Cells = Vec::with_capacity(d.len() * e.len());
    for &(i, j) in d {
        let o = offset(i, j);
        out.extend(e.iter().map(|&(a, b)| (a + o.0, b + o.1)));
    }
    if m.case == b'c' || m.case == b'd' {
        for &(i, j) in d {
            if !contains(d, (i - 1, j)) {
                continue;
            }
            let ti = (j - i - cmin) as usize;
            let o = offset(i, j);
            if m.case == b'c' && i - lo[ti] == i - 1 - lo[ti + 1] {
                out.extend(m.t.iter().map(|&(a, b)| (a + o.0 + 1, b + o.1 + 1)));
            }
            if m.case == b'd' && hi[ti] - i == hi[ti + 1] - (i - 1) {
                out.extend(m.t.iter().map(|&(a, b)| (a + o.0 - 1, b + o.1 - 1)));
            }
        }
    }
    let out = normalize(out);
    if out.len() > limit { None } else { Some(out) }
}

pub fn compose(d: &[Cell], e: &[Cell], m: &Mark) -> Cells {
    compose_limited(d, e, m, usize::MAX).unwrap()
}

/// Cases (a), (b): the outer from its diagonal heights and the lowest-row shifts.
fn outer_from_rows(hs: &[i16], da: &[i16], v: Cell, case: u8) -> Option<Cells> {
    let mut out = Vec::new();
    for (t, &h) in hs.iter().enumerate() {
        let t = t as i16;
        let lo = if case == b'a' {
            da[t as usize] - t * v.0
        } else {
            -(da[t as usize] - t * v.0) - h + 1
        };
        out.extend((lo..lo + h).map(|i| (i, i + t)));
    }
    let s = normalize(out);
    if is_connected_skew(&s) { Some(s) } else { None }
}

/// Every connected skew diagram with the given consecutive diagonal heights.
pub fn shapes_with_heights(hs: &[i16]) -> Vec<Cells> {
    let r = hs.len();
    let mut out: FxHashSet<Cells> = FxHashSet::default();
    if r >= 1 && hs[0] == 1 && hs[r - 1] == 1 && hs.iter().all(|&h| h >= 1) {
        fn rec(hs: &[i16], t: usize, a: i16, acc: &mut Cells, out: &mut FxHashSet<Cells>) {
            if t == hs.len() {
                let s = normalize(acc.clone());
                if is_connected_skew(&s) {
                    out.insert(s);
                }
                return;
            }
            let b_prev = a + hs[t - 1] - 1;
            for na in [a - 1, a] {
                let nb = na + hs[t] - 1;
                if nb != b_prev && nb != b_prev - 1 {
                    continue;
                }
                let n = acc.len();
                acc.extend((na..=nb).map(|i| (i, i + t as i16)));
                rec(hs, t + 1, na, acc, out);
                acc.truncate(n);
            }
        }
        let mut acc = vec![(0i16, 0i16)];
        rec(hs, 1, 0, &mut acc, &mut out);
    }
    let mut v: Vec<Cells> = out.into_iter().collect();
    v.sort();
    v
}

/// Private-diagonal reading of the outer heights, or None when the private diagonals disagree.
fn outer_heights(hf: &[i16], he: &[i16], q: usize, w: usize, ndd: usize) -> Option<Vec<i16>> {
    let mut hs: Option<Vec<i16>> = None;
    for wp in w..q {
        let h: Vec<i16> = (0..ndd).map(|t| hf[t * q + wp] - he[wp] + 1).collect();
        match &hs {
            None => hs = Some(h),
            Some(prev) if *prev != h => return None,
            _ => {}
        }
    }
    let hs = hs?;
    if hs[0] != 1 || hs[hs.len() - 1] != 1 || hs.iter().any(|&h| h < 1) {
        return None;
    }
    if hs.windows(2).any(|p| (p[0] - p[1]).abs() > 1) {
        return None;
    }
    Some(hs)
}

/// Every connected skew subdiagram of F, in place, passed to `f`.
pub fn for_each_subdiagram(fd: &[Cell], mut f: impl FnMut(&Cells)) {
    let ri = row_intervals(fd).unwrap();
    fn rec(
        ri: &[(i16, i16, i16)],
        idx: usize,
        prev: Option<(i16, i16)>,
        acc: &mut Cells,
        f: &mut dyn FnMut(&Cells),
    ) {
        if idx == ri.len() {
            return;
        }
        let (row, lo, hi) = ri[idx];
        for l in lo..=hi {
            for r in l..=hi {
                if let Some((pl, pr)) = prev {
                    if l > pl || r > pr || r < pl {
                        continue;
                    }
                }
                let n = acc.len();
                acc.extend((l..=r).map(|j| (row, j)));
                f(acc);
                rec(ri, idx + 1, Some((l, r)), acc, f);
                acc.truncate(n);
            }
        }
    }
    let mut acc = Vec::new();
    for a in 0..ri.len() {
        rec(&ri, a, None, &mut acc, &mut f);
    }
}

/// Search S: every connected subdiagram of F as inner, every legal mark, outer heights from the
/// private diagonals, every outer with those heights.
pub fn finder_subdiagram(f: &[Cell]) -> Vec<Chart> {
    let hf = height_seq(f);
    let nf = hf.len();
    let mut found: FxHashSet<Chart> = FxHashSet::default();
    let mut seen: FxHashSet<Cells> = FxHashSet::default();
    let mut shapes: FxHashMap<Vec<i16>, Vec<Cells>> = FxHashMap::default();
    for_each_subdiagram(f, |s| {
        if s.len() < 2 {
            return;
        }
        let e = normalize(s.clone());
        if !seen.insert(e.clone()) {
            return;
        }
        let he = height_seq(&e);
        let ne_ = he.len();
        let mut plan: FxHashMap<i16, Vec<i16>> = FxHashMap::default();
        for q in ne_ / 2 + 1..=ne_ {
            let (m, rem) = ((nf - ne_) / q, (nf - ne_) % q);
            if rem != 0 || m < 1 {
                continue;
            }
            if let Some(hs) = outer_heights(&hf, &he, q, ne_ - q, m + 1) {
                plan.insert(q as i16, hs);
            }
        }
        if plan.is_empty() {
            return;
        }
        for mk in marks(&e) {
            let Some(hs) = plan.get(&mk.q) else { continue };
            let cand = shapes.entry(hs.clone()).or_insert_with(|| shapes_with_heights(hs));
            for d in cand.iter() {
                if d.len() >= 2 && compose(d, &e, &mk) == f {
                    found.insert(Chart { d: d.clone(), e: e.clone(), m: mk.clone() });
                }
            }
        }
    });
    let mut v: Vec<Chart> = found.into_iter().collect();
    v.sort();
    v
}

/// Search B: for each period q, the inner is read off the first and last q diagonals of F.
pub fn finder_band(f: &[Cell]) -> Vec<Chart> {
    let hf = height_seq(f);
    let nf = hf.len();
    let c0 = min_content(f);
    let mut af = vec![i16::MAX; nf];
    for &(i, j) in f {
        let c = (j - i - c0) as usize;
        af[c] = af[c].min(i);
    }
    let fset = set(f);
    let mut found: FxHashSet<Chart> = FxHashSet::default();
    for q in 2..=nf / 2 {
        let w = nf % q;
        let ndd = nf / q;
        let mut ok = true;
        'outer: for t in 1..ndd {
            let dh = hf[t * q + w] - hf[w];
            let da = af[t * q + w] - af[w];
            for wp in w + 1..q {
                if hf[t * q + wp] - hf[wp] != dh || af[t * q + wp] - af[wp] != da {
                    ok = false;
                    break 'outer;
                }
            }
        }
        if !ok {
            continue;
        }
        let sh = ((ndd - 1) * q) as i16;
        let a = af[w + sh as usize] - af[w];
        let rel = |c: Cell| c.1 - c.0 - c0;
        let aa: Cells = f.iter().copied().filter(|&c| rel(c) < q as i16).collect();
        let bt: Cells = sorted(
            f.iter()
                .copied()
                .filter(|&c| rel(c) >= (nf - q) as i16)
                .map(|(i, j)| (i - a, j - a - sh))
                .collect(),
        );
        let x: Cells = aa.iter().copied().filter(|&c| rel(c) >= w as i16).collect();
        let y: Cells = bt.iter().copied().filter(|&c| rel(c) <= q as i16 - 1).collect();
        if x != y {
            continue;
        }
        let mut e0 = aa.clone();
        e0.extend(bt.iter().copied());
        let e0 = sorted(e0);
        if !is_connected_skew(&e0) {
            continue;
        }
        let s0 = (e0[0].0, e0.iter().map(|c| c.1).min().unwrap());
        let e = normalize(e0);
        let he = height_seq(&e);
        let Some(hs) = outer_heights(&hf, &he, q, w, ndd) else { continue };
        let da: Vec<i16> = (0..ndd).map(|t| af[t * q + w] - af[w]).collect();
        for mk in marks(&e) {
            if mk.q != q as i16 {
                continue;
            }
            let cand: Vec<Cells> = if mk.case == b'a' || mk.case == b'b' {
                outer_from_rows(&hs, &da, mk.v, mk.case).into_iter().collect()
            } else {
                let sg: i16 = if mk.case == b'c' { 1 } else { -1 };
                let v = mk.v;
                let all_in = (0..ndd).all(|t| {
                    (0..hs[t]).all(|k| {
                        e.iter().all(|&(i, j)| {
                            fset.contains(&(
                                i + s0.0 + t as i16 * v.0 + sg * k,
                                j + s0.1 + t as i16 * v.1 + sg * k,
                            ))
                        })
                    })
                });
                if !all_in {
                    continue;
                }
                shapes_with_heights(&hs)
            };
            for d in cand {
                if d.len() >= 2 && compose(&d, &e, &mk) == f {
                    found.insert(Chart { d, e: e.clone(), m: mk.clone() });
                }
            }
        }
    }
    let mut v: Vec<Chart> = found.into_iter().collect();
    v.sort();
    v
}

pub fn private_heights_hold(f: &[Cell], d: &[Cell], e: &[Cell], q: usize) -> bool {
    let (hf, he, hd) = (height_seq(f), height_seq(e), height_seq(d));
    if hf.len() != (hd.len() - 1) * q + he.len() {
        return false;
    }
    (0..hd.len()).all(|t| (he.len() - q..q).all(|wp| hf[t * q + wp] == hd[t] + he[wp] - 1))
}

pub fn size_bound_holds(f: &[Cell], d: &[Cell], e: &[Cell], q: usize) -> bool {
    f.len() as i64 >= (q * d.len()) as i64 + nd(e) as i64 - q as i64
}

/// Validate a chart as `roots_keys.chart_ok` does.
pub fn chart_ok(f: &[Cell], c: &Chart) -> Result<(), &'static str> {
    if c.d.len() < 2 || c.e.len() < 2 || !is_connected_skew(&c.d) || !is_connected_skew(&c.e) {
        return Err("not a proper chart");
    }
    let legal: Vec<Mark> = marks(&c.e)
        .into_iter()
        .filter(|m| m.b == c.m.b && m.t == c.m.t && m.case == c.m.case && m.q == c.m.q)
        .collect();
    if legal.len() != 1 || legal[0] != c.m {
        return Err("illegal mark");
    }
    if compose(&c.d, &c.e, &c.m) != f {
        return Err("recomposition failed");
    }
    let q = c.m.q as usize;
    if !private_heights_hold(f, &c.d, &c.e, q) || !size_bound_holds(f, &c.d, &c.e, q) {
        return Err("private heights or size bound failed");
    }
    let nf = nd(f) as usize;
    if (nd(&c.m.b) as usize, nd(&c.e) as usize) != (nf % q, q + nf % q) {
        return Err("chart cost failed");
    }
    Ok(())
}
