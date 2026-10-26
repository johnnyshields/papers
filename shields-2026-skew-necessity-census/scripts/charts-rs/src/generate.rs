//! Forward generation of every proper chart of every connected diagram of at most `nmax` cells.
//!
//! Every proper chart F = D o_W E with |F| <= nmax is produced, because the enumeration covers
//! every connected inner E with 2 <= |E| <= (2 nmax - 1)/3, every legal mark of E, and every
//! connected outer D with 2 <= |D| <= (nmax - w)/q.  The outer bound is |F| >= q|D| + w
//! (`lem:size`).  The inner bound: the copies of the two cells of D on its least and greatest
//! contents lie in F; they are disjoint when N_D >= 3, and when N_D = 2 they meet only on the
//! contents [q, N_E-1], in at most min(a, c) cells, where a and c count the cells of E on the
//! contents [0, w-1] and [q, N_E-1].  Since E has a cell on each of the q - w >= 1 contents
//! [w, q-1], a + c <= |E| - 1, so |F| >= 2|E| - (|E| - 1)/2, that is 3|E| <= 2|F| - 1.  Both
//! bounds are also asserted on every chart produced.

use crate::compose::compose_limited;
use crate::diagram::*;
use crate::marks::{Mark, marks, rotate_mark, is_symmetric_marked};
use rayon::prelude::*;
use rustc_hash::FxHashMap;

pub struct Inner {
    pub e: Cells,
    pub m: Mark,
    pub er: Cells,
    pub mr: Mark,
    /// E = E* (unmarked symmetry).
    pub sym: bool,
    /// (E, W) equals its rotation as a marked inner.
    pub sym_marked: bool,
}

pub struct Atlas {
    pub nmax: usize,
    pub inners: Vec<Inner>,
    pub outers: Vec<Cells>,
    /// F (profile key) -> its proper charts as (outer index, inner index).
    pub charts: FxHashMap<Box<[u8]>, Vec<(u32, u32)>>,
    pub compositions: u64,
    pub non_skew: u64,
}

pub fn connected_of_area(a: usize) -> Vec<Cells> {
    let mut out = Vec::new();
    for rows in compositions(a) {
        for_each_gaps(&rows, |g| out.push(cells_of(&rows, g)));
    }
    out
}

type Found = (Vec<Inner>, Vec<(Box<[u8]>, u32, u32)>, u64, u64);

pub fn generate(nmax: usize) -> Atlas {
    let dmax = nmax / 2;
    let emax = (2 * nmax - 1) / 3;
    let mut outers: Vec<Cells> = Vec::new();
    let mut outer_end = vec![0usize; dmax + 1];
    for a in 2..=dmax {
        outers.extend(connected_of_area(a));
        outer_end[a] = outers.len();
    }
    let mut inners: Vec<Inner> = Vec::new();
    let mut flat: Vec<(Box<[u8]>, u32, u32)> = Vec::new();
    let (mut compositions_done, mut non_skew) = (0u64, 0u64);
    for a in 2..=emax {
        let found: Vec<Found> = compositions(a)
            .into_par_iter()
            .map(|rows| {
                let mut local: Found = (Vec::new(), Vec::new(), 0, 0);
                for_each_gaps(&rows, |g| {
                    let e = cells_of(&rows, g);
                    let ne_ = nd(&e) as usize;
                    if ne_ + ne_ / 2 + 1 > nmax {
                        return;
                    }
                    for mk in marks(&e) {
                        let q = mk.q as usize;
                        let w = ne_ - q;
                        if q + ne_ > nmax {
                            continue;
                        }
                        let dcap = ((nmax - w) / q).min(dmax);
                        if dcap < 2 {
                            continue;
                        }
                        let id = local.0.len() as u32;
                        let mut used = false;
                        for (di, d) in outers[..outer_end[dcap]].iter().enumerate() {
                            local.2 += 1;
                            let Some(f) = compose_limited(d, &e, &mk, nmax) else { continue };
                            if !is_connected_skew(&f) {
                                local.3 += 1;
                                continue;
                            }
                            assert!(f.len() >= q * d.len() + w, "size bound");
                            assert!(3 * e.len() + 1 <= 2 * f.len(), "inner bound");
                            local.1.push((key_of(&profile_of(&f)), di as u32, id));
                            used = true;
                        }
                        if used {
                            let (er, mr) = rotate_mark(&e, &mk);
                            let sym = crate::diagram::rotate(&e) == e;
                            let sym_marked = is_symmetric_marked(&e, &mk);
                            local.0.push(Inner { e: e.clone(), m: mk, er, mr, sym, sym_marked });
                        }
                    }
                });
                local
            })
            .collect();
        for (ins, fl, c, ns) in found {
            let base = inners.len() as u32;
            inners.extend(ins);
            flat.extend(fl.into_iter().map(|(k, d, i)| (k, d, i + base)));
            compositions_done += c;
            non_skew += ns;
        }
    }
    let mut charts: FxHashMap<Box<[u8]>, Vec<(u32, u32)>> = FxHashMap::default();
    for (k, d, i) in flat {
        charts.entry(k).or_default().push((d, i));
    }
    for v in charts.values_mut() {
        v.sort_unstable();
        let n = v.len();
        v.dedup();
        assert_eq!(n, v.len(), "a chart generated twice");
    }
    Atlas { nmax, inners, outers, charts, compositions: compositions_done, non_skew }
}

impl Atlas {
    /// The charts of F as `Chart`s (empty when F has none).
    pub fn charts_of(&self, f: &[Cell]) -> Vec<crate::compose::Chart> {
        assert!(f.len() <= self.nmax);
        let mut v: Vec<crate::compose::Chart> = self
            .charts
            .get(&key_of(&profile_of(f)))
            .map(|cs| {
                cs.iter()
                    .map(|&(d, i)| {
                        let inner = &self.inners[i as usize];
                        crate::compose::Chart {
                            d: self.outers[d as usize].clone(),
                            e: inner.e.clone(),
                            m: inner.m.clone(),
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();
        v.sort();
        v
    }
}
