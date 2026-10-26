//! Class-size clause over every diagram with a chart, and the per-member checks of
//! `verify_roots.py`, `verify_keys.py` and `verify_conjecture.py`.

use crate::compose::*;
use crate::diagram::*;
use crate::generate::Atlas;
use crate::marks::*;
use crate::poly::{Poly, jt_poly};
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Mutex;

/// The nonrotation classes of the census, as profile keys.
pub struct Classes {
    pub by_area: Vec<Vec<Vec<Box<[u8]>>>>,
    pub member_of: FxHashMap<Box<[u8]>, (usize, usize)>,
}

impl Classes {
    pub fn load(dir: &std::path::Path, max: usize) -> Classes {
        let mut by_area = vec![Vec::new(); max + 1];
        let mut member_of = FxHashMap::default();
        for n in 1..=max {
            let path = dir.join(format!("area-{n:02}.json"));
            let raw: serde_json::Value =
                serde_json::from_slice(&std::fs::read(&path).expect("census area file")).unwrap();
            assert_eq!(raw["area"].as_u64().unwrap() as usize, n);
            for (ci, cl) in raw["nonrotation"].as_array().unwrap().iter().enumerate() {
                let mut members = Vec::new();
                for p in cl.as_array().unwrap() {
                    let rows: Vec<u8> = p[0].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as u8).collect();
                    let gaps: Vec<u8> = p[1].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as u8).collect();
                    let k = key_of(&(rows, gaps));
                    member_of.insert(k.clone(), (n, ci));
                    members.push(k);
                }
                by_area[n].push(members);
            }
        }
        Classes { by_area, member_of }
    }

    /// The class of F as a set of profile keys.
    pub fn class_of(&self, k: &[u8]) -> Vec<Box<[u8]>> {
        if let Some(&(n, ci)) = self.member_of.get(k) {
            let mut v = self.by_area[n][ci].clone();
            v.sort();
            return v;
        }
        let p = profile_from_key(k);
        let r = key_of(&rot_profile(&p));
        let mut v = vec![k.to_vec().into_boxed_slice(), r];
        v.sort();
        v.dedup();
        v
    }
}

/// A factorization: the first factor and the marked inners (indices into the atlas) after it.
#[derive(Clone)]
pub struct Fact {
    pub first: Cells,
    pub steps: Vec<u32>,
}

fn cost(nf: usize, q: usize) -> (usize, usize) {
    (nf % q, q + nf % q)
}

/// Minimal charts of F, as (outer index, inner index).
pub fn minimal(atlas: &Atlas, f: &[Cell]) -> Vec<(u32, u32)> {
    let Some(cs) = atlas.charts.get(&key_of(&profile_of(f))) else { return vec![] };
    let nf = nd(f) as usize;
    let best = cs.iter().map(|&(_, i)| cost(nf, atlas.inners[i as usize].m.q as usize)).min().unwrap();
    cs.iter().copied().filter(|&(_, i)| cost(nf, atlas.inners[i as usize].m.q as usize) == best).collect()
}

/// Every irreducible factorization of F (Def. 5.5): the first factor has no proper chart and
/// each step is a minimal factorization.
pub fn irreducible(atlas: &Atlas, f: &[Cell], memo: &FxHashMap<Box<[u8]>, Vec<Fact>>) -> Vec<Fact> {
    let sm = minimal(atlas, f);
    if sm.is_empty() {
        return vec![Fact { first: f.to_vec(), steps: vec![] }];
    }
    let mut out = Vec::new();
    for (d, i) in sm {
        let dc = &atlas.outers[d as usize];
        let k = key_of(&profile_of(dc));
        let pre = match memo.get(&k) {
            Some(p) => p.clone(),
            None => irreducible(atlas, dc, memo),
        };
        for mut p in pre {
            p.steps.push(i);
            out.push(p);
        }
    }
    out
}

pub fn realize(atlas: &Atlas, first: &[Cell], steps: &[u32], rot: u32) -> Cells {
    let mut s = if rot & 1 == 1 { rotate(first) } else { first.to_vec() };
    for (k, &i) in steps.iter().enumerate() {
        let inner = &atlas.inners[i as usize];
        s = if rot >> (k + 1) & 1 == 1 {
            compose(&s, &inner.er, &inner.mr)
        } else {
            compose(&s, &inner.e, &inner.m)
        };
    }
    s
}

pub struct SizeRow {
    pub area: usize,
    pub diagrams_with_chart: u64,
    pub factorizations: u64,
    pub longest: usize,
    pub variants_composed: u64,
}

/// Outcome of the class-size check on one diagram with a chart.
struct SizeOut {
    nfac: u64,
    longest: usize,
    variants: u64,
}

fn size_one(atlas: &Atlas, classes: &Classes, k: &[u8], memo: &FxHashMap<Box<[u8]>, Vec<Fact>>) -> (Vec<Fact>, SizeOut) {
    let p = profile_from_key(k);
    let f = cells_of(&p.0, &p.1);
    let facts = irreducible(atlas, &f, memo);
    let cl = classes.class_of(k);
    let mut rs = FxHashSet::default();
    let mut rsm = FxHashSet::default();
    let mut variants = 0u64;
    let mut longest = 0;
    for fa in &facts {
        let first_sym = rotate(&fa.first) == fa.first;
        let r = !first_sym as usize + fa.steps.iter().filter(|&&i| !atlas.inners[i as usize].sym).count();
        let rm = !first_sym as usize + fa.steps.iter().filter(|&&i| !atlas.inners[i as usize].sym_marked).count();
        rs.insert(r);
        rsm.insert(rm);
        let len = fa.steps.len() + 1;
        longest = longest.max(len);
        let mut v: Vec<Box<[u8]>> = (0..1u32 << len)
            .map(|bits| key_of(&profile_of(&realize(atlas, &fa.first, &fa.steps, bits))))
            .collect();
        variants += 1 << len;
        v.sort();
        v.dedup();
        assert!(v == cl, "the reversal variants of an irreducible factorization are not the class: {:?}", p);
    }
    assert_eq!(rs.len(), 1, "r depends on the factorization: {:?}", p);
    let r = *rs.iter().next().unwrap();
    assert_eq!(1usize << r, cl.len(), "class size is not 2^r: {:?}", p);
    assert!(rs == rsm, "marked and unmarked symmetry counts differ: {:?}", p);
    let nfac = facts.len() as u64;
    (facts, SizeOut { nfac, longest, variants })
}

/// The class-size clause on every connected diagram of at most `atlas.nmax` cells with a proper
/// chart.  Areas are processed in increasing order, so the factorizations of every outer are
/// memoized before they are needed.
pub fn size_check_all(atlas: &Atlas, classes: &Classes) -> Vec<SizeRow> {
    let mut by_area: Vec<Vec<&Box<[u8]>>> = vec![Vec::new(); atlas.nmax + 1];
    for k in atlas.charts.keys() {
        let p = profile_from_key(k);
        by_area[p.0.iter().map(|&r| r as usize).sum::<usize>()].push(k);
    }
    let mut memo: FxHashMap<Box<[u8]>, Vec<Fact>> = FxHashMap::default();
    let dmax = atlas.nmax / 2;
    let mut rows = Vec::new();
    for (area, keys) in by_area.iter().enumerate() {
        if keys.is_empty() {
            continue;
        }
        let out: Vec<(Box<[u8]>, Vec<Fact>, SizeOut)> = keys
            .par_iter()
            .map(|k| {
                let (facts, o) = size_one(atlas, classes, k, &memo);
                ((*k).clone(), facts, o)
            })
            .collect();
        let mut row = SizeRow { area, diagrams_with_chart: 0, factorizations: 0, longest: 0, variants_composed: 0 };
        for (k, facts, o) in out {
            row.diagrams_with_chart += 1;
            row.factorizations += o.nfac;
            row.longest = row.longest.max(o.longest);
            row.variants_composed += o.variants;
            if area <= dmax {
                memo.insert(k, facts);
            }
        }
        rows.push(row);
    }
    rows
}

// ------------------------------------------------------------------------------------------ keys

/// Interned exact outer polynomials and canonical marked inners, so that keys are integer pairs.
#[derive(Default)]
pub struct Interner {
    polys: FxHashMap<Poly, u32>,
    poly_of: FxHashMap<Cells, u32>,
    marked: FxHashMap<MarkedTuple, u32>,
}

pub type Key = (u32, u32);

impl Interner {
    pub fn poly(me: &Mutex<Interner>, d: &[Cell]) -> u32 {
        if let Some(&id) = me.lock().unwrap().poly_of.get(d) {
            return id;
        }
        let p = jt_poly(d);
        let mut g = me.lock().unwrap();
        let n = g.polys.len() as u32;
        let id = *g.polys.entry(p).or_insert(n);
        g.poly_of.insert(d.to_vec(), id);
        id
    }
    pub fn marked(me: &Mutex<Interner>, e: &[Cell], m: &Mark) -> u32 {
        let t = canon_marked(e, m);
        let mut g = me.lock().unwrap();
        let n = g.marked.len() as u32;
        *g.marked.entry(t).or_insert(n)
    }
}

pub fn key(me: &Mutex<Interner>, c: &Chart, corrupt: bool) -> Key {
    let d = if corrupt { transpose(&c.d) } else { c.d.clone() };
    (Interner::marked(me, &c.e, &c.m), Interner::poly(me, &d))
}

/// Key modulo the ordinary gauge (`verify_keys.gauge_key`, with the uniqueness assertion of
/// `roots_keys.gauge_key`).
pub fn gauge_key(me: &Mutex<Interner>, c: &Chart) -> Key {
    if c.m.case == b'b' && !c.m.b.is_empty() {
        let mut alt = FxHashSet::default();
        for m2 in marks(&c.e) {
            if m2.case == b'a' && m2.q == c.m.q && m2.v == (c.m.v.0 + 1, c.m.v.1 + 1) {
                assert_eq!(compose(&antitranspose(&c.d), &c.e, &m2), compose(&c.d, &c.e, &c.m));
                alt.insert((Interner::marked(me, &c.e, &m2), Interner::poly(me, &transpose(&c.d))));
            }
        }
        if !alt.is_empty() {
            assert_eq!(alt.len(), 1);
            return alt.into_iter().next().unwrap();
        }
    }
    key(me, c, false)
}

pub fn minimal_charts(f: &[Cell], cs: &[Chart]) -> Vec<Chart> {
    if cs.is_empty() {
        return vec![];
    }
    let nf = nd(f) as usize;
    let best = cs.iter().map(|c| cost(nf, c.m.q as usize)).min().unwrap();
    cs.iter().filter(|c| cost(nf, c.m.q as usize) == best).cloned().collect()
}

// ------------------------------------------------------------------------------------------ members

pub struct MemberData {
    pub key: Box<[u8]>,
    pub cells: Cells,
    pub charts: Vec<Chart>,
    pub keys: Vec<Key>,
    pub gkeys: Vec<Key>,
    pub allkeys: Vec<Key>,
    pub corrupt: Vec<Key>,
    pub smp: i16,
    pub periods: Vec<i16>,
    pub band_seconds: f64,
    pub sub_seconds: f64,
}

fn keyset(it: impl Iterator<Item = Key>) -> Vec<Key> {
    let mut v: Vec<Key> = it.collect();
    v.sort();
    v.dedup();
    v
}

/// Charts of one member by all three routes, which must agree; then its keys.
pub fn member(atlas: &Atlas, me: &Mutex<Interner>, k: &[u8], run_s: bool) -> MemberData {
    let p = profile_from_key(k);
    let f = cells_of(&p.0, &p.1);
    let g = atlas.charts_of(&f);
    let t = std::time::Instant::now();
    let b = finder_band(&f);
    let band_seconds = t.elapsed().as_secs_f64();
    assert!(b == g, "search B and the forward generation disagree on {:?}", p);
    let t = std::time::Instant::now();
    if run_s {
        let s = finder_subdiagram(&f);
        assert!(s == g, "search S and the forward generation disagree on {:?}", p);
    }
    let sub_seconds = t.elapsed().as_secs_f64();
    assert!(!g.is_empty(), "a member of a nonrotation class without a proper chart: {:?}", p);
    for c in &g {
        chart_ok(&f, c).unwrap_or_else(|e| panic!("{e}: {:?}", p));
    }
    let sm = minimal_charts(&f, &g);
    let mut periods: Vec<i16> = g.iter().map(|c| c.m.q).collect();
    periods.sort();
    periods.dedup();
    MemberData {
        key: k.to_vec().into_boxed_slice(),
        keys: keyset(sm.iter().map(|c| key(me, c, false))),
        gkeys: keyset(sm.iter().map(|c| gauge_key(me, c))),
        allkeys: keyset(g.iter().map(|c| key(me, c, false))),
        corrupt: keyset(sm.iter().map(|c| key(me, c, true))),
        smp: sm[0].m.q,
        periods,
        charts: g,
        cells: f,
        band_seconds,
        sub_seconds,
    }
}

/// A common presentation of Schur-equal X, Y (`verify_conjecture.common_presentation`): the first
/// factors, then the marked inners as (E, mark) of X's and Y's sides.
pub fn common_presentation(
    atlas: &Atlas,
    me: &Mutex<Interner>,
    x: &[Cell],
    y: &[Cell],
) -> (Vec<(Cells, Option<Mark>)>, Vec<(Cells, Option<Mark>)>) {
    if x == y || rotate(x) == y {
        return (vec![(x.to_vec(), None)], vec![(y.to_vec(), None)]);
    }
    let cx = minimal_charts(x, &atlas.charts_of(x));
    let cy = minimal_charts(y, &atlas.charts_of(y));
    let kx: FxHashMap<Key, &Chart> = cx.iter().map(|c| (key(me, c, false), c)).collect();
    let ky: FxHashMap<Key, &Chart> = cy.iter().map(|c| (key(me, c, false), c)).collect();
    let mut common: Vec<&Key> = kx.keys().filter(|k| ky.contains_key(*k)).collect();
    common.sort();
    let k = *common.first().expect("no common minimal key");
    let (a, b) = (kx[k], ky[k]);
    let (er, mr) = rotate_mark(&a.e, &a.m);
    assert!((b.e == a.e && b.m == a.m) || (b.e == er && b.m == mr), "marked inners not equal up to rotation");
    let (mut px, mut py) = common_presentation(atlas, me, &a.d, &b.d);
    px.push((a.e.clone(), Some(a.m.clone())));
    py.push((b.e.clone(), Some(b.m.clone())));
    (px, py)
}

pub fn realize_pres(p: &[(Cells, Option<Mark>)]) -> Cells {
    let mut s = p[0].0.clone();
    for (e, m) in &p[1..] {
        s = compose(&s, e, m.as_ref().unwrap());
    }
    s
}

pub fn same_or_rotated(a: &(Cells, Option<Mark>), b: &(Cells, Option<Mark>)) -> bool {
    if a == b {
        return true;
    }
    match &a.1 {
        None => b.1.is_none() && rotate(&a.0) == b.0,
        Some(m) => {
            let (er, mr) = rotate_mark(&a.0, m);
            b.0 == er && b.1.as_ref() == Some(&mr)
        }
    }
}
