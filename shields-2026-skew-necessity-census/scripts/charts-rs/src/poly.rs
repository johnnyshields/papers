//! Exact Jacobi--Trudi polynomials in Z[h_1, h_2, ...] (port of `skew_core.jt_poly_lists`):
//! Laplace expansion along rows, memoized on the set of used columns.  A monomial is the weakly
//! decreasing list of its indices.  Coefficient arithmetic is overflow-checked.

use crate::diagram::*;
use rustc_hash::FxHashMap;
use std::rc::Rc;

pub type Poly = Vec<(Vec<u8>, i64)>;

pub fn jt_poly(d: &[Cell]) -> Poly {
    let (rows, gaps) = profile_of(d);
    let n = rows.len();
    assert!(n <= 32);
    let mut x = vec![0i16; n];
    let mut y = vec![0i16; n];
    x[n - 1] = rows[n - 1] as i16;
    for i in (0..n - 1).rev() {
        y[i] = x[i + 1] - gaps[i] as i16;
        x[i] = y[i] + rows[i] as i16;
    }
    type P = Rc<FxHashMap<Vec<u8>, i64>>;
    fn rec(i: usize, used: u32, x: &[i16], y: &[i16], memo: &mut FxHashMap<u32, P>) -> P {
        if let Some(p) = memo.get(&used) {
            return p.clone();
        }
        let n = x.len();
        let mut acc: FxHashMap<Vec<u8>, i64> = FxHashMap::default();
        if i == n {
            acc.insert(vec![], 1);
        } else {
            let mut k = 0;
            for j in 0..n {
                if used >> j & 1 == 1 {
                    k += 1;
                    continue;
                }
                let t = x[i] - y[j];
                if t < 0 {
                    continue;
                }
                let sgn: i64 = if (j - k) % 2 == 1 { -1 } else { 1 };
                let sub = rec(i + 1, used | 1 << j, x, y, memo);
                for (m, c) in sub.iter() {
                    let mut mm = m.clone();
                    if t > 0 {
                        let pos = mm.iter().position(|&a| (a as i16) < t).unwrap_or(mm.len());
                        mm.insert(pos, t as u8);
                    }
                    let e = acc.entry(mm).or_insert(0);
                    *e = e.checked_add(sgn.checked_mul(*c).unwrap()).unwrap();
                }
            }
            acc.retain(|_, c| *c != 0);
        }
        let p = Rc::new(acc);
        memo.insert(used, p.clone());
        p
    }
    let mut memo = FxHashMap::default();
    let p = rec(0, 0, &x, &y, &mut memo);
    let mut v: Poly = p.iter().map(|(m, c)| (m.clone(), *c)).collect();
    v.sort();
    v
}
