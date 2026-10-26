use crate::model::{MAX, Profile, coordinates, mix};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

thread_local! {
    static MATRIX: RefCell<[[u64; MAX]; MAX]> = const { RefCell::new([[0; MAX]; MAX]) };
}

pub const P: u64 = (1u64 << 61) - 1;
pub const Q: u64 = (1u64 << 61) - 31;

#[inline(always)]
pub fn mul(a: u64, b: u64, modulus: u64) -> u64 {
    let z = a as u128 * b as u128;
    if modulus == P {
        let t = (z as u64 & P) + (z >> 61) as u64;
        if t >= P { t - P } else { t }
    } else {
        (z % modulus as u128) as u64
    }
}
#[inline(always)]
fn sub(a: u64, b: u64, modulus: u64) -> u64 {
    if a >= b { a - b } else { modulus - (b - a) }
}
pub fn power(mut a: u64, mut e: u64, modulus: u64) -> u64 {
    let mut r = 1;
    while e > 0 {
        if e & 1 != 0 {
            r = mul(r, a, modulus);
        }
        a = mul(a, a, modulus);
        e >>= 1;
    }
    r
}

#[derive(Clone)]
pub struct Point {
    pub modulus: u64,
    pub h: [u64; MAX + 1],
    inv: [u64; MAX + 1],
}
impl Point {
    pub fn new(modulus: u64, seed: u64) -> Self {
        let mut h = [1; MAX + 1];
        let mut inv = [1; MAX + 1];
        for k in 1..=MAX {
            h[k] = 1 + mix(seed + k as u64) % (modulus - 1);
            inv[k] = power(h[k], modulus - 2, modulus);
        }
        Self { modulus, h, inv }
    }
    pub fn with_zero(&self, degree: usize) -> Self {
        assert!(degree > 0 && degree <= MAX);
        let mut point = self.clone();
        point.h[degree] = 0;
        point.inv[degree] = 0;
        point
    }
    pub fn eval(&self, rows: &[u8], gaps: &[u8]) -> u64 {
        MATRIX.with(|workspace| self.eval_in(rows, gaps, &mut workspace.borrow_mut()))
    }
    fn eval_in(&self, rows: &[u8], gaps: &[u8], matrix: &mut [[u64; MAX]; MAX]) -> u64 {
        let n = rows.len();
        let (x, y) = coordinates(rows, gaps);
        // The column supports are nested prefixes. Every read below is inside
        // its original prefix, including elimination updates in later columns.
        // Overwrite those prefixes; structurally zero entries are never read.
        let mut bottom = [0usize; MAX];
        for j in 0..n {
            for i in 0..n {
                let d = x[i] - y[j];
                if d < 0 {
                    break;
                }
                matrix[i][j] = self.h[d as usize];
                bottom[j] = i;
            }
        }
        let p = self.modulus;
        let mut active = (1u64 << n) - 1;
        let mut changed = 0u64;
        let mut det = 1;
        let mut negative = false;
        for col in 0..n {
            let mut candidates = active & ((1u64 << (bottom[col] + 1)) - 1);
            let pivot;
            loop {
                if candidates == 0 {
                    return 0;
                }
                let r = 63 - candidates.leading_zeros() as usize;
                if matrix[r][col] != 0 {
                    pivot = r;
                    break;
                }
                candidates &= !(1u64 << r);
            }
            let pivot_bit = 1u64 << pivot;
            negative ^= (active & (pivot_bit - 1)).count_ones() % 2 == 1;
            active ^= pivot_bit;
            let value = matrix[pivot][col];
            det = mul(det, value, p);
            if col + 1 == n {
                break;
            }
            let inverse = if changed & pivot_bit == 0 {
                self.inv[(x[pivot] - y[col]) as usize]
            } else {
                power(value, p - 2, p)
            };
            let mut todo = active & ((1u64 << (bottom[col] + 1)) - 1);
            while todo != 0 {
                let r = todo.trailing_zeros() as usize;
                todo &= todo - 1;
                if matrix[r][col] == 0 {
                    continue;
                }
                let factor = mul(matrix[r][col], inverse, p);
                changed |= 1u64 << r;
                for j in col + 1..n {
                    matrix[r][j] = sub(matrix[r][j], mul(factor, matrix[pivot][j], p), p);
                }
            }
        }
        if negative && det != 0 { p - det } else { det }
    }
}

// Exterior multiplication of rows, from bottom to top. Each state is a selected
// column subset; each coefficient is an exact polynomial in independent h_i.
// Checked i128 arithmetic makes overflow a failure, never silent corruption.
pub type Polynomial = BTreeMap<Vec<u8>, i128>;
pub fn exact(profile: &Profile) -> Polynomial {
    assert!(profile.valid());
    let n = profile.0.len();
    let (x, y) = coordinates(&profile.0, &profile.1);
    let area: usize = profile.0.iter().map(|&r| r as usize).sum();
    // Column supports are nested prefixes. The number of nonzero Leibniz
    // terms is product_j (support_length[j]-j). There are at most area-1
    // nonzero entries strictly below the diagonal, hence at most 2^(area-1)
    // terms. Every bottom-row partial matching extends to a full matching.
    let mut term_bound = 1u64;
    let mut below = 0;
    for j in 0..n {
        let support = x[..n].iter().take_while(|&&a| a >= y[j]).count();
        assert!(support > j);
        term_bound *= (support - j) as u64;
        below += support - j - 1;
    }
    assert!(below < area && term_bound <= (1u64 << (area - 1)));
    let mut states: HashMap<u64, Polynomial> = HashMap::new();
    states.insert(0, BTreeMap::from([(Vec::new(), 1)]));
    for row in (0..n).rev() {
        let mut next: HashMap<u64, Polynomial> = HashMap::new();
        for (mask, poly) in states {
            for col in 0..n {
                if mask & (1u64 << col) != 0 {
                    continue;
                }
                let degree = x[row] - y[col];
                if degree < 0 {
                    continue;
                }
                let sign = if (mask & ((1u64 << col) - 1)).count_ones() % 2 == 0 {
                    1i128
                } else {
                    -1
                };
                let target = next.entry(mask | (1u64 << col)).or_default();
                for (monomial, coefficient) in &poly {
                    let mut term = monomial.clone();
                    if degree > 0 {
                        let pos = term.partition_point(|&v| v > degree as u8);
                        term.insert(pos, degree as u8);
                    }
                    let entry = target.entry(term).or_default();
                    *entry = entry
                        .checked_add(coefficient.checked_mul(sign).unwrap())
                        .expect("exact coefficient overflow");
                }
            }
        }
        for poly in next.values_mut() {
            poly.retain(|_, c| *c != 0);
        }
        states = next;
    }
    states.remove(&((1u64 << n) - 1)).unwrap()
}

pub fn evaluate_polynomial(poly: &Polynomial, point: &Point) -> u64 {
    let p = point.modulus;
    let mut out = 0;
    for (monomial, &coefficient) in poly {
        let mut val = coefficient.rem_euclid(p as i128) as u64;
        for &d in monomial {
            val = mul(val, point.h[d as usize], p);
        }
        out += val;
        if out >= p {
            out -= p;
        }
    }
    out
}

// Deterministic Miller--Rabin bases sufficient for all unsigned 64-bit integers.
pub fn prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    for a in [2, 325, 9375, 28178, 450775, 9780504, 1795265022] {
        if a % n == 0 {
            continue;
        }
        let mut x = power(a % n, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        let mut witness = true;
        for _ in 1..s {
            x = mul(x, x, n);
            if x == n - 1 {
                witness = false;
                break;
            }
        }
        if witness {
            return false;
        }
    }
    true
}
