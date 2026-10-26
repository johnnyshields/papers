use serde::{Deserialize, Serialize};

pub const MAX: usize = 35;
const ROW_BITS: u32 = 35;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Profile(pub Vec<u8>, pub Vec<u8>);

impl Profile {
    pub fn rotation(&self) -> Self {
        Self(
            self.0.iter().rev().copied().collect(),
            self.1.iter().rev().copied().collect(),
        )
    }
    pub fn canonical(&self) -> Self {
        std::cmp::min(self.clone(), self.rotation())
    }
    pub fn valid(&self) -> bool {
        !self.0.is_empty()
            && self.0.iter().all(|&r| r > 0)
            && self.1.len() + 1 == self.0.len()
            && self
                .1
                .iter()
                .enumerate()
                .all(|(i, &g)| g < self.0[i].min(self.0[i + 1]))
            && self.0.iter().map(|&r| r as usize).sum::<usize>() <= MAX
    }
    pub fn code(&self) -> u64 {
        assert!(self.valid());
        pack(&self.0, &self.1)
    }
    pub fn decode(code: u64) -> Self {
        let mut mask = code & ((1u64 << ROW_BITS) - 1);
        let mut prev = 0;
        let mut rows = Vec::new();
        while mask != 0 {
            let pos = mask.trailing_zeros() as u8 + 1;
            rows.push(pos - prev);
            prev = pos;
            mask &= mask - 1;
        }
        let mut rank = code >> ROW_BITS;
        let mut gaps = vec![0; rows.len() - 1];
        for i in (0..gaps.len()).rev() {
            let radix = rows[i].min(rows[i + 1]) as u64;
            gaps[i] = (rank % radix) as u8;
            rank /= radix;
        }
        assert_eq!(rank, 0);
        Self(rows, gaps)
    }
}

pub fn pack(rows: &[u8], gaps: &[u8]) -> u64 {
    let mut mask = 0u64;
    let mut sum = 0;
    for &r in rows {
        sum += r;
        mask |= 1u64 << (sum - 1);
    }
    let mut rank = 0u64;
    for (i, &g) in gaps.iter().enumerate() {
        rank = rank * rows[i].min(rows[i + 1]) as u64 + g as u64;
    }
    assert!(rank < (1u64 << (64 - ROW_BITS)));
    mask | (rank << ROW_BITS)
}

// Construct actual row intervals, then subtract the row index in Jacobi--Trudi.
// Translation does not affect any difference right[i]+1-left[j]-i+j.
pub fn coordinates(rows: &[u8], gaps: &[u8]) -> ([i16; MAX], [i16; MAX]) {
    let mut x = [0; MAX];
    let mut y = [0; MAX];
    let mut left = 0i16;
    for i in 0..rows.len() {
        if i > 0 {
            left += gaps[i - 1] as i16 + 1 - rows[i] as i16;
        }
        y[i] = left - i as i16;
        x[i] = y[i] + rows[i] as i16;
    }
    (x, y)
}

pub fn partitions(n: u8) -> Vec<Vec<u8>> {
    fn visit(rem: u8, bound: u8, cur: &mut Vec<u8>, out: &mut Vec<Vec<u8>>) {
        if rem == 0 {
            out.push(cur.clone());
            return;
        }
        for r in (1..=rem.min(bound)).rev() {
            cur.push(r);
            visit(rem - r, r, cur, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    visit(n, n, &mut Vec::new(), &mut out);
    out
}

// Mixed-radix remaining-multiplicity states, with the last chosen row as boundary.
pub fn shard_count(parts: &[u8]) -> u64 {
    let mut values = Vec::new();
    let mut counts = Vec::new();
    for &r in parts {
        if values.last() == Some(&r) {
            *counts.last_mut().unwrap() += 1u8;
        } else {
            values.push(r);
            counts.push(1u8);
        }
    }
    let mut stride = Vec::new();
    let mut states = 1usize;
    for &c in &counts {
        stride.push(states);
        states *= c as usize + 1;
    }
    let k = values.len();
    let mut table = vec![0u64; states * k];
    for v in &mut table[..k] {
        *v = 1;
    }
    for state in 1..states {
        for last in 0..k {
            let mut total = 0u64;
            for j in 0..k {
                if state / stride[j] % (counts[j] as usize + 1) != 0 {
                    total +=
                        values[last].min(values[j]) as u64 * table[(state - stride[j]) * k + j];
                }
            }
            table[state * k + last] = total;
        }
    }
    (0..k)
        .map(|j| table[(states - 1 - stride[j]) * k + j])
        .sum()
}

// Independent area transfer count, including reflection-fixed profiles.
pub fn area_counts(max: usize) -> (Vec<u64>, Vec<u64>) {
    let mut ways = vec![vec![0u64; max + 1]; max + 1];
    for area in 1..=max {
        for first in 1..=area {
            ways[area][first] = if first == area {
                1
            } else {
                (1..=area - first)
                    .map(|next| first.min(next) as u64 * ways[area - first][next])
                    .sum()
            };
        }
    }
    let total = ways.iter().map(|v| v.iter().sum()).collect();
    let mut fixed = vec![0u64; max + 1];
    for area in 1..=max {
        fixed[area] = 1;
        for half in 1..=area / 2 {
            let center = area - 2 * half;
            for inner in 1..=half {
                fixed[area] += ways[half][inner]
                    * if center == 0 {
                        inner
                    } else {
                        inner.min(center)
                    } as u64;
            }
        }
    }
    (total, fixed)
}

pub struct Enumeration {
    pub profiles: u64,
    pub orbits: u64,
    pub fixed: u64,
}

pub fn enumerate(parts: &[u8], mut callback: impl FnMut(&[u8], &[u8], u64)) -> Enumeration {
    let mut multiplicity = [0u8; MAX + 1];
    for &r in parts {
        multiplicity[r as usize] += 1;
    }
    let values: Vec<u8> = (1..=MAX)
        .filter(|&r| multiplicity[r] > 0)
        .map(|r| r as u8)
        .collect();
    let mut rows = [0u8; MAX];
    let mut gaps = [0u8; MAX];
    let mut tally = Enumeration {
        profiles: 0,
        orbits: 0,
        fixed: 0,
    };
    fn gaps_visit(
        rows: &[u8],
        gaps: &mut [u8],
        pos: usize,
        pal_rows: bool,
        tally: &mut Enumeration,
        callback: &mut impl FnMut(&[u8], &[u8], u64),
    ) {
        if pos == gaps.len() {
            let cmp = if pal_rows {
                gaps.iter().cmp(gaps.iter().rev())
            } else {
                std::cmp::Ordering::Less
            };
            if cmp.is_gt() {
                return;
            }
            tally.orbits += 1;
            tally.fixed += u64::from(cmp.is_eq());
            callback(rows, gaps, pack(rows, gaps));
            return;
        }
        for g in 0..rows[pos].min(rows[pos + 1]) {
            gaps[pos] = g;
            gaps_visit(rows, gaps, pos + 1, pal_rows, tally, callback);
        }
    }
    fn rows_visit(
        pos: usize,
        len: usize,
        values: &[u8],
        counts: &mut [u8; MAX + 1],
        rows: &mut [u8; MAX],
        gaps: &mut [u8; MAX],
        tally: &mut Enumeration,
        callback: &mut impl FnMut(&[u8], &[u8], u64),
    ) {
        if pos == len {
            let rs = &rows[..len];
            tally.profiles += rs
                .windows(2)
                .map(|p| p[0].min(p[1]) as u64)
                .product::<u64>();
            let cmp = rs.iter().cmp(rs.iter().rev());
            if !cmp.is_gt() {
                gaps_visit(rs, &mut gaps[..len - 1], 0, cmp.is_eq(), tally, callback);
            }
            return;
        }
        for &r in values {
            if counts[r as usize] == 0 {
                continue;
            }
            counts[r as usize] -= 1;
            rows[pos] = r;
            rows_visit(pos + 1, len, values, counts, rows, gaps, tally, callback);
            counts[r as usize] += 1;
        }
    }
    rows_visit(
        0,
        parts.len(),
        &values,
        &mut multiplicity,
        &mut rows,
        &mut gaps,
        &mut tally,
        &mut callback,
    );
    assert_eq!(tally.profiles, 2 * tally.orbits - tally.fixed);
    tally
}

// All positive k-row intersections. Zero intersections are determined by row count.
// Additive hashing may merge invariants but can never split equal invariants.
pub fn overlaps_hash(rows: &[u8], gaps: &[u8]) -> u64 {
    let (x, y) = coordinates(rows, gaps);
    let mut out = 0u64;
    for i in 0..rows.len() {
        for j in i + 1..rows.len() {
            let overlap = x[j] - y[i] + (j - i) as i16;
            if overlap <= 0 {
                break;
            }
            let key = ((j - i + 1) * 64 + overlap as usize) as u64;
            out = out.wrapping_add(mix(key));
        }
    }
    out
}

pub fn mix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e3779b97f4a7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}
