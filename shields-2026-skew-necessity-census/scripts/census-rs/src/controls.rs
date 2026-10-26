use crate::{
    algebra::{self, P, Point, Polynomial, Q},
    census::{self, SEED1, SEED2, Shard},
    model::{self, Profile},
};
use std::{collections::BTreeMap, path::Path};

// A separate enumeration: every cut subset of N-1 positions, followed by an
// integer counter in the product of the adjacent overlap radices.
fn direct_profiles(area: usize) -> Vec<Profile> {
    let mut profiles = Vec::new();
    for cut in 0u64..(1u64 << (area - 1)) {
        let mask = cut | (1u64 << (area - 1));
        let mut rows = Vec::new();
        let mut prev = 0;
        for pos in 1..=area {
            if mask & (1u64 << (pos - 1)) != 0 {
                rows.push((pos - prev) as u8);
                prev = pos;
            }
        }
        let choices: usize = rows.windows(2).map(|r| r[0].min(r[1]) as usize).product();
        for mut rank in 0..choices {
            let mut gaps = Vec::new();
            for pair in rows.windows(2) {
                let radix = pair[0].min(pair[1]) as usize;
                gaps.push((rank % radix) as u8);
                rank /= radix;
            }
            profiles.push(Profile(rows.clone(), gaps));
        }
    }
    profiles
}

pub fn run(scratch: &Path) {
    assert!(algebra::prime(P) && algebra::prime(Q));
    let a = Point::new(P, SEED1);
    let b = Point::new(Q, SEED2);
    let (counts, fixed) = model::area_counts(11);
    for area in 1..=9 {
        let direct = direct_profiles(area);
        assert_eq!(direct.len() as u64, counts[area]);
        assert_eq!(
            direct.iter().filter(|f| **f == f.rotation()).count() as u64,
            fixed[area]
        );
        let mut classes: BTreeMap<Polynomial, Vec<Profile>> = BTreeMap::new();
        for profile in &direct {
            assert!(profile.valid());
            assert_eq!(Profile::decode(profile.code()), *profile);
            let poly = algebra::exact(profile);
            assert_eq!(poly, algebra::exact(&profile.rotation()));
            for point in [&a, &b] {
                assert_eq!(
                    point.eval(&profile.0, &profile.1),
                    algebra::evaluate_polynomial(&poly, point)
                );
            }
            classes.entry(poly).or_default().push(profile.clone());
        }
        let mut hist = BTreeMap::new();
        let mut nonrotation = Vec::new();
        for members in classes.values_mut() {
            members.sort_unstable();
            *hist.entry(members.len()).or_insert(0u64) += 1;
            if members
                .iter()
                .any(|f| f.canonical() != members[0].canonical())
            {
                nonrotation.push(members.clone());
            }
        }
        nonrotation.sort_unstable();
        let shards: Vec<_> = model::partitions(area as u8)
            .iter()
            .map(|parts| {
                census::compute_shard(
                    parts,
                    model::shard_count(parts),
                    &scratch.join("controls"),
                    100000,
                )
            })
            .collect();
        let result = census::aggregate(area, &shards, 0., 1);
        assert_eq!(result.histogram, hist);
        assert_eq!(result.nonrotation, nonrotation);
        if area == 9 {
            let a = Profile(vec![1, 2, 1, 3, 2], vec![0; 4]);
            let b = Profile(vec![1, 3, 2, 1, 2], vec![0; 4]);
            assert!(
                result
                    .nonrotation
                    .iter()
                    .any(|cl| cl.contains(&a) && cl.contains(&b))
            );
        }
    }
    for area in 10..=35 {
        let mut rows = Vec::new();
        let mut used = 0;
        while used < area {
            let r = 1 + model::mix((area * 100 + used) as u64) as usize % (area - used).min(5);
            rows.push(r as u8);
            used += r;
        }
        let gaps = rows
            .windows(2)
            .enumerate()
            .map(|(i, r)| (model::mix((area + i) as u64) % r[0].min(r[1]) as u64) as u8)
            .collect();
        let f = Profile(rows, gaps);
        assert_eq!(Profile::decode(f.code()), f);
        let poly = algebra::exact(&f);
        for point in [&a, &b, &a.with_zero(1), &b.with_zero(2)] {
            assert_eq!(
                point.eval(&f.0, &f.1),
                algebra::evaluate_polynomial(&poly, point)
            );
        }
    }
    let ribbon_a = Profile(vec![1, 2, 1, 3, 2], vec![0; 4]);
    let ribbon_b = Profile(vec![1, 3, 2, 1, 2], vec![0; 4]);
    let perturbation = Profile(vec![1, 1, 2, 3, 2], vec![0; 4]);
    assert_ne!(ribbon_a.canonical(), ribbon_b.canonical());
    assert_eq!(algebra::exact(&ribbon_a), algebra::exact(&ribbon_b));
    assert_ne!(algebra::exact(&ribbon_a), algebra::exact(&perturbation));
    assert_ne!(
        a.eval(&ribbon_a.0, &ribbon_a.1),
        a.eval(&perturbation.0, &perturbation.1)
    );
    let expected = algebra::evaluate_polynomial(&algebra::exact(&ribbon_a), &a);
    let planted = (expected + 1) % P;
    assert_ne!(a.eval(&ribbon_a.0, &ribbon_a.1), planted);
    let mut zero = b.clone();
    for h in &mut zero.h[1..] {
        *h = 0;
    }
    let mut shard = Shard {
        histogram: BTreeMap::from([(2, 3)]),
        ..Default::default()
    };
    let candidates = [&ribbon_a, &ribbon_b, &perturbation].map(|f| f.canonical().code());
    census::refine(&candidates, &mut shard, &zero);
    assert_eq!(shard.exact_false_merges_split, 1);
    assert_eq!(shard.histogram, BTreeMap::from([(2, 1), (4, 1)]));
    let parts = vec![3, 2, 2, 1, 1];
    let in_memory = census::compute_shard(
        &parts,
        model::shard_count(&parts),
        &scratch.join("memory-control"),
        100000,
    );
    let spilled = census::compute_shard(
        &parts,
        model::shard_count(&parts),
        &scratch.join("spill-control"),
        13,
    );
    assert_eq!(in_memory.histogram, spilled.histogram);
    assert_eq!(in_memory.nonrotation, spilled.nonrotation);
    assert!(spilled.spilled_records > 0);
    println!(
        "PASS controls: exhaustive exact census 1..9 without invariants; independent cut enumeration; polynomial/evaluation/rotation agreement; 9-cell ribbon pair; perturbation; planted wrong value; forced collision split exactly; external merge agrees; sampled areas 10..35 and zero entries agree with exact polynomials"
    );
}

#[cfg(test)]
mod tests {
    #[test]
    fn controls() {
        super::run(std::path::Path::new(
            "/home/shields/r167-lanes/_rust35/tests",
        ));
    }
}
