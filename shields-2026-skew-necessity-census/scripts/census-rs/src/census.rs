use crate::{
    algebra::{self, P, Point, Polynomial, Q},
    model::{self, Profile},
    storage,
};
use serde::{Deserialize, Serialize};
use std::{
    cmp::Reverse,
    collections::{BTreeMap, BinaryHeap},
    fs::{self, File},
    io::{BufReader, BufWriter, Read, Write},
    path::Path,
    time::Instant,
};

pub const FORMAT: &str = "skew-census-v1";
pub const SEED1: u64 = 0x748c21a90d36ef52;
pub const SEED2: u64 = 0xa3720f4db19e856c;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Record {
    value: u64,
    code: u64,
}

#[derive(Default, Serialize, Deserialize)]
pub struct Shard {
    pub format: String,
    pub parts: Vec<u8>,
    pub profiles: u64,
    pub rotation_orbits: u64,
    pub fixed: u64,
    pub histogram: BTreeMap<usize, u64>,
    pub nonrotation: Vec<Vec<Profile>>,
    pub first_collision_groups: u64,
    pub second_evaluations: u64,
    pub exact_groups: u64,
    pub exact_profiles: u64,
    pub exact_false_merges_split: u64,
    pub first_false_merges_split: u64,
    pub spilled_records: u64,
    pub seconds: f64,
}

#[derive(Serialize, Deserialize)]
pub struct Area {
    pub format: String,
    pub area: usize,
    pub profiles: u64,
    pub rotation_orbits: u64,
    pub fixed: u64,
    pub classes: u64,
    pub histogram: BTreeMap<usize, u64>,
    pub nonrotation_classes: usize,
    pub nonrotation_members: usize,
    pub nonrotation: Vec<Vec<Profile>>,
    pub first_collision_groups: u64,
    pub second_evaluations: u64,
    pub exact_groups: u64,
    pub exact_profiles: u64,
    pub exact_false_merges_split: u64,
    pub first_false_merges_split: u64,
    pub spilled_records: u64,
    pub seconds: f64,
    pub shard_seconds: f64,
    pub peak_rss_kib: u64,
    pub threads: usize,
    pub controls_passed: bool,
}

pub fn refine(group: &[u64], shard: &mut Shard, second: &Point) {
    if group.len() < 2 {
        return;
    }
    shard.first_collision_groups += 1;
    let mut invariant_groups: BTreeMap<u64, Vec<Profile>> = BTreeMap::new();
    for &code in group {
        let f = Profile::decode(code);
        invariant_groups
            .entry(model::overlaps_hash(&f.0, &f.1))
            .or_default()
            .push(f);
    }
    let mut final_groups = 0usize;
    for invariant_group in invariant_groups.values() {
        if invariant_group.len() == 1 {
            final_groups += 1;
            continue;
        }
        let mut eval_groups: BTreeMap<u64, Vec<Profile>> = BTreeMap::new();
        for f in invariant_group {
            shard.second_evaluations += 1;
            eval_groups
                .entry(second.eval(&f.0, &f.1))
                .or_default()
                .push(f.clone());
        }
        for (&value, candidates) in &eval_groups {
            if candidates.len() == 1 {
                final_groups += 1;
                continue;
            }
            shard.exact_groups += 1;
            shard.exact_profiles += candidates.len() as u64;
            let mut polynomials: BTreeMap<Polynomial, Vec<Profile>> = BTreeMap::new();
            for f in candidates {
                let poly = algebra::exact(f);
                assert_eq!(algebra::evaluate_polynomial(&poly, second), value);
                polynomials.entry(poly).or_default().push(f.clone());
            }
            shard.exact_false_merges_split += polynomials.len() as u64 - 1;
            final_groups += polynomials.len();
            for orbit_reps in polynomials.values() {
                if orbit_reps.len() == 1 {
                    continue;
                }
                let mut members = Vec::new();
                for f in orbit_reps {
                    let rotated = f.rotation();
                    let size = if *f == rotated { 1 } else { 2 };
                    *shard.histogram.entry(size).or_default() -= 1;
                    members.push(f.clone());
                    if size == 2 {
                        members.push(rotated);
                    }
                }
                members.sort_unstable();
                assert!(members.windows(2).all(|p| p[0] != p[1]));
                *shard.histogram.entry(members.len()).or_default() += 1;
                shard.nonrotation.push(members);
            }
        }
    }
    shard.first_false_merges_split += final_groups as u64 - 1;
}

fn write_run(path: &Path, records: &mut Vec<Record>) {
    records.sort_unstable();
    storage::wait_for_hot_space(path.parent().unwrap());
    let mut writer = BufWriter::with_capacity(1 << 20, File::create(path).unwrap());
    for record in records.iter() {
        writer.write_all(&record.value.to_le_bytes()).unwrap();
        writer.write_all(&record.code.to_le_bytes()).unwrap();
    }
    writer.flush().unwrap();
    records.clear();
}

fn read_record(reader: &mut BufReader<File>) -> Option<Record> {
    let mut bytes = [0u8; 16];
    let count = reader.read(&mut bytes[..1]).unwrap();
    if count == 0 {
        return None;
    }
    reader.read_exact(&mut bytes[1..]).unwrap();
    Some(Record {
        value: u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        code: u64::from_le_bytes(bytes[8..].try_into().unwrap()),
    })
}

pub fn compute_shard(parts: &[u8], predicted: u64, scratch: &Path, cap: usize) -> Shard {
    let start = Instant::now();
    let first = Point::new(P, SEED1);
    let second = Point::new(Q, SEED2);
    let mut records = Vec::with_capacity(cap.min(predicted as usize));
    let mut runs = Vec::new();
    let tally = model::enumerate(parts, |rows, gaps, code| {
        records.push(Record {
            value: first.eval(rows, gaps),
            code,
        });
        if records.len() == cap {
            fs::create_dir_all(scratch).unwrap();
            let path = scratch.join(format!("run-{:04}.bin", runs.len()));
            write_run(&path, &mut records);
            runs.push(path);
        }
    });
    assert_eq!(
        tally.profiles, predicted,
        "row-multiset enumeration differs from DP: {parts:?}"
    );
    let mut shard = Shard {
        format: FORMAT.into(),
        parts: parts.to_vec(),
        profiles: tally.profiles,
        rotation_orbits: tally.orbits,
        fixed: tally.fixed,
        histogram: BTreeMap::from([(1, tally.fixed), (2, tally.orbits - tally.fixed)]),
        ..Default::default()
    };
    if runs.is_empty() {
        records.sort_unstable();
        let mut begin = 0;
        while begin < records.len() {
            let mut end = begin + 1;
            while end < records.len() && records[end].value == records[begin].value {
                end += 1;
            }
            if end - begin > 1 {
                refine(
                    &records[begin..end]
                        .iter()
                        .map(|r| r.code)
                        .collect::<Vec<_>>(),
                    &mut shard,
                    &second,
                );
            }
            begin = end;
        }
    } else {
        if !records.is_empty() {
            let path = scratch.join(format!("run-{:04}.bin", runs.len()));
            write_run(&path, &mut records);
            runs.push(path);
        }
        drop(records);
        shard.spilled_records = tally.orbits;
        let mut readers: Vec<_> = runs
            .iter()
            .map(|path| BufReader::with_capacity(1 << 18, File::open(path).unwrap()))
            .collect();
        let mut heap = BinaryHeap::new();
        for (idx, reader) in readers.iter_mut().enumerate() {
            if let Some(record) = read_record(reader) {
                heap.push(Reverse((record, idx)));
            }
        }
        let mut value = None;
        let mut codes = Vec::new();
        let mut merged = 0;
        while let Some(Reverse((record, idx))) = heap.pop() {
            if value != Some(record.value) {
                refine(&codes, &mut shard, &second);
                codes.clear();
                value = Some(record.value);
            }
            codes.push(record.code);
            merged += 1;
            if let Some(next) = read_record(&mut readers[idx]) {
                heap.push(Reverse((next, idx)));
            }
        }
        refine(&codes, &mut shard, &second);
        assert_eq!(merged, tally.orbits);
        drop(readers);
        fs::remove_dir_all(scratch).unwrap();
    }
    shard.histogram.retain(|_, count| *count != 0);
    shard.nonrotation.sort_unstable();
    assert_eq!(
        shard
            .histogram
            .iter()
            .map(|(&size, &count)| size as u64 * count)
            .sum::<u64>(),
        predicted
    );
    shard.seconds = start.elapsed().as_secs_f64();
    shard
}

pub fn aggregate(area: usize, shards: &[Shard], seconds: f64, threads: usize) -> Area {
    let mut out = Area {
        format: FORMAT.into(),
        area,
        profiles: 0,
        rotation_orbits: 0,
        fixed: 0,
        classes: 0,
        histogram: BTreeMap::new(),
        nonrotation_classes: 0,
        nonrotation_members: 0,
        nonrotation: Vec::new(),
        first_collision_groups: 0,
        second_evaluations: 0,
        exact_groups: 0,
        exact_profiles: 0,
        exact_false_merges_split: 0,
        first_false_merges_split: 0,
        spilled_records: 0,
        seconds,
        shard_seconds: 0.,
        peak_rss_kib: storage::peak_kib(),
        threads,
        controls_passed: true,
    };
    for s in shards {
        assert_eq!(s.format, FORMAT);
        out.profiles += s.profiles;
        out.rotation_orbits += s.rotation_orbits;
        out.fixed += s.fixed;
        for (&k, &v) in &s.histogram {
            *out.histogram.entry(k).or_default() += v;
        }
        out.nonrotation.extend(s.nonrotation.clone());
        out.first_collision_groups += s.first_collision_groups;
        out.second_evaluations += s.second_evaluations;
        out.exact_groups += s.exact_groups;
        out.exact_profiles += s.exact_profiles;
        out.exact_false_merges_split += s.exact_false_merges_split;
        out.first_false_merges_split += s.first_false_merges_split;
        out.spilled_records += s.spilled_records;
        out.shard_seconds += s.seconds;
    }
    out.classes = out.histogram.values().sum();
    out.nonrotation.sort_unstable();
    out.nonrotation_classes = out.nonrotation.len();
    out.nonrotation_members = out.nonrotation.iter().map(Vec::len).sum();
    let (counts, fixed) = model::area_counts(area);
    assert_eq!(out.profiles, counts[area]);
    assert_eq!(out.fixed, fixed[area]);
    assert_eq!(out.rotation_orbits, (out.profiles + out.fixed) / 2);
    assert_eq!(
        out.histogram
            .iter()
            .map(|(&k, &v)| k as u64 * v)
            .sum::<u64>(),
        out.profiles
    );
    out
}
