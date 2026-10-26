//! Charts, keys and the class-size clause on the census, in Rust.
//!
//! Commands:
//!   dump --max M                 every connected profile of 2..M cells with its legal marks (as an
//!                                inner) and its search-B charts, as JSON lines, for
//!                                `cross_check_python.py`
//!   validate --max M             forward generation through M, and on EVERY connected profile of
//!                                2..M cells, search B == search S == forward generation
//!   run --min A --max B          forward generation through B; the class-size clause on every
//!                                diagram of at most B cells with a proper chart; and on every
//!                                member of every nonrotation class of A..B cells: both searches
//!                                against the generation, chart validity, rotation, keys,
//!                                presentations, factor reversals and the class-size clause
//! Options: --threads T (default 4), --census DIR (census area files), --out DIR, --no-s.

mod analysis;
mod compose;
mod diagram;
mod expected;
mod generate;
mod marks;
mod poly;

use analysis::*;
use compose::*;
use diagram::*;
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use serde_json::json;
use std::{env, fs, path::PathBuf, sync::Mutex, time::Instant};

fn arg(args: &[String], key: &str, default: &str) -> String {
    args.iter()
        .position(|v| v == key)
        .map(|i| args.get(i + 1).expect("missing option value").clone())
        .unwrap_or(default.into())
}

fn cells_json(s: &[Cell]) -> serde_json::Value {
    json!(s.iter().map(|&(i, j)| [i, j]).collect::<Vec<_>>())
}

fn mark_json(m: &marks::Mark) -> serde_json::Value {
    json!({"b": cells_json(&m.b), "t": cells_json(&m.t), "case": (m.case as char).to_string(),
           "v": [m.v.0, m.v.1], "q": m.q})
}

fn atomic_write(path: &PathBuf, v: &serde_json::Value) {
    let tmp = path.with_extension("tmp");
    fs::write(&tmp, serde_json::to_vec_pretty(v).unwrap()).unwrap();
    fs::rename(&tmp, path).unwrap();
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let command = args.get(1).map(String::as_str).unwrap_or("");
    let threads: usize = arg(&args, "--threads", "4").parse().unwrap();
    assert!((1..=16).contains(&threads));
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    let max: usize = arg(&args, "--max", "12").parse().unwrap();
    assert!((2..=40).contains(&max));
    match command {
        "dump" => dump(max),
        "validate" => validate(max),
        "run" => run(&args, max),
        _ => panic!("commands: dump, validate, run"),
    }
}

fn dump(max: usize) {
    for a in 2..=max {
        for f in generate::connected_of_area(a) {
            let ms: Vec<_> = marks::marks(&f).iter().map(mark_json).collect();
            let cs: Vec<_> = finder_band(&f)
                .iter()
                .map(|c| json!({"d": cells_json(&c.d), "e": cells_json(&c.e), "mark": mark_json(&c.m)}))
                .collect();
            let p = profile_of(&f);
            println!("{}", json!({"profile": [p.0, p.1], "marks": ms, "band": cs}));
        }
    }
}

fn validate(max: usize) {
    let t = Instant::now();
    let atlas = generate::generate(max);
    println!(
        "generation through {max}: {} diagrams with a chart, {} marked inners, {} compositions, {} non-skew ({:.1}s)",
        atlas.charts.len(), atlas.inners.len(), atlas.compositions, atlas.non_skew, t.elapsed().as_secs_f64()
    );
    for a in 2..=max {
        let fs_ = generate::connected_of_area(a);
        let rooted: usize = fs_
            .par_iter()
            .map(|f| {
                let g = atlas.charts_of(f);
                let b = finder_band(f);
                let s = finder_subdiagram(f);
                assert!(b == g && s == g, "searches disagree on {:?}", profile_of(f));
                for c in &g {
                    chart_ok(f, c).unwrap();
                }
                !g.is_empty() as usize
            })
            .sum();
        println!("PASS area {a}: {} profiles, {rooted} with a chart; search B == search S == generation", fs_.len());
    }
    println!("ALL PASS ({:.1}s)", t.elapsed().as_secs_f64());
}

fn run(args: &[String], max: usize) {
    let t0 = Instant::now();
    let min: usize = arg(args, "--min", "8").parse().unwrap();
    let census = PathBuf::from(arg(args, "--census", concat!(env!("CARGO_MANIFEST_DIR"), "/../census-rs/results")));
    let out = PathBuf::from(arg(args, "--out", concat!(env!("CARGO_MANIFEST_DIR"), "/results")));
    let run_s = !args.iter().any(|a| a == "--no-s");
    fs::create_dir_all(&out).unwrap();
    let classes = Classes::load(&census, max);

    // ---------------------------------------------------------------- forward generation
    let t = Instant::now();
    let atlas = generate::generate(max);
    let gen_seconds = t.elapsed().as_secs_f64();
    let mut with_chart = vec![0u64; max + 1];
    for k in atlas.charts.keys() {
        with_chart[profile_from_key(k).0.iter().map(|&r| r as usize).sum::<usize>()] += 1;
    }
    for &(n, c) in expected::WITH_CHART {
        if n <= max {
            assert_eq!(with_chart[n], c, "diagrams with a chart at area {n} differ from the Python size check");
        }
    }
    if max >= 24 {
        assert_eq!(with_chart[..=24].iter().sum::<u64>(), expected::WITH_CHART_THROUGH_24);
    }
    println!(
        "PASS generation through {max}: {} diagrams with a chart, {} marked inners, {} compositions, {} non-skew ({gen_seconds:.1}s)",
        atlas.charts.len(), atlas.inners.len(), atlas.compositions, atlas.non_skew
    );

    // ---------------------------------------------------------------- class size, every diagram
    let t = Instant::now();
    let size_rows = size_check_all(&atlas, &classes);
    let size_seconds = t.elapsed().as_secs_f64();
    for r in &size_rows {
        assert_eq!(r.diagrams_with_chart, with_chart[r.area]);
        println!(
            "PASS size clause, area {}: {} diagrams with a chart, {} irreducible factorizations, longest {}",
            r.area, r.diagrams_with_chart, r.factorizations, r.longest
        );
    }
    println!(
        "PASS (size, all diagrams): every connected diagram of at most {max} cells with a proper chart satisfies |[F]| = 2^r for every irreducible factorization, and the reversal variants of each are exactly its class ({size_seconds:.1}s)"
    );
    let summary = json!({
        "max": max,
        "with_chart": with_chart,
        "with_chart_total": with_chart.iter().sum::<u64>(),
        "marked_inners": atlas.inners.len(),
        "compositions": atlas.compositions,
        "non_skew": atlas.non_skew,
        "generation_seconds": gen_seconds,
        "size_seconds": size_seconds,
        "threads": threads(),
        "size_rows": size_rows.iter().map(|r| json!({"area": r.area, "with_chart": r.diagrams_with_chart,
            "irreducible_factorizations": r.factorizations, "longest": r.longest,
            "variants_composed": r.variants_composed})).collect::<Vec<_>>(),
    });
    atomic_write(&out.join(format!("size-through-{max:02}.json")), &summary);

    // ---------------------------------------------------------------- members of nonrotation classes
    let me = Mutex::new(Interner::default());
    let (mut total_corrupt, mut total_arbitrary) = (0u64, 0u64);
    for n in min..=max {
        let cls = &classes.by_area[n];
        if cls.is_empty() {
            continue;
        }
        let t = Instant::now();
        let mem: Vec<&Box<[u8]>> = cls.iter().flatten().collect();
        let data: Vec<MemberData> = mem.par_iter().map(|k| member(&atlas, &me, k, run_s)).collect();
        let by: FxHashMap<&[u8], &MemberData> = data.iter().map(|d| (&*d.key, d)).collect();
        let charts_seconds = t.elapsed().as_secs_f64();

        // Rotation: every chart rotates to a chart of the rotation.
        for d in &data {
            let r = key_of(&rot_profile(&profile_from_key(&d.key)));
            let dr = by[&*r];
            assert_eq!(d.charts.len(), dr.charts.len());
            let set: FxHashSet<&Chart> = dr.charts.iter().collect();
            for c in &d.charts {
                let (er, mr) = marks::rotate_mark(&c.e, &c.m);
                assert!(set.contains(&Chart { d: rotate(&c.d), e: er, m: mr }), "a chart does not rotate");
            }
        }

        // Roots table.
        let mut dist = [0u64; 5];
        let mut cases = FxHashMap::default();
        for d in &data {
            dist[d.charts.len().min(4)] += 1;
            for c in &d.charts {
                *cases.entry(c.m.case).or_insert(0u64) += 1;
            }
        }
        let max_d = data.iter().flat_map(|d| d.charts.iter().map(|c| c.d.len())).max().unwrap() as u64;
        let nchart: u64 = data.iter().map(|d| d.charts.len() as u64).sum();
        let roots_row = [
            cls.len() as u64, data.len() as u64, data.len() as u64, nchart, dist[1], dist[2], dist[3], dist[4], max_d,
            *cases.get(&b'a').unwrap_or(&0), *cases.get(&b'b').unwrap_or(&0),
            *cases.get(&b'c').unwrap_or(&0), *cases.get(&b'd').unwrap_or(&0),
        ];
        if let Some(e) = expected::ROOTS.iter().find(|e| e.0 == n) {
            assert_eq!(roots_row, e.1, "roots table row {n} differs from the Python");
        }

        // Keys.
        let (mut corrupt_splits, mut arbitrary_splits, mut multi) = (0u64, 0u64, 0u64);
        let mut smdist: FxHashMap<i16, u64> = FxHashMap::default();
        for cl in cls {
            let ds: Vec<&MemberData> = cl.iter().map(|k| by[&**k]).collect();
            assert!(ds.iter().all(|d| d.keys == ds[0].keys), "two key sets in one class");
            assert!(ds.iter().all(|d| d.smp == ds[0].smp));
            *smdist.entry(ds[0].smp).or_insert(0) += 1;
            for d in &ds {
                assert_eq!(d.gkeys.len(), 1, "more than one key modulo the gauge");
                multi += (d.periods.len() >= 2) as u64;
            }
            let mut c: FxHashSet<&Vec<Key>> = ds[1..].iter().map(|d| &d.keys).collect();
            c.insert(&ds[0].corrupt);
            corrupt_splits += (c.len() > 1) as u64;
            let a: FxHashSet<&Vec<Key>> = ds.iter().map(|d| &d.allkeys).collect();
            arbitrary_splits += (a.len() > 1) as u64;
        }
        total_corrupt += corrupt_splits;
        total_arbitrary += arbitrary_splits;
        let mut smv: Vec<(i16, u64)> = smdist.into_iter().collect();
        smv.sort();
        if let Some(e) = expected::KEYS.iter().find(|e| e.0 == n) {
            assert_eq!((cls.len() as u64, multi, smv.as_slice()), (e.1, e.2, e.3), "keys table row {n} differs");
        }

        // Presentations of every ordered pair.
        let pairs: Vec<(&Box<[u8]>, &Box<[u8]>)> =
            cls.iter().flat_map(|cl| cl.iter().flat_map(move |x| cl.iter().map(move |y| (x, y)))).collect();
        let lens: Vec<usize> = pairs
            .par_iter()
            .map(|(x, y)| {
                let (dx, dy) = (by[&***x], by[&***y]);
                let (px, py) = common_presentation(&atlas, &me, &dx.cells, &dy.cells);
                assert_eq!(realize_pres(&px), dx.cells);
                assert_eq!(realize_pres(&py), dy.cells);
                assert_eq!(px.len(), py.len());
                assert!(px.iter().zip(&py).all(|(a, b)| same_or_rotated(a, b)));
                px.len()
            })
            .collect();
        let mut lendist: FxHashMap<usize, u64> = FxHashMap::default();
        for l in &lens {
            *lendist.entry(*l).or_insert(0) += 1;
        }
        let one_factor = lendist.get(&1).copied().unwrap_or(0);

        // Every factor reversal of every chart stays in the class.
        let reversals: u64 = data
            .par_iter()
            .map(|d| {
                let cl: FxHashSet<Box<[u8]>> = classes.class_of(&d.key).into_iter().collect();
                let mut n = 0;
                for c in &d.charts {
                    let (er, mr) = marks::rotate_mark(&c.e, &c.m);
                    for r in [compose(&rotate(&c.d), &c.e, &c.m), compose(&c.d, &er, &mr), compose(&rotate(&c.d), &er, &mr)] {
                        assert!(cl.contains(&key_of(&profile_of(&r))), "a factor reversal leaves the class");
                        n += 1;
                    }
                }
                n
            })
            .sum();

        // Class size on the members, with the published table row.
        let empty = FxHashMap::default();
        let facts: FxHashMap<&[u8], (u64, usize)> = data
            .par_iter()
            .map(|d| {
                let fs_ = irreducible(&atlas, &d.cells, &empty);
                (&*d.key, (fs_.len() as u64, fs_.iter().map(|f| f.steps.len() + 1).max().unwrap()))
            })
            .collect();
        let (mut nf, mut c4, mut c8, mut longest) = (0u64, 0u64, 0u64, 0usize);
        for cl in cls {
            c4 += (cl.len() == 4) as u64;
            c8 += (cl.len() == 8) as u64;
            for k in cl {
                nf += facts[&**k].0;
                longest = longest.max(facts[&**k].1);
            }
        }
        let conj_row = [data.len() as u64, nf, c4, c8, longest as u64];
        if let Some(e) = expected::CONJ.iter().find(|e| e.0 == n) {
            assert_eq!(conj_row, e.1, "conjecture table row {n} differs");
        }
        let band_s: f64 = data.iter().map(|d| d.band_seconds).sum();
        let sub_s: f64 = data.iter().map(|d| d.sub_seconds).sum();
        let mut lv: Vec<(usize, u64)> = lendist.into_iter().collect();
        lv.sort();
        let row = json!({
            "area": n, "classes": cls.len(), "members": data.len(), "rooted": data.len(),
            "charts": nchart, "members_by_charts": {"1": dist[1], "2": dist[2], "3": dist[3], "4+": dist[4]},
            "largest_outer": max_d,
            "charts_by_case": {"a": roots_row[9], "b": roots_row[10], "c": roots_row[11], "d": roots_row[12]},
            "members_with_two_or_more_periods": multi,
            "minimal_period_classes": smv.iter().map(|(p, c)| json!([p, c])).collect::<Vec<_>>(),
            "corrupted_key_classes_split": corrupt_splits,
            "all_chart_key_classes_split": arbitrary_splits,
            "ordered_pairs": pairs.len(), "one_factor_pairs": one_factor,
            "presentation_lengths": lv.iter().map(|(l, c)| json!([l, c])).collect::<Vec<_>>(),
            "factor_reversals": reversals,
            "irreducible_factorizations": nf, "classes_of_size_4": c4, "classes_of_size_8": c8,
            "longest_factorization": longest,
            "search_s_on_every_member": run_s,
            "band_seconds": band_s, "subdiagram_seconds": sub_s,
            "seconds": t.elapsed().as_secs_f64(), "chart_seconds": charts_seconds, "threads": threads(),
        });
        atomic_write(&out.join(format!("members-{n:02}.json")), &row);
        println!(
            "PASS members N={n}: {} classes, {} members, {} charts (1/2/3/4+: {}/{}/{}/{}), largest outer {}, cases a/b/c/d {}/{}/{}/{}; B == S == generation; keys agree; {} pairs presented; {} reversals; {} irreducible factorizations, longest {}; transposed-outer control splits {}, all-chart keys split {} ({:.1}s)",
            cls.len(), data.len(), nchart, dist[1], dist[2], dist[3], dist[4], max_d,
            roots_row[9], roots_row[10], roots_row[11], roots_row[12], pairs.len(), reversals, nf, longest,
            corrupt_splits, arbitrary_splits, t.elapsed().as_secs_f64()
        );
    }
    assert!(total_corrupt > 0, "the transposed-outer control never splits a class");
    if min <= 8 && max >= 26 {
        println!("controls through {max}: transposed outer splits {total_corrupt} classes, all-chart keys split {total_arbitrary}");
    }
    if min <= 8 && max == 26 {
        assert_eq!((total_corrupt, total_arbitrary), expected::CONTROLS_THROUGH_26);
    }
    println!("ALL PASS ({:.1}s)", t0.elapsed().as_secs_f64());
}

fn threads() -> usize {
    rayon::current_num_threads()
}
