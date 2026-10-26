mod algebra;
mod census;
mod controls;
mod model;
mod storage;

use rayon::prelude::*;
use std::{
    env, fs,
    path::PathBuf,
    sync::{
        Mutex,
        atomic::{AtomicUsize, Ordering},
    },
    time::Instant,
};

fn arg(args: &[String], key: &str, default: &str) -> String {
    args.iter()
        .position(|v| v == key)
        .map(|i| args.get(i + 1).expect("missing option value").clone())
        .unwrap_or(default.into())
}
fn main() {
    let args: Vec<String> = env::args().collect();
    let command = args.get(1).map(String::as_str).unwrap_or("census");
    let work = PathBuf::from(arg(&args, "--work", "/mnt/d/mvw-rust"));
    let scratch = PathBuf::from(arg(
        &args,
        "--scratch",
        "/home/shields/r167-lanes/_rust35/hot",
    ));
    let summary = PathBuf::from(arg(
        &args,
        "--summary",
        concat!(env!("CARGO_MANIFEST_DIR"), "/results"),
    ));
    let threads: usize = arg(&args, "--threads", "16").parse().unwrap();
    let max: usize = arg(&args, "--max", "20").parse().unwrap();
    let min: usize = arg(&args, "--min", "1").parse().unwrap();
    let cap: usize = arg(&args, "--records", "16000000").parse().unwrap();
    let spill_gib: u64 = arg(&args, "--spill-gib", "384").parse().unwrap();
    assert!((1..=512).contains(&spill_gib));
    assert!((1..=16).contains(&threads));
    assert!(min >= 1 && min <= max && max <= model::MAX);
    assert!((1..=32_000_000).contains(&cap));
    fs::create_dir_all(&scratch).unwrap();
    rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build_global()
        .unwrap();
    if command == "scale" {
        let (counts, fixed) = model::area_counts(max);
        let mut rows = Vec::new();
        for n in min..=max {
            let parts = model::partitions(n as u8);
            let sized: Vec<_> = parts
                .par_iter()
                .map(|p| (model::shard_count(p), p.clone()))
                .collect();
            let total: u64 = sized.iter().map(|p| p.0).sum();
            assert_eq!(total, counts[n]);
            let largest = sized.iter().max_by_key(|p| p.0).unwrap();
            let row = serde_json::json!({"area":n,"profiles":total,"rotation_orbits":(total+fixed[n])/2,
                "row_multisets":parts.len(),"largest_profiles":largest.0,"largest_parts":largest.1});
            println!("{row}");
            rows.push(row);
        }
        storage::atomic_json(&work.join("scale.json"), &rows);
        storage::atomic_json(&summary.join("scale.json"), &rows);
        return;
    }
    controls::run(&scratch);
    if command == "controls" {
        return;
    }
    assert_eq!(command, "census", "commands: census, scale, controls");
    if max > 26 {
        let gate: serde_json::Value = storage::read_json(&work.join("cross-check.json"));
        assert_eq!(
            gate["passed"], true,
            "the independent Python gate must pass before area 27"
        );
        assert!(gate["through"].as_u64().unwrap() >= 26);
    }
    for n in min..=max {
        let area_file = work.join(format!("area-{n:02}.json"));
        if area_file.exists() {
            let result: census::Area = storage::read_json(&area_file);
            assert_eq!(result.format, census::FORMAT);
            assert_eq!(result.area, n);
            let original = storage::retry(|| fs::read(&area_file)).unwrap();
            storage::atomic_bytes(&summary.join(format!("area-{n:02}.json")), &original);
            print_row(&result, "resumed");
            continue;
        }
        let start = Instant::now();
        let parts = model::partitions(n as u8);
        let mut jobs: Vec<_> = parts
            .par_iter()
            .map(|p| (p.clone(), model::shard_count(p)))
            .collect();
        jobs.sort_unstable_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        let total: u64 = jobs.iter().map(|p| p.1).sum();
        let largest = jobs[0].1;
        let free_disk = storage::available_bytes(&scratch);
        let floor = storage::minimum_free_bytes();
        let reserve = if floor == 0 { 0 } else { floor + (28u64 << 30) };
        let disk_budget = storage::DiskBudget::new(
            (spill_gib << 30)
                .min(free_disk / 4 * 3)
                .min(free_disk.saturating_sub(reserve)),
        );
        let (_, fixed_counts) = model::area_counts(n);
        let fixed_upper = fixed_counts[n];
        println!(
            "DISK N={n} free_bytes={free_disk} reserved_payload_limit={}",
            disk_budget.limit
        );
        println!(
            "SIZE N={n} profiles={total} shards={} largest={largest} record_cap={cap} threads={threads}",
            jobs.len()
        );
        let checkpoint = work.join(format!("checkpoints/area-{n:02}"));
        storage::retry(|| fs::create_dir_all(&checkpoint)).unwrap();
        let completed = AtomicUsize::new(0);
        let next_job = AtomicUsize::new(0);
        let last_message = Mutex::new(Instant::now());
        // Dynamic largest-first assignment avoids a contiguous parallel slice
        // leaving one worker with most of the expensive initial shards.
        let shards: Vec<_> = (0..threads)
            .into_par_iter()
            .flat_map_iter(|_| {
                let mut local = Vec::new();
                loop {
                    let index = next_job.fetch_add(1, Ordering::Relaxed);
                    let Some((p, predicted)) = jobs.get(index) else {
                        break;
                    };
                    let key = p.iter().map(u8::to_string).collect::<Vec<_>>().join("-");
                    let path = checkpoint.join(format!("{key}.json"));
                    let shard: census::Shard = if path.exists() {
                        let s: census::Shard = storage::read_json(&path);
                        assert_eq!(s.format, census::FORMAT);
                        assert_eq!(s.parts, *p);
                        assert_eq!(s.profiles, *predicted);
                        s
                    } else {
                        let hot = scratch.join(format!("area-{n:02}/{key}"));
                        if hot.exists() {
                            fs::remove_dir_all(&hot).unwrap();
                        }
                        let orbit_upper = (*predicted + (*predicted).min(fixed_upper)) / 2;
                        let payload = if orbit_upper >= cap as u64 {
                            16 * orbit_upper
                        } else {
                            0
                        };
                        let _disk_permit = disk_budget.acquire(payload);
                        let s = census::compute_shard(p, *predicted, &hot, cap);
                        storage::atomic_json(&path, &s);
                        s
                    };
                    let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
                    let mut last = last_message.lock().unwrap();
                    if last.elapsed().as_secs() >= 30 || done == jobs.len() {
                        println!(
                            "PROGRESS N={n} {done}/{} shards {:.1}s peak={}KiB",
                            jobs.len(),
                            start.elapsed().as_secs_f64(),
                            storage::peak_kib()
                        );
                        *last = Instant::now();
                    }
                    local.push(shard);
                }
                local
            })
            .collect();
        assert_eq!(shards.len(), jobs.len());
        let got: std::collections::BTreeSet<_> = shards.iter().map(|s| &s.parts).collect();
        let expected: std::collections::BTreeSet<_> = jobs.iter().map(|(p, _)| p).collect();
        assert_eq!(got, expected, "shard partition is incomplete or duplicated");
        let result = census::aggregate(n, &shards, start.elapsed().as_secs_f64(), threads);
        storage::atomic_json(&area_file, &result);
        storage::atomic_json(&summary.join(format!("area-{n:02}.json")), &result);
        let resources = serde_json::json!({"area":n,"spill_payload_limit_bytes":disk_budget.limit,
            "peak_reserved_payload_bytes":disk_budget.peak(),"initial_free_hot_bytes":free_disk,
            "records_per_buffer":cap,"threads":threads,"peak_rss_kib":result.peak_rss_kib,
            "minimum_free_hot_bytes":floor});
        storage::atomic_json(&work.join(format!("resources-{n:02}.json")), &resources);
        storage::atomic_json(&summary.join(format!("resources-{n:02}.json")), &resources);
        print_row(&result, "complete");
    }
}

fn print_row(result: &census::Area, status: &str) {
    println!(
        "TABLE {:2} profiles={} orbits={} classes={} histogram={:?} nonrotation={} members={} exact_groups={} exact_profiles={} false_merges={} seconds={:.3} peak_kib={} {status}",
        result.area,
        result.profiles,
        result.rotation_orbits,
        result.classes,
        result.histogram,
        result.nonrotation_classes,
        result.nonrotation_members,
        result.exact_groups,
        result.exact_profiles,
        result.exact_false_merges_split,
        result.seconds,
        result.peak_rss_kib
    );
}
