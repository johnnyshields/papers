use serde::Serialize;
use std::sync::{Condvar, Mutex};
use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::Path,
    thread,
    time::Duration,
};

pub fn retry<T>(mut action: impl FnMut() -> io::Result<T>) -> io::Result<T> {
    let mut last = None;
    for attempt in 0..9 {
        match action() {
            Ok(result) => return Ok(result),
            Err(err) => {
                eprintln!("I/O retry {attempt}: {err}");
                last = Some(err);
                thread::sleep(Duration::from_secs((1u64 << attempt).min(30)));
            }
        }
    }
    Err(last.unwrap())
}

pub fn atomic_json(path: &Path, value: &impl Serialize) {
    let bytes = serde_json::to_vec(value).unwrap();
    atomic_bytes(path, &bytes);
}

pub fn atomic_bytes(path: &Path, bytes: &[u8]) {
    let tmp = path.with_extension("json.tmp");
    retry(|| {
        fs::create_dir_all(path.parent().unwrap())?;
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&tmp)?;
        file.write_all(bytes)?;
        file.sync_all()?;
        fs::rename(&tmp, path)?;
        // File fsync is mandatory. Some mounted filesystems do not support directory fsync.
        if let Ok(dir) = File::open(path.parent().unwrap()) {
            let _ = dir.sync_all();
        }
        Ok(())
    })
    .unwrap();
}

pub fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> T {
    let bytes = retry(|| fs::read(path)).unwrap();
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

pub struct DiskBudget {
    pub limit: u64,
    usage: Mutex<(u64, u64)>,
    changed: Condvar,
}

pub struct DiskPermit<'a> {
    budget: &'a DiskBudget,
    bytes: u64,
}

impl DiskBudget {
    pub fn new(limit: u64) -> Self {
        Self {
            limit,
            usage: Mutex::new((0, 0)),
            changed: Condvar::new(),
        }
    }
    pub fn acquire(&self, bytes: u64) -> DiskPermit<'_> {
        assert!(bytes <= self.limit, "one shard exceeds the hot-disk budget");
        let mut usage = self.usage.lock().unwrap();
        while usage.0 + bytes > self.limit {
            usage = self.changed.wait(usage).unwrap();
        }
        usage.0 += bytes;
        usage.1 = usage.1.max(usage.0);
        DiskPermit {
            budget: self,
            bytes,
        }
    }
    pub fn peak(&self) -> u64 {
        self.usage.lock().unwrap().1
    }
}

impl Drop for DiskPermit<'_> {
    fn drop(&mut self) {
        let mut usage = self.budget.usage.lock().unwrap();
        usage.0 -= self.bytes;
        self.budget.changed.notify_all();
    }
}

pub fn minimum_free_bytes() -> u64 {
    let gib: u64 = std::env::var("CENSUS_MIN_FREE_GIB")
        .unwrap_or_else(|_| "100".into())
        .parse()
        .unwrap();
    assert!(gib <= 1024);
    gib << 30
}

pub fn wait_for_hot_space(path: &Path) {
    // At the maximum CLI buffer size all 16 simultaneous writes total < 8 GiB.
    // The shared-machine default keeps 100 GiB free plus a 20-GiB write margin.
    let floor = minimum_free_bytes();
    if floor == 0 {
        return;
    }
    let threshold = floor + (20u64 << 30);
    loop {
        let free = available_bytes(path);
        if free >= threshold {
            return;
        }
        eprintln!(
            "WAIT hot-disk reserve: {} has {free} bytes free; need {threshold}",
            path.display()
        );
        thread::sleep(Duration::from_secs(30));
    }
}

pub fn available_bytes(path: &Path) -> u64 {
    let output = std::process::Command::new("timeout")
        .args(["10s", "df", "-B1", "--output=avail"])
        .arg(path)
        .output()
        .unwrap();
    assert!(output.status.success(), "cannot size available hot storage");
    String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .last()
        .unwrap()
        .parse()
        .unwrap()
}

#[cfg(test)]
mod tests {
    #[test]
    fn disk_reservations_wait_and_release() {
        use std::{sync::mpsc, time::Duration};
        let budget = super::DiskBudget::new(10);
        let first = budget.acquire(7);
        std::thread::scope(|scope| {
            let (ready_tx, ready_rx) = mpsc::channel();
            let (done_tx, done_rx) = mpsc::channel();
            let budget_ref = &budget;
            scope.spawn(move || {
                ready_tx.send(()).unwrap();
                let _second = budget_ref.acquire(6);
                done_tx.send(()).unwrap();
            });
            ready_rx.recv_timeout(Duration::from_secs(5)).unwrap();
            assert!(done_rx.recv_timeout(Duration::from_millis(20)).is_err());
            drop(first);
            done_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        });
        assert!(budget.peak() <= 10);
        assert_eq!(budget.usage.lock().unwrap().0, 0);
    }
}

pub fn peak_kib() -> u64 {
    fs::read_to_string("/proc/self/status")
        .unwrap()
        .lines()
        .find(|line| line.starts_with("VmHWM:"))
        .and_then(|line| line.split_whitespace().nth(1))
        .unwrap()
        .parse()
        .unwrap()
}
