#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
WORK=${WORK:-/mnt/d/mvw-rust}
SCRATCH=${SCRATCH:-/home/shields/r167-lanes/_rust35}
THREADS=${THREADS:-16}
PYTHON_WORK=${PYTHON_WORK:-/home/shields/r167-lanes/_basepaper/full}
FULL=${FULL:-0}
if [[ $THREADS -lt 1 || $THREADS -gt 16 ]]; then echo 'THREADS must be 1..16' >&2; exit 2; fi
export CARGO_TARGET_DIR="$SCRATCH/target" CARGO_BUILD_JOBS="$THREADS" TMPDIR="$SCRATCH/tmp"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p "$SCRATCH/hot" "$SCRATCH/logs" "$TMPDIR"
run() { timeout "${DURATION:-172800}" nice -n 10 prlimit --as=24000000000 -- "$@"; }
run cargo test --release --manifest-path "$HERE/Cargo.toml"
run cargo build --release --manifest-path "$HERE/Cargo.toml"
if [[ $FULL == 1 ]]; then
  completed=1
  for file in "$HERE"/results/area-??.json; do
    name=${file##*/}; n=${name#area-}; n=${n%.json}; completed=$((10#$n))
  done
  MAX=${MAX:-$completed}
else
  MAX=${MAX:-20}
fi
base=$MAX
if [[ $base -gt 26 ]]; then base=26; fi
run python3 "$HERE/run_logged.py" --log "$WORK/logs/run-through-${base}.log" \
  --hot-log "$SCRATCH/logs/run-through-${base}.log" -- \
  /usr/bin/time -v "$CARGO_TARGET_DIR/release/skew-census" census --max "$base" \
  --work "$WORK" --scratch "$SCRATCH/hot" --threads "$THREADS" --summary "$HERE/results"
if [[ $MAX -gt 26 ]]; then
  run python3 "$HERE/cross_check.py" --work "$WORK" --python-work "$PYTHON_WORK" --through 26
  run python3 "$HERE/run_logged.py" --log "$WORK/logs/run-27-${MAX}.log" \
    --hot-log "$SCRATCH/logs/run-27-${MAX}.log" -- \
    /usr/bin/time -v "$CARGO_TARGET_DIR/release/skew-census" census --min 27 --max "$MAX" \
    --work "$WORK" --scratch "$SCRATCH/hot" --threads "$THREADS" --summary "$HERE/results"
  run python3 "$HERE/run_logged.py" --log "$WORK/logs/roots-27-${MAX}.log" \
    --hot-log "$SCRATCH/logs/roots-27-${MAX}.log" -- \
    python3 "$HERE/roots_keys.py" --min 27 --max "$MAX" --jobs "$THREADS" --work "$WORK" --band-only
fi
run python3 "$HERE/summarize.py" --work "$WORK"
run python3 "$HERE/summarize.py" --work "$WORK" --check
echo 'ALL PASS'
