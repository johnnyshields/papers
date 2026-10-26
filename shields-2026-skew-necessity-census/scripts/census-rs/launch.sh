#!/usr/bin/env bash
set -euo pipefail
# Use under an outer timeout. The detached computation has its own hard deadline.
WORK=${WORK:-/mnt/d/mvw-rust}
SCRATCH=${SCRATCH:-/home/shields/r167-lanes/_rust35}
MAX=${MAX:-26}
MIN=${MIN:-1}
THREADS=${THREADS:-16}
DURATION=${DURATION:-172800}
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
export TMPDIR="$SCRATCH/tmp"
mkdir -p "$SCRATCH/hot" "$SCRATCH/logs" "$TMPDIR"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
nohup timeout "$DURATION" nice -n 10 prlimit --as=24000000000 -- \
  python3 "$HERE/run_logged.py" --log "$WORK/logs/census-${MIN}-${MAX}.log" \
  --hot-log "$SCRATCH/logs/census-${MIN}-${MAX}.log" -- \
  /usr/bin/time -v "$SCRATCH/target/release/skew-census" census \
  --min "$MIN" --max "$MAX" --work "$WORK" --scratch "$SCRATCH/hot" --threads "$THREADS" \
  > "$SCRATCH/logs/launcher-${MIN}-${MAX}.log" 2>&1 < /dev/null &
echo "PID=$! LOG=$WORK/logs/census-${MIN}-${MAX}.log"
