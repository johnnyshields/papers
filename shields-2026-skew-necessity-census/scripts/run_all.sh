#!/usr/bin/env bash
# Quick run (default): the census through 16 cells and every check on it, in a few minutes.
# FULL=1: the census through 26 cells (several CPU-hours; set SKEWBASE_JOBS to the cores you can spare).
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
export SKEWBASE_WORK="${SKEWBASE_WORK:-$(pwd)/_work}"
export SKEWBASE_JOBS="${SKEWBASE_JOBS:-4}"
if [ "${FULL:-0}" = "1" ]; then
  NMAX=26; VMAX=12; BOX=full; CSMAX=22; POLY=11
else
  NMAX=16; VMAX=10; BOX=small; CSMAX=12; POLY=10
fi
python3 verify_enumeration.py --polymax "$POLY"
python3 verify_classes.py "$NMAX"
python3 check_mvw_examples.py
python3 verify_roots.py --vmax "$VMAX" --box "$BOX"
python3 verify_keys.py
python3 verify_conjecture.py --csmax "$CSMAX"
echo "ALL PASS"
