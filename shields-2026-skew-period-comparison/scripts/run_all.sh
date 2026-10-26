#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 check_window_recognition.py
python3 check_primitive_profiles.py
python3 check_residue_arithmetic.py
python3 check_hook_transfer.py
printf 'ALL PASS\n'
