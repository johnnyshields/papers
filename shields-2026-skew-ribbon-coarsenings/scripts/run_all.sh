#!/usr/bin/env bash
set -euo pipefail
python3 verify_algebra.py
python3 verify_balance.py
python3 verify_detector.py
python3 verify_realization.py
python3 verify_recognition.py
python3 verify_depth.py
python3 verify_recovery.py
python3 verify_multilevel.py
echo "ALL PASS"
