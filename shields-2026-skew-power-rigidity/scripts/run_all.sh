#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
python3 check_plan_egp_family_balanced.py
python3 check_hessenberg_membership.py
python3 verify_power_rigidity.py
python3 verify_class_exposure.py
python3 verify_balanced_wall.py
python3 verify_inflation.py
python3 check_r_wall_arbitrary_mate_refutation.py
echo "ALL PASS"
