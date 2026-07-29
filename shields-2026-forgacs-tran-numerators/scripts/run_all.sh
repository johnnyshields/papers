#!/usr/bin/env bash
set -euo pipefail
python3 verify_reduction.py
python3 verify_geometry.py
python3 verify_interval_structure.py
python3 verify_dominance.py
python3 verify_proof.py
python3 verify_equidistribution.py
python3 check_recurrence_stdlib.py
python3 make_figure_pole_geom.py
