#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1
export NUMEXPR_NUM_THREADS=1
python3 verify_coframe_coordinates.py
python3 verify_fixed_caps.py
python3 verify_fixed_cap_census.py
python3 verify_unit_restoration.py
python3 verify_linearized_and_grades.py
python3 verify_linearized_observations.py
python3 verify_linearized_cap_steps.py
python3 verify_block_cramer_quotient.py
python3 verify_stationary.py
python3 verify_positive_power_steps.py
python3 verify_unshifted.py
python3 verify_unshifted_all_p.py
python3 verify_proof_identities.py
python3 check_paper_crossrefs.py
printf '%s\n' 'ALL PASS'
