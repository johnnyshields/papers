#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
python3 verify_power_sum_action.py
python3 verify_weighted_action.py
python3 verify_extraction.py
python3 verify_mixed_extraction.py
python3 verify_transport.py
python3 verify_examples.py
python3 check_hatted_mark.py
python3 check_primitive_monomial.py
python3 check_readout_flint.py
python3 check_decoder_modes.py
python3 check_hopf_action.py 6 3
python3 check_thesis_marks.py 9
printf '%s\n' 'ALL PASS'
