#!/usr/bin/env bash
set -euo pipefail
python3 verify_beta_binomial.py
python3 verify_monotonicity_lemmas.py
python3 verify_kernel.py
python3 verify_theorem.py
python3 verify_remarks.py
python3 check_kernel_stdlib.py
