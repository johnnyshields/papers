#!/usr/bin/env bash
set -euo pipefail
python3 verify_convolution_coefficients.py
python3 verify_conditional_hessian.py
python3 verify_gram.py
python3 verify_determinant.py
python3 verify_bessel_reduction.py
python3 verify_context.py
python3 check_coefficients_stdlib.py
