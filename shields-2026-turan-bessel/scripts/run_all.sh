#!/usr/bin/env bash
set -euo pipefail
python3 verify_convolution_coefficients.py
python3 verify_finite_law.py
python3 verify_gram.py
python3 verify_determinant.py
python3 make_figure_det_m1.py
python3 verify_degree_one_threshold.py
python3 verify_bessel_reduction.py
python3 verify_cauchy_mu_center.py
python3 verify_first_negative_degree.py
python3 verify_continuation.py
python3 verify_context.py
python3 check_coefficients_stdlib.py
python3 verify_dlmf_locators.py
