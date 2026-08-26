#!/usr/bin/env bash
set -euo pipefail
python3 verify_beta_binomial.py
python3 verify_monotonicity_lemmas.py
python3 verify_kernel.py
python3 verify_theorem.py
python3 verify_multiplicity.py
python3 check_fixed_sum_schur.py
python3 check_beta_moment_fold.py
python3 check_kernel_stdlib.py
python3 check_r4_obstruction.py
python3 check_proof_steps.py
python3 check_structural.py
python3 check_differential_domination.py
python3 check_differential_coefficients.py
python3 make_figure_multiplicity.py
python3 render_figures.py
python3 check_mutation_bite.py
