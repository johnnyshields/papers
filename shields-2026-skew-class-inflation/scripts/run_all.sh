#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
python3 check_ref1_class_inflation_exact.py
python3 check_seam_coefficient_order.py
python3 check_hessenberg_membership.py
python3 check_two_residue_decoder.py
python3 check_cut_coefficient_lowering.py
python3 check_chart_inflation.py
python3 check_repeated_block_saturation.py
python3 check_inflation_collapse_threshold.py
python3 check_inflation_all_t.py
python3 check_expansions_substitutions_and_rigidity.py
python3 check_proof_step_equations.py
python3 check_marked_boundary_words.py
python3 check_paper_crossrefs.py
printf 'ALL PASS\n'
