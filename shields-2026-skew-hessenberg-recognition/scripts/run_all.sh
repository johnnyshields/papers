#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python="${PYTHON:-python3}"
for script in \
  verify_hessenberg.py \
  verify_exposure.py \
  check_zero_cut_inventory.py \
  check_zero_free_exposure.py \
  check_separated_support.py \
  check_three_block_classes.py \
  check_three_block_generation.py \
  verify_recognition.py \
  verify_wall_criteria.py \
  check_four_row_wall.py \
  check_four_row_return.py \
  check_four_row_wall_cells.py \
  check_multiplicity_recognition.py \
  check_five_row_classification.py \
  check_constant_gap_boundary.py \
  check_five_row_powers.py \
  check_five_row_split.py \
  check_pattern_controls.py \
  check_nearest_prior.py \
  check_orientation_reduction.py \
  check_widening_controls.py \
  check_literal_charts.py \
  check_parity_pair_equality.py \
  check_parity_pair_determinant.py \
  check_reversal_towers.py
do
  printf '\n== %s ==\n' "$script"
  "$python" "$script"
done
printf '\nALL PASS\n'
