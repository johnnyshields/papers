#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
export PYTHONDONTWRITEBYTECODE=1
python3 check_two_negative_endpoint_orders.py
python3 check_saturated_column.py
python3 check_threshold_budget.py
python3 check_threshold_identities.py
python3 check_threshold_recovery.py
python3 check_threshold_ties.py
python3 check_ten_negative_algebra.py
python3 check_ten_negative_endpoints.py
python3 check_ten_negative_contexts.py
python3 check_ten_negative_families.py
python3 check_six_negative_patterns.py
python3 check_two_negative_endpoints.py
python3 check_six_negative_classes.py
python3 check_boards.py
python3 check_negative_shape.py
python3 check_restoration_growth.py
python3 check_low_negatives.py
python3 check_four_family_minimum.py
python3 check_square.py
python3 check_five_cross.py
python3 check_five_within.py
python3 check_five_negative_algebra.py
python3 check_five_borders.py
python3 check_staircase.py
python3 check_staircase_borders.py
python3 check_endpoint_responses.py
python3 check_certificate_inventory.py
python3 check_negative_count_census.py
python3 check_opening_coefficient_contacts.py
python3 check_border_domain_boundaries.py
python3 check_five_prime_nondivisibility.py
python3 check_row_count_schur_invariant.py
python3 check_class_invariants.py
python3 check_ten_negative_seven_row_family.py
python3 check_six_row_nonrotation_families.py
python3 check_saturated_column_mate_space.py
python3 check_separated_support_rigidity.py
python3 check_ten_negative_full_mate_space.py
if [ "${FULL:-0}" = "1" ]; then
python3 check_staircase_certificate.py
python3 check_ten_negative_rigidity_sample.py
fi
echo "ALL PASS"
