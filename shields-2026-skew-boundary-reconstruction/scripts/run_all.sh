#!/usr/bin/env bash
# Runs the checks that guard the claims printed in the paper.
set -euo pipefail
cd "$(dirname "$0")"

python3 check_cofactor_factorization_and_reconstruction.py
python3 check_two_cap_exclusion_arithmetic.py
python3 check_kernel_relation_and_radix_weight.py
python3 check_elbow_cone_matches_the_square_gap.py
python3 check_passive_starvation_and_block_factorization.py
python3 check_radix_weight_is_admissible_and_injective.py
python3 check_ratio_locus_unbounded_support_family.py
python3 check_ribbon_reversal_freedom.py
python3 check_top_deletion_descent.py
python3 check_equal_pair_rigidity_unconditional.py
python3 check_equality_excludes_ratio_identities.py
python3 check_printed_statement_guards.py
python3 check_marching_saturation.py
python3 make_figures.py --check-only
python3 check_paper_crossrefs.py
python3 check_cofactor_scalar_reconstruction_support_and_backflow.py
python3 check_row_count_is_determined_by_the_skew_function.py
python3 check_ratio_identity_forces_equal_row_multisets.py
python3 check_monge_minor_sign_and_uncrossing_premise.py
python3 check_witnesses_independent.py
python3 check_general_weight_recovery.py
python3 check_abstract_reversal_identity.py
python3 check_locus_family_independent.py
python3 check_geometry_census.py
python3 check_reconstruction_census.py
python3 check_localization_census.py
python3 check_ratio_locus_census.py
python3 check_locus_family_census.py
python3 check_locus_family_all_k.py
python3 check_staircase_boundary_all_n.py
python3 check_scope_and_structural_census.py
python3 check_strict_monge_all_admissible_weights.py
python3 check_cap_fixed_random_admissible_weights.py
python3 check_two_cap_exclusion_on_formal_vectors.py

# Slow checks (minutes each, one core): FULL=1 ./run_all.sh
if [ "${FULL:-0}" = "1" ]; then
    python3 check_cap_fixed_adjacent_edge_guard.py
    python3 check_capfixed_tail_is_normalized.py
    python3 check_boundary_three_exclusion.py
    python3 check_specialization_bridge.py
fi

echo "ALL PASS"
