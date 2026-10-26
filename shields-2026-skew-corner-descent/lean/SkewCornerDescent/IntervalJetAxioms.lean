/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.NormalComparisonAxioms

/-!
# Full inverse and original interval-jet axiom guards

Guards the complete original coefficient, literal-root, intrinsic-order,
response-valuation and finite ordinary-gauge constructions.
-/

/-- info: 'SkewCornerDescent.Matrix.normal_inverse_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_inverse_coeff_one

/-- info: 'SkewCornerDescent.Matrix.normal_inverse_product_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_inverse_product_coeff_one

/-- info: 'SkewCornerDescent.Matrix.normal_series_deriv_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_series_deriv_inverse

/-- info: 'SkewCornerDescent.Matrix.normal_activity_amplitude_gradient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_activity_amplitude_gradient

/-- info: 'SkewCornerDescent.Matrix.normal_activity_amplitude_gradient_coeff_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_activity_amplitude_gradient_coeff_one

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_diagonal_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_diagonal_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_inverse_product_coeff_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_inverse_product_coeff_one

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_entry_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_entry_short

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_diagonal_high_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_diagonal_high_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_period_activity_high_inverse_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_period_activity_high_inverse_jet

/-- info: 'SkewCornerDescent.Matrix.ordinary_profile_coeff_at_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.ordinary_profile_coeff_at_index

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_response_rows_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_response_rows_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_response_cols_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_response_cols_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_coeff_at_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_coeff_at_row

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_coeff_at_col' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_coeff_at_col

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_prefix_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_prefix_separation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_suffix_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_suffix_separation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_prefix_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_prefix_matrix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_suffix_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_suffix_matrix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitPrefixIndex_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitPrefixIndex_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitPrefixIndex_surjective_through' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitPrefixIndex_surjective_through

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitSuffixIndex_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitSuffixIndex_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitSuffixIndex_surjective_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalUnitSuffixIndex_surjective_from

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_incoming_prefix_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_incoming_prefix_value

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_outgoing_suffix_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_outgoing_suffix_value

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_incoming_protected_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_incoming_protected_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_outgoing_protected_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_outgoing_protected_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_selected_block_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_selected_block_cases

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_interval_block_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_interval_block_cases

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_far_row_invisible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_far_row_invisible

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_far_col_invisible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_far_col_invisible

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_visible_row_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_visible_row_cases

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_visible_col_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_visible_col_cases

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_first_slope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_first_slope

/-- info: 'SkewCornerDescent.Matrix.normal_det_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_det_coeff_one

/-- info: 'SkewCornerDescent.Matrix.normal_det_first_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_det_first_slope

/-- info: 'SkewCornerDescent.Matrix.upper_hessenberg_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.upper_hessenberg_trace

/-- info: 'SkewCornerDescent.Matrix.upper_triangular_inverse_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.upper_triangular_inverse_diagonal

/-- info: 'SkewCornerDescent.Matrix.upper_triangular_inverse_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.upper_triangular_inverse_adjacent

/-- info: 'SkewCornerDescent.Matrix.hessenberg_normal_first_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_normal_first_slope

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_first_normal_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_first_normal_balance

/-- info: 'SkewCornerDescent.Matrix.one_active_comparison_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_active_comparison_coeff_one

/-- info: 'SkewCornerDescent.Matrix.normal_log_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_log_coeff_one

/-- info: 'SkewCornerDescent.Matrix.normalized_log_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalized_log_coeff_one

/-- info: 'SkewCornerDescent.Matrix.normLog_internal_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normLog_internal_caps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_normal_log_internal_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_normal_log_internal_caps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_first_slope_internal_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_first_slope_internal_caps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalComparison_internal_log_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalComparison_internal_log_balance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalComparison_internal_log_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalComparison_internal_log_balance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_first_normal_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_first_normal_balance

/-- info: 'SkewCornerDescent.Matrix.hessenberg_forward_cost_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_forward_cost_nat

/-- info: 'SkewCornerDescent.Matrix.hessenberg_one_shy_disjoint_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_one_shy_disjoint_pair

/-- info: 'SkewCornerDescent.Matrix.hessenberg_two_upper_positions_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_two_upper_positions_unique

/-- info: 'SkewCornerDescent.Matrix.hessenberg_single_interval_weighted_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_single_interval_weighted_product

/-- info: 'SkewCornerDescent.Matrix.hessenberg_one_shy_weighted_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_one_shy_weighted_product

/-- info: 'SkewCornerDescent.Matrix.two_interval_cycle_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.two_interval_cycle_apply

/-- info: 'SkewCornerDescent.Matrix.two_interval_cycle_hessenberg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.two_interval_cycle_hessenberg

/-- info: 'SkewCornerDescent.Matrix.two_interval_cycle_upper_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.two_interval_cycle_upper_data

/-- info: 'SkewCornerDescent.Matrix.two_interval_cycle_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.two_interval_cycle_cost

/-- info: 'SkewCornerDescent.Matrix.hessenberg_one_shy_eq_two_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_one_shy_eq_two_cycles

/-- info: 'SkewCornerDescent.Matrix.two_interval_cycle_one_shy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.two_interval_cycle_one_shy

/-- info: 'SkewCornerDescent.Matrix.oneShyPairToPermutation_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.oneShyPairToPermutation_positions

/-- info: 'SkewCornerDescent.Matrix.oneShyPair_starts_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.oneShyPair_starts_ne

/-- info: 'SkewCornerDescent.Matrix.oneShyPairToPermutation_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.oneShyPairToPermutation_injective

/-- info: 'SkewCornerDescent.Matrix.oneShyPairToPermutation_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.oneShyPairToPermutation_surjective

/-- info: 'SkewCornerDescent.Matrix.one_shy_marked_sum_eq_interval_pairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_shy_marked_sum_eq_interval_pairs

/-- info: 'SkewCornerDescent.Matrix.one_shy_cost_two_retains_two_marks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_shy_cost_two_retains_two_marks

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_single_interval_activity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_single_interval_activity

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_one_shy_activity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_one_shy_activity

/-- info: 'SkewCornerDescent.Matrix.oneShyPairToPermutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.oneShyPairToPermutation

/-- info: 'SkewCornerDescent.Matrix.oneShyPairEquivMarkedPermutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.oneShyPairEquivMarkedPermutation

/-- info: 'SkewCornerDescent.Matrix.hessenberg_marked_activity_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_marked_activity_derivative

/-- info: 'SkewCornerDescent.Matrix.hessenberg_det_marked_activity_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_det_marked_activity_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_derivative_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_derivative_inputs

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_det_marked_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_det_marked_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalPeriodHigherIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalPeriodHigherIndex

/-- info: 'SkewCornerDescent.Matrix.normal_cost_prefactor_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_cost_prefactor_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_two_costs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_two_costs

/-- info: 'SkewCornerDescent.Matrix.one_shy_marked_sum_eq_filtered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_shy_marked_sum_eq_filtered

/-- info: 'SkewCornerDescent.Matrix.one_shy_filtered_sum_eq_interval_pairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_shy_filtered_sum_eq_interval_pairs

/-- info: 'SkewCornerDescent.Matrix.oneShyPair_remaining_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.oneShyPair_remaining_activity

/-- info: 'SkewCornerDescent.Matrix.one_shy_filtered_activity_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_shy_filtered_activity_sum

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_residue_polynomial_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_residue_polynomial_chain

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_residue_chart_polynomial_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_residue_chart_polynomial_chain

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedSuffix_sum_eq_of_zero_off' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedSuffix_sum_eq_of_zero_off

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedSuffix_inverse_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedSuffix_inverse_transport

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedSuffix_residueRight_coeff_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedSuffix_residueRight_coeff_sum

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSuffix_residueRight_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSuffix_residueRight_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSuffix_row_lt_col' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSuffix_row_lt_col

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_selected_suffix_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_selected_suffix_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_selected_prefix_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_selected_prefix_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normal_hh_normal_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normal_hh_normal_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normal_interval_profile_normal_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normal_interval_profile_normal_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_direction_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_direction_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalLeftEndpointPolynomial_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalLeftEndpointPolynomial_residue

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalRightEndpointPolynomial_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalRightEndpointPolynomial_residue

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_first_jet_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_first_jet_profile

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_cross_profile_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_cross_profile_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_long_response_local_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_long_response_local_gradient

/-- info: 'SkewCornerDescent.Matrix.beta_inverse_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.beta_inverse_map

/-- info: 'SkewCornerDescent.Matrix.betaEndpointLeftPolynomial_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.betaEndpointLeftPolynomial_map

/-- info: 'SkewCornerDescent.Matrix.betaEndpointRightPolynomial_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.betaEndpointRightPolynomial_map

/-- info: 'SkewCornerDescent.Matrix.endpointVariation_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.endpointVariation_indicator

/-- info: 'SkewCornerDescent.Matrix.retainedResponse_endpointVariation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.retainedResponse_endpointVariation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_hh_chart_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.residue_hh_chart_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_interval_chart_profile_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.residue_interval_chart_profile_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_chart_profile_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_chart_profile_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_raw_chart_first_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_raw_chart_first_jet

/-- info: 'SkewCornerDescent.Matrix.single_interval_remaining_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.single_interval_remaining_activity

/-- info: 'SkewCornerDescent.Matrix.hessenberg_single_marked_activity_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_single_marked_activity_sum

/-- info: 'SkewCornerDescent.Matrix.hessenberg_marked_one_length_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_marked_one_length_sum

/-- info: 'SkewCornerDescent.Matrix.hessenberg_marked_two_length_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_marked_two_length_sum

/-- info: 'SkewCornerDescent.Matrix.sum_two_adjacent_frontiers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.sum_two_adjacent_frontiers

/-- info: 'SkewCornerDescent.Matrix.normalized_log_deriv_mul_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalized_log_deriv_mul_independent

/-- info: 'SkewCornerDescent.Matrix.normal_marked_first_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normal_marked_first_coeff

/-- info: 'SkewCornerDescent.Matrix.hessenberg_partition_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_partition_coeff_one

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_frontier_intervals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_frontier_intervals

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_interval_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_interval_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_partition_log_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_partition_log_next

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_first_interval_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_first_interval_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_log_interval_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_marked_log_interval_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_partition_coeff_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_partition_coeff_one

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalResponseMatrix_selected_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalResponseMatrix_selected_entry

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_period_entry_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_period_entry_gradient

/-- info: 'SkewCornerDescent.Matrix.one_shy_pair_sum_eq_filtered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_shy_pair_sum_eq_filtered

/-- info: 'SkewCornerDescent.Matrix.one_shy_disjoint_pair_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.one_shy_disjoint_pair_cancellation

/-- info: 'SkewCornerDescent.Matrix.adjacent_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.adjacent_pair_sum

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_partition_coeff_one_pairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_partition_coeff_one_pairs

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_long_response_local_gradient_laurent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_long_response_local_gradient_laurent

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_long_entry_local_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_long_entry_local_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_core_words_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_core_words_copy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_core_words_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_core_words_mod

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_period_response_normal_gradient_of_core_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_period_response_normal_gradient_of_core_phase

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_core_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_core_phase

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_closure_core_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_closure_core_phase

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_closure_period_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_closure_period_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_selected_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_selected_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_selected_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_selected_card

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_profile_selected_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_profile_selected_count

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureSelectedCopy_strictMono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureSelectedCopy_strictMono

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureSelectedCopy_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureSelectedCopy_before

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureEnumeration_strictMono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureEnumeration_strictMono

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureEnumeration_eq_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosureEnumeration_eq_original

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_enumeration_upper_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_enumeration_upper_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_enumeration_lower_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_enumeration_lower_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_enumeration_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_enumeration_copy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_core_words_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_core_words_copy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_core_words_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_core_words_mod

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_ordered_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_ordered_endpoints

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_core_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_core_phase
