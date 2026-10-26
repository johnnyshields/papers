/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.PhysicalFrameAxioms

/-!
# Actual literal-recovery and coefficient-field axiom guards

Guards the complete original coefficient, literal-root, intrinsic-order,
response-valuation and finite ordinary-gauge constructions.
-/

/-- info: 'SkewCornerDescent.polynomial_product_coeff_mem_subfield' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.polynomial_product_coeff_mem_subfield

/-- info: 'SkewCornerDescent.polynomial_laurent_coeff_mem_subfield' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.polynomial_laurent_coeff_mem_subfield

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_residue_mem_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_residue_mem_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCrossPrefixCharge_mem_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCrossPrefixCharge_mem_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelfPrefixCharge_mem_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelfPrefixCharge_mem_lower

/-- info: 'SkewCornerDescent.transcendental_over_derivation_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.transcendental_over_derivation_constants

/-- info: 'SkewCornerDescent.Matrix.normalCyclicFirstCharge_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalCyclicFirstCharge_deriv

/-- info: 'SkewCornerDescent.Matrix.normalCyclicFirstCharge_deriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalCyclicFirstCharge_deriv_zero

/-- info: 'SkewCornerDescent.simple_extension_derivation_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.simple_extension_derivation_constants

/-- info: 'SkewCornerDescent.simple_extension_affine_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.simple_extension_affine_polynomial

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_first_cyclic_high_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_first_cyclic_high_zero

/-- info: 'SkewCornerDescent.Matrix.residueGeneratorCoefficientField_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueGeneratorCoefficientField_fixed

/-- info: 'SkewCornerDescent.Matrix.residueGeneratorCoefficientField_adjoin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueGeneratorCoefficientField_adjoin

/-- info: 'SkewCornerDescent.Matrix.residueGeneratorCoefficientField_transcendental' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueGeneratorCoefficientField_transcendental

/-- info: 'SkewCornerDescent.Matrix.residueGeneratorDeriv_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueGeneratorDeriv_eq_zero_iff

/-- info: 'SkewCornerDescent.Matrix.residueGenerator_affine_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueGenerator_affine_polynomial

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_first_log_high_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_first_log_high_zero

/-- info: 'SkewCornerDescent.partial_mem_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.partial_mem_supported

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_gradient_mem_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_gradient_mem_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_second_high_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_second_high_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_affine_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_affine_coefficient

/-- info: 'SkewCornerDescent.Matrix.normalCyclicFirstCharge_balanced_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalCyclicFirstCharge_balanced_deriv

/-- info: 'SkewCornerDescent.Matrix.normalDiagonalCycle_inverse_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalDiagonalCycle_inverse_pair

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_first_log_two_high_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_first_log_two_high_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_first_log_all_high_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_first_log_all_high_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_phase_energy_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_phase_energy_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_literal_of_right_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_literal_of_right_jet

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_start_core_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_start_core_literal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_end_core_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_end_core_literal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_interval_incoming_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_interval_incoming_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_left_profile_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_left_profile_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.protected_unit_incoming' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.protected_unit_incoming

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.protected_unit_outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.protected_unit_outgoing

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_interval_outgoing_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_interval_outgoing_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_right_profile_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_empty_right_profile_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_incoming_unit_row_ne_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_incoming_unit_row_ne_empty

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_outgoing_unit_col_ne_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_outgoing_unit_col_ne_empty

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_nonzero_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_nonzero_position

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_nonzero_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_nonzero_position

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_row_distance_band' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_row_distance_band

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_col_distance_band' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_col_distance_band

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_nonselected_row_high' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_nonselected_row_high

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_nonselected_col_high' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_nonselected_col_high

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_row_low_iff_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_row_low_iff_selected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_col_low_iff_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_col_low_iff_selected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_incoming_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_incoming_atom

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_outgoing_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_outgoing_atom

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_nonselected_left_profile_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_nonselected_left_profile_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_nonselected_right_profile_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_nonselected_right_profile_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_incoming_block_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_incoming_block_match

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_outgoing_block_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_outgoing_block_match

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_tau_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_tau_strict

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_top_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_top_strict

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_tau_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_tau_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_top_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_top_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_gt_tau' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_gt_tau

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_col_lt_row_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_col_lt_row_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_row_sets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_row_sets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_col_sets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_col_sets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_rows_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_rows_exists

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_cols_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_cols_exists

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_row_le_block_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_row_le_block_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_col_ge_tau' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_col_ge_tau

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_distances_least' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_distances_least

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_col_distances_least' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_col_distances_least

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_incoming_extreme' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_incoming_extreme

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_outgoing_extreme' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_outgoing_extreme

/-- info: 'SkewCornerDescent.Matrix.vertex_outgoing_inverse_affine_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.vertex_outgoing_inverse_affine_copy

/-- info: 'SkewCornerDescent.Matrix.vertex_incoming_inverse_affine_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.vertex_incoming_inverse_affine_copy

/-- info: 'SkewCornerDescent.Matrix.profile_beta_cast_of_cells_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.profile_beta_cast_of_cells_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_endpoint_equiv_of_core_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_endpoint_equiv_of_core_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_endpoint_equiv_of_core_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_endpoint_equiv_of_core_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_prefix_equiv_of_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_prefix_equiv_of_matches

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_suffix_equiv_of_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_suffix_equiv_of_matches

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_distances_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_distances_normalized

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_col_distances_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_col_distances_normalized

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_endpoint_equiv_of_lists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_endpoint_equiv_of_lists

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_columns_of_prefix_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_columns_of_prefix_copy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_left_unit_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_left_unit_extension

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_half_midpoint_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_half_midpoint_unique

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_rows_of_suffix_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_rows_of_suffix_copy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_right_unit_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_right_unit_extension

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_incoming_empty_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_incoming_empty_recovery

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_outgoing_empty_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_outgoing_empty_recovery

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_straddling_unit_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_straddling_unit_match

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_row_block_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_row_block_strict

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_col_block_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_remaining_col_block_strict

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_unit_prefix_visible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_left_unit_prefix_visible

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_unit_suffix_visible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_right_unit_suffix_visible

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_tau_of_endpoint_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_tau_of_endpoint_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_lt_iff_tau' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_lt_iff_tau

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_between' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_unit_between

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_endpoint_label_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_endpoint_label_le

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_prefix_point_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_left_prefix_point_matches

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_unit_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_left_unit_recovery

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_top_of_endpoint_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_row_top_of_endpoint_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_lt_iff_row_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_lt_iff_row_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_suffix_point_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_right_suffix_point_matches

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_endpoint_equiv_of_end_core_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_selected_endpoint_equiv_of_end_core_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_unit_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_right_unit_recovery

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_extremes_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_extremes_strict

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_prefix_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_prefix_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_suffix_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_unit_suffix_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_incoming_value_of_profile_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_incoming_value_of_profile_jet

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_outgoing_value_of_profile_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_outgoing_value_of_profile_jet

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_straddling_unit_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_straddling_unit_recovery

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_positive_unit_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_positive_unit_recovery

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_nonmidpoint_point_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_nonmidpoint_point_match

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_kept_equiv_of_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_kept_equiv_of_matches

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_unique

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_coordinates

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_nonmidpoint_interval_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_nonmidpoint_interval_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_block_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_block_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_nonmidpoint_iff_block_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_nonmidpoint_iff_block_ne

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_remaining_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_remaining_separation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_midpoint_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_without_midpoint_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_without_midpoint_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.midpoint_vertex_beta_response_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.midpoint_vertex_beta_response_ne

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_response_ne_punctured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_response_ne_punctured

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_presence_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_presence_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_equiv_of_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_equiv_of_matches

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_early_recovery_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_early_recovery_interval

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_nonliteral_first_profile_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_nonliteral_first_profile_difference

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_endpoint_polynomials_of_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_endpoint_polynomials_of_copy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_incoming_difference_visible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_incoming_difference_visible

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_incoming_difference_visible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_incoming_difference_visible

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_phase_discrepancy_choice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_phase_discrepancy_choice

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_phase_resolving_margin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_phase_resolving_margin

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_first_discrepancies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_first_discrepancies

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_phase_energy_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_phase_energy_witness

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_literal_iff_incoming_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_literal_iff_incoming_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_copy_of_incoming_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_copy_of_incoming_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_literal_intervals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_literal_intervals

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_positive_avoiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_positive_avoiding

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_square_energy_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_square_energy_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_filtered_phase_energy_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_filtered_phase_energy_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_filtered_phase_energy_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_filtered_phase_energy_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_log_detection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_normal_log_detection

/-- info: 'SkewCornerDescent.Matrix.log_coeff_ne_zero_imp_ratio_detection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.log_coeff_ne_zero_imp_ratio_detection

/-- info: 'SkewCornerDescent.Matrix.log_coeff_ne_zero_imp_prefactor_detection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.log_coeff_ne_zero_imp_prefactor_detection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_selected_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_selected_count

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_true_cap_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_true_cap_product

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_internal_residue_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_internal_residue_product

/-- info: 'SkewCornerDescent.single_active_packet_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.single_active_packet_support

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_residue_quotient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_residue_quotient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_cap_normalized_power' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_cap_normalized_power

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_ordinary_residue_power' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_ordinary_residue_power

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_supplied_series_power' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_supplied_series_power

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_normal_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_normal_match

/-- info: 'SkewCornerDescent.Matrix.ordinaryMonomialDefect_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.ordinaryMonomialDefect_factorization
