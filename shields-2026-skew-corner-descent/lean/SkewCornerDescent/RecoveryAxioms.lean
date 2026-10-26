/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ComponentRowRecovery
import SkewCornerDescent.Matrix.UnitVertexProfileCoefficients
import SkewCornerDescent.Matrix.SelectedCoreLowProfiles
import SkewCornerDescent.Matrix.OriginalHessenbergTops
import SkewCornerDescent.Matrix.OriginalCoreProductJets
import SkewCornerDescent.Matrix.OrderedComponentRowRecovery
import SkewCornerDescent.Matrix.OrderedProfileLocality
import SkewCornerDescent.Matrix.ProtectedProfileGroups
import SkewCornerDescent.Matrix.LiteralComponentBetaRecovery
import SkewCornerDescent.Matrix.BetaSetReindex

/-!
# Axiom guards for protected component recovery coefficients

Guards the complete original extreme inverse entries and their protected profile
coefficients supporting `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
-/

/-- info: 'SkewCornerDescent.Matrix.last_column_minor_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.last_column_minor_ne_zero

/-- info: 'SkewCornerDescent.Matrix.first_row_minor_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.first_row_minor_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_least_column_entry_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_least_column_entry_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_greatest_row_entry_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_inverse_greatest_row_entry_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.component_incoming_protected_coefficient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.component_incoming_protected_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.component_outgoing_protected_coefficient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.component_outgoing_protected_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.component_residue_inverse_mem_selected_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.component_residue_inverse_mem_selected_lower

/-- info: 'SkewCornerDescent.Matrix.residue_higher_linear_support_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.residue_higher_linear_support_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.component_extreme_incoming_columns_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.component_extreme_incoming_columns_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.component_extreme_outgoing_rows_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.component_extreme_outgoing_rows_eq

/-- info: 'SkewCornerDescent.Matrix.unit_vertex_response_correction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.unit_vertex_response_correction

/-- info: 'SkewCornerDescent.Matrix.geometric_unit_vertex_feedback_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.geometric_unit_vertex_feedback_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.geometric_vertex_left_correction_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.geometric_vertex_left_correction_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.geometric_vertex_right_correction_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.geometric_vertex_right_correction_lower

/-- info: 'SkewCornerDescent.Matrix.midpointCorrectionPolynomial_coeff_two'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.midpointCorrectionPolynomial_coeff_two

/-- info: 'SkewCornerDescent.Matrix.midpoint_correction_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.midpoint_correction_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_vertex_changes_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_midpoint_vertex_changes_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_early_literal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_early_literal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_incoming_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_incoming_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_outgoing_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_outgoing_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_profile_product_gradient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_profile_product_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_selected_gt_twice_top'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_selected_gt_twice_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_profile_top_gradient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_profile_top_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_product_coeff_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_product_coeff_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_literal_of_left_jet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_literal_of_left_jet

/-- info: 'SkewCornerDescent.normalized_unit_power_dvd'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.normalized_unit_power_dvd

/-- info: 'SkewCornerDescent.normalized_unit_power_coeff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.normalized_unit_power_coeff

/-- info: 'SkewCornerDescent.unit_jet_product_right'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.unit_jet_product_right

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_interval_profile_gradient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_interval_profile_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_response_first_differences_opposite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.residue_response_first_differences_opposite

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_pruned'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_pruned

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_profile_gradient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_profile_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_response_first_differences_opposite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_response_first_differences_opposite

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_original_incoming_top'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_original_incoming_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_original_outgoing_top'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_original_outgoing_top

/-- info: 'SkewCornerDescent.Matrix.incoming_inverse_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.incoming_inverse_prefix

/-- info: 'SkewCornerDescent.Matrix.outgoing_inverse_suffix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.outgoing_inverse_suffix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_left_low_coeff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_left_low_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_right_low_coeff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_right_low_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.protected_profile_visible_match'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.protected_profile_visible_match

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.triangular_higher_linear_support_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.triangular_higher_linear_support_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.effective_incoming_support_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.effective_incoming_support_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.effective_outgoing_support_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.effective_outgoing_support_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_extreme_incoming_columns_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_extreme_incoming_columns_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_extreme_outgoing_rows_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.ordered_component_extreme_outgoing_rows_eq

/-- info: 'SkewCornerDescent.Matrix.literal_component_of_beta_sets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.literal_component_of_beta_sets

/-- info: 'SkewCornerDescent.Matrix.beta_contraction_eq_of_sets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.beta_contraction_eq_of_sets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_vertex_incoming_protected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_vertex_incoming_protected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_vertex_outgoing_protected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_vertex_outgoing_protected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_low_strip'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_left_profile_low_strip

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_low_strip'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_right_profile_low_strip

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_strip_eq_selected_core'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_left_strip_eq_selected_core

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_strip_eq_selected_core'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_right_strip_eq_selected_core

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_profile_discrepancy_gt_top_of_cores'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_profile_discrepancy_gt_top_of_cores

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_profile_product_low_cores'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_profile_product_low_cores

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_equal_response_core_products'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_equal_response_core_products
