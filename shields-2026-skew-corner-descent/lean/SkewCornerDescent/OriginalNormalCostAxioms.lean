/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureQuotientTransfer
import SkewCornerDescent.LinearCyclicWindows

/-!
# Axiom guards for literal first-fresh interval costs

Guards the complete original determinant frontier and interval contraction supporting
`shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
-/

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_forward_sum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_forward_sum

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_interval_cost' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_interval_cost

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_prod_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_prod_zero

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_zero

/-- info: 'SkewCornerDescent.Matrix.hessenberg_coeff_deriv_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_coeff_deriv_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_constant_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_constant_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_derivative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_independent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_independent

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_minimum_cost'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_minimum_cost

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_product' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_product

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_frontier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_frontier

/-- info: 'SkewCornerDescent.Matrix.hessenberg_coeff_deriv_frontier' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_coeff_deriv_frontier

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_derivative_below'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_derivative_below

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_frontier

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_unique_forward' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_unique_forward

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_interval_apply' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_interval_apply

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_eq_interval_cycle' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_eq_interval_cycle

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_interval_sign' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_interval_sign

/-- info: 'SkewCornerDescent.Matrix.inverse_interval_cycle_apply' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.inverse_interval_cycle_apply

/-- info: 'SkewCornerDescent.Matrix.inverse_interval_cycle_hessenberg' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.inverse_interval_cycle_hessenberg

/-- info: 'SkewCornerDescent.Matrix.inverse_interval_cycle_cost' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.inverse_interval_cycle_cost

/-- info: 'SkewCornerDescent.Matrix.deriv_prod_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.deriv_prod_zero

/-- info: 'SkewCornerDescent.Matrix.deriv_prod_single' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.deriv_prod_single

/-- info: 'SkewCornerDescent.Matrix.inverse_interval_cycle_upper_erase' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.inverse_interval_cycle_upper_erase

/-- info: 'SkewCornerDescent.Matrix.inverse_interval_cycle_upper_derivative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.inverse_interval_cycle_upper_derivative

/-- info: 'SkewCornerDescent.Matrix.hessenberg_frontier_without_long_interval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_frontier_without_long_interval

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_interval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_interval

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_interval_sum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_interval_sum

/-- info: 'SkewCornerDescent.Matrix.inverse_interval_cycle_start' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.inverse_interval_cycle_start

/-- info: 'SkewCornerDescent.Matrix.hessenberg_interval_frontier_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_interval_frontier_iff

/-- info: 'SkewCornerDescent.Matrix.hessenberg_interval_frontier_sum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_interval_frontier_sum

/-- info: 'SkewCornerDescent.Matrix.diagonal_product_inverse_interval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.diagonal_product_inverse_interval

/-- info: 'SkewCornerDescent.Matrix.hessenberg_coeff_deriv_intervals' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_coeff_deriv_intervals

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_derivative_indicator'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_derivative_indicator

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_intervals'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_intervals

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_intervals'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_intervals

/-- info: 
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_detected_intervals'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_detected_intervals

/-- info: 'SkewCornerDescent.Matrix.hessenberg_distance_interval_sum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_distance_interval_sum

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_subdiagonal' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_subdiagonal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_interval_sum' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_interval_sum

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_lt_of_strict_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_lt_of_strict_window

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_short_of_length_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_short_of_length_bound

/-- info: 
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_from_length_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_from_length_bound

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_pos

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_sum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_sum

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_last_eq_splice' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_last_eq_splice

/-- info: 
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response_endpoint_distance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response_endpoint_distance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_response' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_response

/-- info: 'SkewCornerDescent.CyclicWindows.finEquiv_eq_natCast' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.CyclicWindows.finEquiv_eq_natCast

/-- info: 'SkewCornerDescent.CyclicWindows.windowSum_finite_interval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.CyclicWindows.windowSum_finite_interval

/-- info: 'SkewCornerDescent.CyclicWindows.windowSum_finite_wrap' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.CyclicWindows.windowSum_finite_wrap

/-- info: 'SkewCornerDescent.CyclicWindows.windowSum_of_zmod_period' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.CyclicWindows.windowSum_of_zmod_period

/-- info: 'SkewCornerDescent.CyclicWindows.windowSum_of_zmod_period_multiple' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.CyclicWindows.windowSum_of_zmod_period_multiple

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_internal_window' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_internal_window

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_left_window' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_left_window

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_cyclic_internal_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_cyclic_internal_window

/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_left_window_lt_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_left_window_lt_completion

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_eq_diagonal' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_eq_diagonal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_right_window' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_right_window

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_cyclic_right_window_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_cyclic_right_window_lt

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_cyclic_left_window_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_cyclic_left_window_lt

/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_bound_of_cyclic_gaps'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_bound_of_cyclic_gaps

/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_bound_of_periodic_gaps'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_bound_of_periodic_gaps

/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_from_periodic_gaps'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_from_periodic_gaps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_period_sum' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_period_sum

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_eq_cyclic_top_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_eq_cyclic_top_iff

/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_internal_periodic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_internal_periodic

/-- info: 'SkewCornerDescent.Matrix.hessenberg_internal_interval_sum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_internal_interval_sum

/-- info: 'SkewCornerDescent.Matrix.hessenberg_internal_interval_product' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_internal_interval_product

/-- info: 'SkewCornerDescent.Matrix.hessenberg_internal_interval_inverse_windows' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_internal_interval_inverse_windows

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalResidue_linear_windows'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalResidue_linear_windows

/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_linear_periodic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalized_log_linear_periodic

/-- info: 'SkewCornerDescent.linearOffset_inverse_product' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.linearOffset_inverse_product

/-- info: 'SkewCornerDescent.linearInverseWindowSum_cyclic_truncation' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.linearInverseWindowSum_cyclic_truncation

/-- info: 'SkewCornerDescent.linearInverseWindowSum_add_period' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.linearInverseWindowSum_add_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.mem_selectedComponentInventory' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.mem_selectedComponentInventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedBlock_cells_injective' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedBlock_cells_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_eq_original_image'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_eq_original_image

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_card' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_card

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_translate' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_translate

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_inventory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_card' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_card

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_profile_selected_count'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_profile_selected_count

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_minContent_strictAnti' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_minContent_strictAnti

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_lt_iff_minContent' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_lt_iff_minContent

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_order_of_translated_cells' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_order_of_translated_cells

open SkewCornerDescent.Matrix.SelectedCoordinate in
/-- info: 
'SkewCornerDescent.Matrix.SelectedCoordinate.existsUnique_originalSelectedBlock_of_translated_component'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  existsUnique_originalSelectedBlock_of_translated_component

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_copy_exists'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_copy_exists

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_cells'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_strictMono'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_strictMono

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_before'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_before

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureEnumeration_strictMono'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureEnumeration_strictMono

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureEnumeration_eq_original'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureEnumeration_eq_original

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_enumeration_upper_cells'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_enumeration_upper_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_enumeration_lower_cells'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_enumeration_lower_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_central_distance' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_central_distance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_profile_component_span'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_profile_component_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_central_normal_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_central_normal_response

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_cells' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_cells

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_minContent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_minContent

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_maxContent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_maxContent

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_profile_endpoints' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_profile_endpoints

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_minContent_of_translated_cells'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_minContent_of_translated_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_first_cap' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_first_cap

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_last_cap' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_last_cap

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_distance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_distance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_upper

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_mod'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_mod


/-- info: 'SkewCornerDescent.CyclicWindows.finEquiv_symm_val' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.CyclicWindows.finEquiv_symm_val


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_projection


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_period'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_period


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_completed_gap_window


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normalized_log_from_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normalized_log_from_source


/-- info: 'SkewCornerDescent.Matrix.originalProfile_ne' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalProfile_ne


/-- info: 'SkewCornerDescent.Matrix.originalProfile_sw' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalProfile_sw


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalDisplacement_pair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalDisplacement_pair


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_row_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_row_bounds


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_profile_rows' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_profile_rows


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_profile_point' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_profile_point


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_xi_upper' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_xi_upper


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_zeta_upper' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_zeta_upper


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_xi_lower' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_xi_lower


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_zeta_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_zeta_lower


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_xi_upper' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_xi_upper


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_zeta_upper' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_zeta_upper


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_xi_lower' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_xi_lower


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_zeta_lower' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_zeta_lower


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_matrix' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_matrix


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_previous_upper' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_previous_upper


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_previous_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_previous_lower


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_cut_upper' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_cut_upper


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_cut_lower_positive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_cut_lower_positive


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_cut_central' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_cut_central


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_cut_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_cut_lower


/-- info: 'SkewCornerDescent.Matrix.interiorBlock_eq_sum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interiorBlock_eq_sum


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_upper' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_upper


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_lower


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_copy_strictMono' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_copy_strictMono


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_copy_label' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_complementary_copy_label


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_fiber' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_fiber


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_first' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_first


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_last' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_last


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_length' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_length


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_matrix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_matrix


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_det' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_det


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_block_selected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_block_selected


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_copy_coordinates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_copy_coordinates


/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_block_cells' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalHorizontalClosure_block_cells


/-- info: 'SkewCornerDescent.Matrix.originalClosureBlocksEquiv_upper' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalClosureBlocksEquiv_upper


/-- info: 'SkewCornerDescent.Matrix.originalClosureBlocksEquiv_lower' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalClosureBlocksEquiv_lower


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_block_displacement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_block_displacement


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosureSelectedCopy_block


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_size'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_size


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_row_position'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_row_position


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_row'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_row


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_col'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_col


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureRemainingEquiv_upper' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureRemainingEquiv_upper


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureRemainingEquiv_lower' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureRemainingEquiv_lower


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_remaining_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_remaining_endpoints


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_label'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_selected_label


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_remaining_label' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_remaining_label


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_interval_same_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_interval_same_copy


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_interval_other_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_interval_other_copy


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureRemainingCopy_injective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureRemainingCopy_injective


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureResponseIntervalCopy_surjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureResponseIntervalCopy_surjective


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response_interval_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response_interval_endpoints


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_retained_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_retained_endpoints


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_local_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_local_response


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_same_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_same_copy


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_other_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_other_copy


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureCapIntervalCopy_surjective' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosureCapIntervalCopy_surjective


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_interval_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_interval_endpoints


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_retained_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_retained_endpoints


/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_response


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_enumeration_copy' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_enumeration_copy


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_ordered_response' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_ordered_response


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_ordered_left_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_ordered_left_response


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_ordered_right_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_ordered_right_response


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_response_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_response_copy


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_response_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_response_word


/-- info:

'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_response_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_response_product


/-- info:

'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_residue_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_residue_product


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_true_left_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_true_left_response


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_true_right_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_true_right_response


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_true_cap_product' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_true_cap_product


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response_residue_det'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response_residue_det


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_original_quotient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_original_quotient


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_residue_quotient' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_residue_quotient


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_residue_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_residue_ne_zero


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_regular_cross' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_regular_cross


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_quotient' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_quotient


/-- info:
'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normalized_quotient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normalized_quotient


/-- info:
'SkewCornerDescent.Matrix.coeff_deriv_inv_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_inv_zero


/-- info:
'SkewCornerDescent.Matrix.coeff_deriv_inv_first' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_inv_first


/-- info:
'SkewCornerDescent.Matrix.coeff_deriv_normalized_quotient_log_first' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_normalized_quotient_log_first


/-- info:

'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_quotient_log_from_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_quotient_log_from_source

