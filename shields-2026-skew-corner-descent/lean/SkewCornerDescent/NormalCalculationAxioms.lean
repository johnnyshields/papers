/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalPeriodGradient
import SkewCornerDescent.Matrix.OriginalInternalNextLogFrontier

/-!
# Complete normal-calculation and original high-interval axiom guards

Guards both exact normal logarithmic frontiers, the full surviving-generator
series derivative, original inverse/profile gradients, and produced actual
period-length raw selected-function high coefficients.
-/

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_mul_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_mul_next

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_pow_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_pow_next

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_log_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_log_next

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_log_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_normalized_log_next

/-- info: 'SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation

/-- info: 'SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation_coeff

/-- info: 'SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation_C

/-- info: 'SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.powerSeriesCoefficientDerivation_X

/-- info: 'SkewCornerDescent.Matrix.residueSeriesGeneratorDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueSeriesGeneratorDeriv

/-- info: 'SkewCornerDescent.Matrix.residueSeriesGeneratorDeriv_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueSeriesGeneratorDeriv_coeff

/-- info: 'SkewCornerDescent.Matrix.residueSeriesGeneratorDeriv_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.residueSeriesGeneratorDeriv_C

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_shape

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_subdiagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_subdiagonal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_det_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_det_interval

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_constant_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_constant_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_before_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_before_first

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normalized_log_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normalized_log_next

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normal_hh_higher_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normal_hh_higher_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_contraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_contraction

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_pruned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_pruned

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normal_interval_profile_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normal_interval_profile_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_profile_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_profile_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_low_core_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_low_core_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_low_core_jets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_low_core_jets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_gradient_above_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normal_gradient_above_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_prime_top_partial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_prime_top_partial

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_coefficient_eq_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.residue_coefficient_eq_normal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_polynomial_product_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_polynomial_product_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_polynomial_product_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_polynomial_product_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_cross_polynomial_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_cross_polynomial_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_multiple_phase_jets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_multiple_phase_jets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_period_endpoint_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_period_endpoint_height

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_period_total_gt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_period_total_gt_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_period_response_normal_gradient_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_period_response_normal_gradient_of_le

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_period_response_normal_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_period_response_normal_gradient

