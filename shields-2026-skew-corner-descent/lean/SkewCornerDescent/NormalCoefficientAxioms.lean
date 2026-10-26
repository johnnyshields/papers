/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalDefectCoefficient
import SkewCornerDescent.Matrix.OriginalNormalCoefficientDerivatives
import SkewCornerDescent.Matrix.NormalVirtualDifference
import SkewCornerDescent.Matrix.OriginalClosureQuotientTransfer
import SkewCornerDescent.Matrix.NormalComparisonCoefficient
import SkewCornerDescent.Matrix.OriginalVirtualClosureTransfer
import SkewCornerDescent.Matrix.OriginalAmalgamationCyclicInventory
import SkewCornerDescent.Matrix.OriginalAmalgamationNormalTransfer
import SkewCornerDescent.Matrix.OriginalVirtualCycleTransfer
import SkewCornerDescent.Matrix.OriginalComparisonLogTransfer
import SkewCornerDescent.Matrix.NormalRationalFactorization
import SkewCornerDescent.Matrix.NormalOrientationTransfer
import SkewCornerDescent.Matrix.NormalRationalCoefficientTransfer
import SkewCornerDescent.Matrix.OriginalRationalPrefactor
import SkewCornerDescent.Matrix.OriginalTransfer
import SkewCornerDescent.Matrix.OriginalMaximalBinFull
import SkewCornerDescent.Matrix.OriginalDualIdentities
import SkewCornerDescent.Matrix.OriginalPrimitiveShort
import SkewCornerDescent.Matrix.OriginalShortCoefficient
import SkewCornerDescent.CyclicLogBalance
import SkewCornerDescent.Matrix.OriginalOnePositiveShort
import SkewCornerDescent.Matrix.OriginalAutomaticOpen

/-!
# Axiom guards for complete normal coefficient transfer

Guards the original-generator and full logarithm coefficient statements supporting
`shields-2026-skew-corner-descent.tex` (`lem:original-transfer`, `lem:maximal-bin`).
-/

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_mul_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_mul_zero

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_mul_first' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_mul_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_pow_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_pow_zero

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_pow_first' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_pow_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_log_first' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_log_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_log_first' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_normalized_log_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normal_defect' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_normal_defect

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_inv_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_inv_zero

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_inv_first' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.coeff_deriv_inv_first

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalCost_derivative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalCost_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_derivative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff_derivative

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_difference_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_normalized_difference_first

/-- info: 'SkewCornerDescent.CyclicWindows.linearInverseWindowSum_closure_double' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.linearInverseWindowSum_closure_double

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_virtual_closure_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_virtual_closure_first

/-- info: 'SkewCornerDescent.CyclicWindows.linearInverseWindowSum_complete_double'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.linearInverseWindowSum_complete_double

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_linear_inventory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_linear_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_quotient_log_cyclic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_quotient_log_cyclic

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_mul_log_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_normalized_mul_log_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_inv_log_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_normalized_inv_log_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_pow_log_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_normalized_pow_log_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_prod_log_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_normalized_prod_log_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_normalized_signed_product_log_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_normalized_signed_product_log_first

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_complete_comparison_defect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_complete_comparison_defect

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_normalized_log_linear_periodic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_normalized_log_linear_periodic

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_from_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_from_source

/-- info: 'SkewCornerDescent.finiteWordCycle_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.finiteWordCycle_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_linear_inventory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_linear_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_component_span'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_component_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_completed_gap_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_completed_gap_word

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_normalized_log_from_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_normalized_log_from_source

/-- info: 'SkewCornerDescent.CyclicWindows.inverseWindowSum_complete_replace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.inverseWindowSum_complete_replace

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_cycle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_cycle

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_normalized_log_from_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_normalized_log_from_source

/-- info: 'SkewCornerDescent.Matrix.signedNormalProduct_mul_common'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.signedNormalProduct_mul_common

/-- info: 'SkewCornerDescent.Matrix.normalRationalDefect_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.normalRationalDefect_factorization

/-- info: 'SkewCornerDescent.Matrix.normalizedSeries_constant_unit_mul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.normalizedSeries_constant_unit_mul

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_oriented_normal_defect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_oriented_normal_defect

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_full_rational_defect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_full_rational_defect

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualCentralResponse_eq_signed_cap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualCentralResponse_eq_signed_cap

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_residue_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_residue_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_residue_transcendental'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_residue_transcendental

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalPrefactor_constant_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalPrefactor_constant_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalDefect_coefficient_of_residue_match'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalDefect_coefficient_of_residue_match

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_rational_prefactor_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_rational_prefactor_zero

/-- info: 'SkewCornerDescent.Matrix.coeff_deriv_full_rational_defect_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.coeff_deriv_full_rational_defect_zero

/-- info: 'SkewCornerDescent.Matrix.rationalDefect_residue_match'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.rationalDefect_residue_match

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_component_span'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_component_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualCentralResponse_eq_oriented_cap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualCentralResponse_eq_oriented_cap

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalClasses_coefficient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalClasses_coefficient

/-- info: 'SkewCornerDescent.Matrix.jetsAffineOver_mul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.jetsAffineOver_mul

/-- info: 'SkewCornerDescent.Matrix.jetsAffineOver_inv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.jetsAffineOver_inv

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_long_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.hessenberg_permutation_long_unique

/-- info: 'SkewCornerDescent.Matrix.hessenberg_jets_affine'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.hessenberg_jets_affine

/-- info: 'SkewCornerDescent.Matrix.fullRationalDefect_jets_affine'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.fullRationalDefect_jets_affine

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_jets_affine_periodic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_jets_affine_periodic

/-- info: 'SkewCornerDescent.signedRational_series_transfer'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.signedRational_series_transfer

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPeriodIncrement_span'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalPeriodIncrement_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCyclicTop_gt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalCyclicTop_gt

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTransfer_all_eligible_indices'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalTransfer_all_eligible_indices

/-- info: 'SkewCornerDescent.transcendental_signed_reciprocal_sum_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.transcendental_signed_reciprocal_sum_ne_zero

/-- info: 'SkewCornerDescent.CyclicWindows.integer_zmod_period_of_maximum_eq_average'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.integer_zmod_period_of_maximum_eq_average

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtual_signed_reciprocal_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtual_signed_reciprocal_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_maximum_alternative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_maximum_alternative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_maximal_gap_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSchur_maximal_gap_frontier

/-- info: 'SkewCornerDescent.CyclicWindows.filteredInverseWindowSum_closure_scale'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.filteredInverseWindowSum_closure_scale

/-- info: 'SkewCornerDescent.sum_prod_inv_ne_zero_of_positive_specialization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.sum_prod_inv_ne_zero_of_positive_specialization

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_inverse_inventory_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_inverse_inventory_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_filtered_inventory_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_filtered_inventory_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_from_gap_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_from_gap_bound

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_period_distance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_period_distance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_completed_gap_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_completed_gap_bound

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_strict_normalized_log_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_strict_normalized_log_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualResidue_signed_reciprocal_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualResidue_signed_reciprocal_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_strict_bin_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_strict_bin_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalClasses_representation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalClasses_representation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalDefect_strict_bin_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRationalDefect_strict_bin_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalMaximalBin_alternative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalMaximalBin_alternative

/-- info: 'SkewCornerDescent.CyclicWindows.filteredLinearInverseWindowSum_complete_double'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.CyclicWindows.filteredLinearInverseWindowSum_complete_double

/-- info: 'SkewCornerDescent.CyclicWindows.filteredInverseWindowSum_complete_replace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.filteredInverseWindowSum_complete_replace

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalFilteredIntervalInventory_eq_linear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalFilteredIntervalInventory_eq_linear

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_filtered_interval_inventory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_filtered_interval_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_period_gap_windows'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_period_gap_windows

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_filtered_interval_inventory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_filtered_interval_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_filtered_cycle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVirtualClosure_normalized_log_filtered_cycle

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_normalized_log_filtered_bin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_normalized_log_filtered_bin

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalMaximalBin_full'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalMaximalBin_full

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_dual_identities'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_dual_identities

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_rational_class_sums'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_rational_class_sums

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_actual_dual_nonvanishing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_actual_dual_nonvanishing

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_inventory_dual_nonvanishing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_inventory_dual_nonvanishing

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalActual_coefficient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalActual_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalManyActive_periodic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalManyActive_periodic

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalManyActive_general'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalManyActive_general

/-- info: 'SkewCornerDescent.CyclicWindows.window_dual_eligible_nonvanishing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.window_dual_eligible_nonvanishing

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_short'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_short

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalShort_coefficient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalShort_coefficient

/-- info: 'SkewCornerDescent.CyclicWindows.cyclic_signed_log_balance'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.cyclic_signed_log_balance

/-- info: 'SkewCornerDescent.CyclicWindows.one_positive_cyclic_last_pos'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.one_positive_cyclic_last_pos

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_positive_separated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseClasses_positive_separated

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOnePositive_inventories'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalOnePositive_inventories

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOnePositive_short'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalOnePositive_short

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAutomatic_open'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAutomatic_open
