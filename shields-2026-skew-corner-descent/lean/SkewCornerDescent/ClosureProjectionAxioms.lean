/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCoreProjectionBlocks
import SkewCornerDescent.Matrix.OriginalEndpointProjectionZeros
import SkewCornerDescent.Matrix.IntervalResponseHessian
import SkewCornerDescent.Matrix.OriginalCapProductHessian
import SkewCornerDescent.Matrix.ResidueHessianSymmetry
import SkewCornerDescent.Matrix.OriginalCapInverseProjection
import SkewCornerDescent.Matrix.OriginalPrivateUnitProjection
import SkewCornerDescent.Matrix.OriginalOrdinaryPrivateCapLocalization
import SkewCornerDescent.Matrix.OriginalPrivatePeriodTop
import SkewCornerDescent.Matrix.OriginalPrivatePeriodComparison
import SkewCornerDescent.Matrix.OriginalPhaseHessianProjection
import SkewCornerDescent.Matrix.OriginalPrivateHessianPin
import SkewCornerDescent.Matrix.OriginalPinnedSupportAlternative

/-!
# Axiom guards for complete actual closure projection ingredients

Guards the full original Hessian, complete inverse projections, original
component support and proper-core weight replacement supporting
`shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
-/

/-- info: 'SkewCornerDescent.Matrix.entryDeriv_retainedResponse_hessian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.entryDeriv_retainedResponse_hessian

/-- info: 'SkewCornerDescent.Matrix.generatorDeriv_intervalResponse_hessian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.generatorDeriv_intervalResponse_hessian

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_interval_response_hessian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_interval_response_hessian

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_hessian_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_hessian_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_projection_same_blocks'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_projection_same_blocks

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_inverse_entry_span'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_inverse_entry_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_projection_proper_cores'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_projection_proper_cores

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_proper_core_hessian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_proper_core_hessian

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTrueCapProduct_hessian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalTrueCapProduct_hessian

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_higher_commute'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_higher_commute

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_first_strip_core_projection_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_first_strip_core_projection_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_last_strip_core_projection_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_last_strip_core_projection_zero

/-- info: 'SkewCornerDescent.Matrix.profile_private_unit_vertex_count'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.profile_private_unit_vertex_count

/-- info: 'SkewCornerDescent.Matrix.vertexBetaMatrix_affine_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.vertexBetaMatrix_affine_reindex

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_affine_beta_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.profileInverseProjection_affine_beta_copy

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_restrict_blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.profileInverseProjection_restrict_blocks

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_prefix_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.profileInverseProjection_prefix_cap

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_suffix_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.profileInverseProjection_suffix_cap

/-- info: 'SkewCornerDescent.Matrix.private_diagonal_no_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.private_diagonal_no_interior

/-- info: 'SkewCornerDescent.Matrix.private_diagonal_interior_components_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.private_diagonal_interior_components_separated

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_inverse_projection_same_blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_inverse_projection_same_blocks

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_core_projection_same_blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_core_projection_same_blocks

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_inverse_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_cap_inverse_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_cap_inverse_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_cap_inverse_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_cap_inverse_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_cap_inverse_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_cap_inverse_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_cap_inverse_projection

/-- info: 'SkewCornerDescent.Matrix.profile_private_beta_pair_trichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.profile_private_beta_pair_trichotomy

/-- info: 'SkewCornerDescent.Matrix.profile_private_same_block_endpoints_trichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.profile_private_same_block_endpoints_trichotomy

/-- info: 'SkewCornerDescent.Matrix.geometric_unit_vertex_projection_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.geometric_unit_vertex_projection_insert

/-- info: 'SkewCornerDescent.Matrix.blockTriangular_kept_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.blockTriangular_kept_det_ne_zero

/-- info: 'SkewCornerDescent.Matrix.blockTriangularKeptInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.blockTriangularKeptInverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_cut_trichotomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_cut_trichotomy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_of_beta_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_of_beta_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_unit_iff_vertical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_unit_iff_vertical

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_unit_block_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_unit_block_singleton

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_interval_iff_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_interval_iff_endpoints

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_of_remaining_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_of_remaining_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalKeptBlockInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalKeptBlockInverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalWithoutPrivateUnitInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalIntervalWithoutPrivateUnitInverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_unit_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_unit_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_filtered_cap_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_filtered_cap_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_cap_interval_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_cap_interval_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.profile_normalized_lower_private_boundaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.profile_normalized_lower_private_boundaries

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.profile_normalized_upper_private_boundaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.profile_normalized_upper_private_boundaries

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_window_iff_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemaining_private_window_iff_bounds

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalFilteredCapInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalFilteredCapInverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_filtered_cap_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_filtered_cap_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalFilteredCap_projection_of_contained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalFilteredCap_projection_of_contained

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivatePeriod_top_eq_cap_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivatePeriod_top_eq_cap_sum

/-- info: 'SkewCornerDescent.Matrix.separatedBelowInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.separatedBelowInverse

/-- info: 'SkewCornerDescent.Matrix.separatedAboveInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.separatedAboveInverse

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_le_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.profileInverseProjection_le_retained

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_ge_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.profileInverseProjection_ge_retained

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerPrivateCapEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLowerPrivateCapEquiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperPrivateCapEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalUpperPrivateCapEquiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_lower_cap_without_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_lower_cap_without_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_upper_cap_without_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_upper_cap_without_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_lower_cap_with_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_lower_cap_with_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_upper_cap_with_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_upper_cap_with_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryPrivate_lower_cap_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryPrivate_lower_cap_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryPrivate_upper_cap_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryPrivate_upper_cap_projection

/-- info: 'SkewCornerDescent.Matrix.private_diagonal_of_no_interior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.private_diagonal_of_no_interior

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_phase_chain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_phase_chain

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_private_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_private_boundary

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateLower_cap_coordinates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateLower_cap_coordinates

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateUpper_cap_coordinates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateUpper_cap_coordinates

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_profile_join_private'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_profile_join_private

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_lower_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_lower_window

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_upper_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_upper_window

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_join_no_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_join_no_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalEqualWindow_lower_cap_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalEqualWindow_lower_cap_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalEqualWindow_upper_cap_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalEqualWindow_upper_cap_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_half_cap_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_half_cap_projection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_join_projection_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_join_projection_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_join_projection_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_join_projection_upper

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateJoin_comparison_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateJoin_comparison_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateJoin_comparison_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateJoin_comparison_upper

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivatePeriod_comparison_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivatePeriod_comparison_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivatePeriod_comparison_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivatePeriod_comparison_upper

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_laurent_normalized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_laurent_normalized

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_closure_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_closure_copy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_phase_hessian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_phase_hessian

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_phase_hessian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_phase_hessian

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivate_lower_hessian_pin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivate_lower_hessian_pin

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivate_upper_hessian_pin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivate_upper_hessian_pin

/-- info: 'SkewCornerDescent.CyclicWindows.closureWord_private_boundary'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.closureWord_private_boundary

/-- info: 'SkewCornerDescent.CyclicWindows.finiteWord_private_boundary'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.finiteWord_private_boundary

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivate_boundary_active'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivate_boundary_active

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_middle_local_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_middle_local_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTrueCapProduct_hessian_source_order'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalTrueCapProduct_hessian_source_order

/-- info: 'SkewCornerDescent.Matrix.residue_affine_label_of_mixed_difference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.residue_affine_label_of_mixed_difference

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_closure_plane_pin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_closure_plane_pin

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPinnedSupport_alternative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPinnedSupport_alternative

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_interior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_interior

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_components'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_components

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_join_private'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_join_private

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_content_extrema'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_content_extrema

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_profile_content'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_profile_content

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_lower_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_lower_window

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_upper_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_upper_window

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_selected_normalized_cells'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_selected_normalized_cells

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_retained_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_retained_endpoints

/-- info: 'SkewCornerDescent.Matrix.originalVerticalClosure_profile_join_private'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.originalVerticalClosure_profile_join_private

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_join_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_join_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_join_interval_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_join_interval_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleteWindow_cap_vectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleteWindow_cap_vectors

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_half_cap_vectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_half_cap_vectors

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_half_cap_vectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_half_cap_vectors

/-- info: 'SkewCornerDescent.Matrix.private_nonunit_sides_equiv'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.private_nonunit_sides_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_half_cap_vectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_half_cap_vectors

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_private_cap_vectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_private_cap_vectors

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateInterval_cap_vectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrivateInterval_cap_vectors

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_join_nonunit_vectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_join_nonunit_vectors

/-- info: 'SkewCornerDescent.Matrix.vertexBetaResponse_affine_reindex'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.vertexBetaResponse_affine_reindex

/-- info: 'SkewCornerDescent.Matrix.vertexBetaResponse_unit_insert'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.vertexBetaResponse_unit_insert

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_unit_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_private_unit_response

/-- info: 'SkewCornerDescent.Matrix.vertexBetaResponse_into_cut'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.vertexBetaResponse_into_cut

/-- info: 'SkewCornerDescent.Matrix.vertexBetaResponse_out_of_cut'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.vertexBetaResponse_out_of_cut

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_into_cut_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_into_cut_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_out_of_cut_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_out_of_cut_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_response_correction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_response_correction

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_local_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_local_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_central_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_central_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_plane_actual_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_plane_actual_response
