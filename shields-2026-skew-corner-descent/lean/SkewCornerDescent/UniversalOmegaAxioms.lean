/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalColumnPlaneLabels
import SkewCornerDescent.FiniteCapComparison
import SkewCornerDescent.OrdinaryGauge
import SkewCornerDescent.Matrix.ProjectionTransport
import SkewCornerDescent.Matrix.OppositeEndpointProfiles

/-!
# Axiom guards for whole-diagram and compatible-matrix transport

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`,
`lem:shared-core`, `rem:ordinary-gauge`, `rem:comparison-v`).
Pins generated footprints for full polynomial transpose, actual residue fields,
complete cap comparisons, and integral common-core determinant divisibility.
-/

/-- info: 'SkewCornerDescent.universal_elementary_eq_recursive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.universal_elementary_eq_recursive

/-- info: 'SkewCornerDescent.evalComplete_comp_schurInvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.evalComplete_comp_schurInvolution

/-- info: 'SkewCornerDescent.aeval_elementary_profile_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.aeval_elementary_profile_schur

/-- info: 'SkewCornerDescent.schurInvolution_cellSchur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.schurInvolution_cellSchur

/-- info: 'SkewCornerDescent.schurInvolution_skew_cellSchur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.schurInvolution_skew_cellSchur

/-- info: 'SkewCornerDescent.all_column_corner_transpose_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.all_column_corner_transpose_rows

/-- info: 'SkewCornerDescent.corner_power_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.corner_power_transpose

/-- info: 'SkewCornerDescent.primeOrder_schurInvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.primeOrder_schurInvolution

/-- info: 'SkewCornerDescent.polynomialSpan_schurInvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.polynomialSpan_schurInvolution

/-- info: 'SkewCornerDescent.schurInvolution_mem_supported_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.schurInvolution_mem_supported_below

/-- info: 'SkewCornerDescent.originalSchurFieldEquiv_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.originalSchurFieldEquiv_involutive

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residueTranspose_residueMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.residueTranspose_residueMap

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residueTranspose_left_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.residueTranspose_left_inverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residueTranspose_right_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.residueTranspose_right_inverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.rational_residue_match_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.rational_residue_match_transpose

/-- info: 'SkewCornerDescent.complete_profile_window_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.complete_profile_window_transpose

/-- info: 'SkewCornerDescent.complete_transpose_private_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.complete_transpose_private_cuts

/-- info: 'SkewCornerDescent.complete_overlap_union_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.complete_overlap_union_transpose

/-- info: 'SkewCornerDescent.exists_transposed_selectedCoordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.exists_transposed_selectedCoordinate

/-- info: 'SkewCornerDescent.vertical_closure_transpose_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.vertical_closure_transpose_profile

/-- info: 'SkewCornerDescent.empty_closure_schur_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.empty_closure_schur_complement

/-- info: 'SkewCornerDescent.rationalReflection_isCoprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.rationalReflection_isCoprime

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.regularTransposeEquiv_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.regularTransposeEquiv_residue

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.regularTransposeEquiv_originalField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.regularTransposeEquiv_originalField

/-- info: 'SkewCornerDescent.signedRational_root_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.signedRational_root_support

/-- info: 'SkewCornerDescent.rationalReflection_root_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.rationalReflection_root_union

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_normalized_complement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosures_normalized_complement

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_rational_match_transpose_horizontal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_rational_match_transpose_horizontal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_plane_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_plane_labels

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_residue_mem_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_residue_mem_classes

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_signed_support_label_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_signed_support_label_exists

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_active_rational_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_active_rational_roots

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_row_rational_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_row_rational_roots

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_block_transpose_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_block_transpose_exists

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_block_transpose_exists_reverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_block_transpose_exists_reverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_cap_tops_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_cap_tops_transpose

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_cap_coincidence_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_cap_coincidence_transpose

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_column_plane_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_column_plane_labels

/-- info: 'SkewCornerDescent.nonVMark_finite_caps_ne_two_hats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_finite_caps_ne_two_hats

/-- info: 'SkewCornerDescent.nonVMark_one_row_cofactor_ne_two_hats' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_one_row_cofactor_ne_two_hats

/-- info: 'SkewCornerDescent.nonVVerticalMarkFour_isLegal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.nonVVerticalMarkFour_isLegal

/-- info: 'SkewCornerDescent.nonVFour_compose_gauge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.nonVFour_compose_gauge

/-- info: 'SkewCornerDescent.two_cell_outer_functions_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.two_cell_outer_functions_ne

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_reindex_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.profileInverseProjection_reindex_translate

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_eq_zero_of_rows_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.profileInverseProjection_eq_zero_of_rows_lt

/-- info: 'SkewCornerDescent.Matrix.profileInverseProjection_eq_zero_of_cols_gt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.profileInverseProjection_eq_zero_of_cols_gt

/-- info: 'SkewCornerDescent.Matrix.det_option_expand_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.det_option_expand_row

/-- info: 'SkewCornerDescent.Matrix.det_option_expand_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.det_option_expand_column

/-- info: 'SkewCornerDescent.Matrix.borderedCore_det_left_option_expand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.borderedCore_det_left_option_expand

/-- info: 'SkewCornerDescent.Matrix.commonCoreDifference_left_option_expand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCoreDifference_left_option_expand

/-- info: 'SkewCornerDescent.Matrix.commonCoreDifference_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCoreDifference_dual

/-- info: 'SkewCornerDescent.Matrix.commonCoreDifference_left_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCoreDifference_left_equiv

/-- info: 'SkewCornerDescent.Matrix.singleCoreBorder_cross_difference_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.singleCoreBorder_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.singleCoreBorderSum_cross_difference_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.singleCoreBorderSum_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.commonCoreDifference_empty_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCoreDifference_empty_dvd

/-- info: 'SkewCornerDescent.Matrix.commonCoreDifference_left_induction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCoreDifference_left_induction

/-- info: 'SkewCornerDescent.Matrix.commonCoreDifference_right_empty_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCoreDifference_right_empty_dvd

/-- info: 'SkewCornerDescent.Matrix.commonCoreDifference_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.commonCoreDifference_dvd

/-- info: 'SkewCornerDescent.Matrix.endpointCoreFrame_eq_originalProfileFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.endpointCoreFrame_eq_originalProfileFrame

/-- info: 'SkewCornerDescent.Matrix.endpointCoreFrame_eq_bordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.endpointCoreFrame_eq_bordered

/-- info: 'SkewCornerDescent.Matrix.endpointCore_cross_difference_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.endpointCore_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.endpointCoreFrame_base_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.endpointCoreFrame_base_profile

/-- info: 'SkewCornerDescent.Matrix.oppositeEndpointProfiles_cross_difference_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.oppositeEndpointProfiles_cross_difference_dvd

/-- info: 'SkewCornerDescent.Matrix.single_row_source_cross_difference_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.single_row_source_cross_difference_dvd
