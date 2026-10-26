/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ComponentElimination
import SkewCornerDescent.Matrix.OriginalHorizontalSplice
import SkewCornerDescent.Matrix.OriginalPolynomialResponses
import SkewCornerDescent.Matrix.OriginalEndpointProfiles
import SkewCornerDescent.Matrix.OriginalClosureResponse

/-! # Observed axiom footprints of original interior blocks -/

/--
info: 'SkewCornerDescent.Matrix.interior_polynomial_blockTriangular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_polynomial_blockTriangular

/--
info: 'SkewCornerDescent.Matrix.interiorBlock_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorBlock_interval

/--
info: 'SkewCornerDescent.Matrix.interior_empty_row_isolated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_empty_row_isolated

/--
info: 'SkewCornerDescent.Matrix.interior_empty_row_pivot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_empty_row_pivot

/--
info: 'SkewCornerDescent.Matrix.interiorSliceProfile_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorSliceProfile_matrix

/--
info: 'SkewCornerDescent.Matrix.mem_interiorBlockFiber_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.mem_interiorBlockFiber_iff

/--
info: 'SkewCornerDescent.Matrix.interiorBlock_slice_same' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorBlock_slice_same

/--
info: 'SkewCornerDescent.Matrix.interiorSliceCells_eq_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorSliceCells_eq_translate

/--
info: 'SkewCornerDescent.Matrix.interiorSliceCells_connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorSliceCells_connected

/--
info: 'SkewCornerDescent.Matrix.interiorSliceCells_eq_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorSliceCells_eq_filter

/--
info: 'SkewCornerDescent.Matrix.interior_components_eq_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_components_eq_blocks

/--
info: 'SkewCornerDescent.Matrix.interior_edgeComponents_eq_image' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_edgeComponents_eq_image

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_schur' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorBlockCells_schur

/--
info: 'SkewCornerDescent.Matrix.interior_block_det_eq_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_block_det_eq_profile

/--
info: 'SkewCornerDescent.Matrix.interior_det_eq_block_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_det_eq_block_product

/--
info: 'SkewCornerDescent.Matrix.interior_empty_block_det' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_empty_block_det

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalBlock

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.dvd_originalBlock_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.dvd_originalBlock_iff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalEmptyBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalEmptyBlock

/--
info: 'SkewCornerDescent.Matrix.originalSelectedMinor_eq_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalSelectedMinor_eq_profile

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalSelectedMinor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalSelectedMinor

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_blockTriangular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_blockTriangular

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalRemovedDiagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalRemovedDiagonal

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalRemovedMatrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalRemovedMatrix

/--
info: 'SkewCornerDescent.Matrix.originalBlockIndex_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalBlockIndex_injective

/--
info: 'SkewCornerDescent.Matrix.originalBlockIndex_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalBlockIndex_surjective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.complementaryRowPartition_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.complementaryRowPartition_injective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.complementaryRowPartition_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.complementaryRowPartition_surjective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.complementaryColPartition_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.complementaryColPartition_injective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.complementaryColPartition_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.complementaryColPartition_surjective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSplitMatrix_removed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSplitMatrix_removed

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSplitMatrix_local_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSplitMatrix_local_det

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSplitMatrix_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSplitMatrix_det

/--
info: 'SkewCornerDescent.Matrix.blockTriangular_inverse_toSquareBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.blockTriangular_inverse_toSquareBlock

/--
info: 'SkewCornerDescent.Matrix.inverseContraction_same_block' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.inverseContraction_same_block

/--
info: 'SkewCornerDescent.Matrix.map_inverseContraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.map_inverseContraction

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_selected_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_selected_zero

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_diagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_diagonal

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_diagonal_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_diagonal_embedding

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_eq_componentResponse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_eq_componentResponse

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_eq_selected_quotient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_eq_selected_quotient

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_diagonal_residue_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_diagonal_residue_zero

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_isUpperHessenberg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_isUpperHessenberg

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_subdiagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_subdiagonal

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_residue_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_residue_det

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_local_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_local_det

/--
info: 'SkewCornerDescent.Matrix.interior_block_endpoint_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_block_endpoint_separation

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_endpoint_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_endpoint_distance

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalFirstCapDistance_gt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalFirstCapDistance_gt_top

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLastCapDistance_gt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLastCapDistance_gt_top

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_gap_gt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_gap_gt_top

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedRow_gt_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedRow_gt_selected

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedCol_lt_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedCol_lt_selected

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponse_incoming_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalResponse_incoming_cutoff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponse_outgoing_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalResponse_outgoing_cutoff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_embedding_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_embedding_interval

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_triangular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_triangular

/--
info: 'SkewCornerDescent.Matrix.profile_proper_minor_span_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.profile_proper_minor_span_lt

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_det_span_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_det_span_le

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_inverse_denominator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_inverse_denominator

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_inverse_geometric_denominator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_inverse_geometric_denominator

/--
info: 'SkewCornerDescent.Matrix.interior_singleton_block_det' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_singleton_block_det

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_top_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_top_eq

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_supported_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_supported_below

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_span_mem_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_span_mem_lower

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_contraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_contraction

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_triangular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_triangular

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_transcendental' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_transcendental

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_residue_lower_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_residue_lower_scalar

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_factorization

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_gt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_gt_top

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergTop_coe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergTop_coe

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_residue_triangular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_residue_triangular

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCount_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCount_pos

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_first

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_last

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_between' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_between

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergDistance_sum

/--
info: 'SkewCornerDescent.Matrix.interior_det_eq_original_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interior_det_eq_original_product

/--
info: 'SkewCornerDescent.Matrix.originalBlockPolynomial_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalBlockPolynomial_ne_zero

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlock_primeOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalBlock_primeOrder

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCount_eq_primeOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCount_eq_primeOrder

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCount_pos_of_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCount_pos_of_dvd

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.component_elimination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.component_elimination

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_minContent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorBlockCells_minContent

/--
info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_connected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_connected

/--
info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_interior

/--
info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_first_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_first_subset

/--
info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_second_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_second_subset

/--
info: 'SkewCornerDescent.Matrix.originalHorizontalDisplacement_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalDisplacement_content

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCapSpliceDistance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalCapSpliceDistance_eq

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCapSpliceDistance_cap_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalCapSpliceDistance_cap_sum

/--
info: 'SkewCornerDescent.Matrix.lowerGeneratorField_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.lowerGeneratorField_fraction

/--
info: 'SkewCornerDescent.Matrix.polynomialSpan_lt_of_supported' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.polynomialSpan_lt_of_supported

/--
info: 'SkewCornerDescent.Matrix.originalMap_mem_lower_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalMap_mem_lower_iff

/--
info: 'SkewCornerDescent.Matrix.inverseContraction_polynomial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.inverseContraction_polynomial_fraction

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_triangular_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_triangular_fraction

/--
info: 'SkewCornerDescent.Matrix.residueLowerField_mem_band' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueLowerField_mem_band

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_generator_mem_band' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_generator_mem_band

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_supported_mem_band' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_supported_mem_band

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.residue_fraction_mem_band' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.residue_fraction_mem_band

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_polynomial

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_residue_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenbergResponse_residue_polynomial

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponse_blockTriangular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalResponse_blockTriangular

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_embedding_pruned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_embedding_pruned

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_profiles_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_profiles_derivatives

/--
info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_components

/--
info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_component_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_component_disjoint

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_eq_of_label_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.interiorBlockCells_eq_of_label_eq

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.exists_originalSelectedBlock_of_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.exists_originalSelectedBlock_of_component

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.exists_originalSelectedBlock_of_translated_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.exists_originalSelectedBlock_of_translated_component

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_component_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_component_span

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_response
