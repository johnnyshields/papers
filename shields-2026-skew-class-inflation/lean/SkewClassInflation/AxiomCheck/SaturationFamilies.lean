/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationBoundaryRigidity
import SkewClassInflation.SaturationSplitPositions
import SkewClassInflation.SaturationTheorem

/-!
# Exact SaturationFamilies axiom footprints

Every expected message is the observed kernel footprint of the declaration it guards.
-/

/-- info: 'SkewClassInflation.contractAllMinimum_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_span

/-- info: 'SkewClassInflation.first_upper_not_shifted_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.first_upper_not_shifted_column

/-- info: 'SkewClassInflation.first_lower_not_shifted_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.first_lower_not_shifted_row

/-- info: 'SkewClassInflation.contractAllMinimum_first_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_first_row

/-- info: 'SkewClassInflation.contractAllMinimum_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_rotate

/-- info: 'SkewClassInflation.contractAllMinimum_rows_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_rows_above

/-- info: 'SkewClassInflation.contract_distinguished_residualSets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_distinguished_residualSets

/-- info: 'SkewClassInflation.contractAllMinimum_residualSets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_residualSets

/-- info: 'SkewClassInflation.contractAllMinimum_sets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_sets

/-- info: 'SkewClassInflation.contractAllMinimum_shifted_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_shifted_colSet

/-- info: 'SkewClassInflation.distinguished_cut_reassembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_cut_reassembly

/-- info: 'SkewClassInflation.contractAllMinimum_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllMinimum_self

/-- info: 'SkewClassInflation.exists_first_distinguished' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_first_distinguished

/-- info: 'SkewClassInflation.distinguished_not_mem_of_gap_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_not_mem_of_gap_ne

/-- info: 'SkewClassInflation.distinguished_join_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_join_constant

/-- info: 'SkewClassInflation.distinguished_merge_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_merge_rowSet

/-- info: 'SkewClassInflation.distinguished_merge_shifted_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_merge_shifted_colSet

/-- info: 'SkewClassInflation.profile_rowSet_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_rowSet_above

/-- info: 'SkewClassInflation.profile_shifted_colSet_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_shifted_colSet_below

/-- info: 'SkewClassInflation.distinguished_prefix_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_prefix_contraction

/-- info: 'SkewClassInflation.SaturationInner.equalGapDouble_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.equalGapDouble_thick

/-- info: 'SkewClassInflation.SaturationInner.equalGapDouble_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.equalGapDouble_gaps

/-- info: 'SkewClassInflation.SaturationInner.equalGapDouble_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.equalGapDouble_rows

/-- info: 'SkewClassInflation.ambiguous_zero_parent_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_zero_parent_full_class

/-- info: 'SkewClassInflation.ambiguous_one_parent_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_one_parent_full_class

/-- info: 'SkewClassInflation.SaturationInner.merge_power_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.merge_power_chain

/-- info: 'SkewClassInflation.SaturationInner.chain_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_first

/-- info: 'SkewClassInflation.SaturationInner.chain_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_row_count

/-- info: 'SkewClassInflation.SaturationInner.chain_first_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_first_gap

/-- info: 'SkewClassInflation.SaturationInner.chain_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_thick

/-- info: 'SkewClassInflation.SaturationInner.diagram_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_row_count

/-- info: 'SkewClassInflation.SaturationInner.diagram_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_thick

/-- info: 'SkewClassInflation.SaturationInner.diagram_eq_rotated_implies_palindrome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_eq_rotated_implies_palindrome

/-- info: 'SkewClassInflation.SaturationInner.inner_symmetric_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.inner_symmetric_iff

/-- info: 'SkewClassInflation.SaturationInner.orientations_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.orientations_disjoint

/-- info: 'SkewClassInflation.SaturationInner.rotated_diagram_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.rotated_diagram_injective

/-- info: 'SkewClassInflation.SaturationInner.power_rotate_of_palindrome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_rotate_of_palindrome

/-- info: 'SkewClassInflation.SaturationInner.full_class_of_palindrome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.full_class_of_palindrome

/-- info: 'SkewClassInflation.SaturationInner.full_class_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.full_class_finite

/-- info: 'SkewClassInflation.SaturationInner.full_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.full_class_card

/-- info: 'SkewClassInflation.SaturationInner.power_one_column_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_one_column_bounds

/-- info: 'SkewClassInflation.SaturationInner.power_column_zero_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_column_zero_residue

/-- info: 'SkewClassInflation.SaturationInner.chain_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_span

/-- info: 'SkewClassInflation.SaturationInner.chain_column_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_column_multiple

/-- info: 'SkewClassInflation.SaturationInner.diagram_column_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_column_multiple

/-- info: 'SkewClassInflation.SaturationInner.diagram_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_injective

/-- info: 'SkewClassInflation.SaturationInner.chain_compose_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_compose_eq_source

/-- info: 'SkewClassInflation.SaturationInner.diagram_compose_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_compose_eq_source

/-- info: 'SkewClassInflation.SaturationInner.literal_legal_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.literal_legal_chart

/-- info: 'SkewClassInflation.SaturationInner.chain_large_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_large_multiplicity

/-- info: 'SkewClassInflation.SaturationInner.chain_large_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_large_degree

/-- info: 'SkewClassInflation.SaturationInner.chain_highest_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_highest_coefficient

/-- info: 'SkewClassInflation.SaturationInner.diagram_highest_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_highest_coefficient

/-- info: 'SkewClassInflation.SaturationInner.arbitrary_mate_total_contraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.arbitrary_mate_total_contraction

/-- info: 'SkewClassInflation.SaturationInner.power_excludes_large_label' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_excludes_large_label

/-- info: 'SkewClassInflation.SaturationInner.powerFunctions_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.powerFunctions_cons

/-- info: 'SkewClassInflation.SaturationInner.chain_constant_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_constant_coefficient

/-- info: 'SkewClassInflation.SaturationInner.diagram_constant_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_constant_coefficient

/-- info: 'SkewClassInflation.SaturationInner.blockInventory_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.blockInventory_connected

/-- info: 'SkewClassInflation.SaturationInner.blockInventory_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.blockInventory_product

/-- info: 'SkewClassInflation.SaturationInner.arbitrary_mate_component_matching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.arbitrary_mate_component_matching

/-- info: 'SkewClassInflation.SaturationInner.arbitrary_mate_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.arbitrary_mate_geometry

/-- info: 'SkewClassInflation.SaturationInner.full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.full_class

/-- info: 'SkewClassInflation.SaturationInner.total_contraction_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.total_contraction_inverse

/-- info: 'SkewClassInflation.SaturationInner.full_class_ones' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.full_class_ones

/-- info: 'SkewClassInflation.SaturationInner.chain_gap_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_gap_product

/-- info: 'SkewClassInflation.SaturationInner.chain_gap_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_gap_sum

/-- info: 'SkewClassInflation.SaturationInner.diagram_gap_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_gap_product

/-- info: 'SkewClassInflation.SaturationInner.diagram_gap_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_gap_sum

/-- info: 'SkewClassInflation.SaturationInner.diagram_small_gap_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_small_gap_count

/-- info: 'SkewClassInflation.SaturationInner.diagram_large_gap_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_large_gap_count

/-- info: 'SkewClassInflation.SaturationInner.diagram_cofactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_cofactor

/-- info: 'SkewClassInflation.SaturationInner.diagram_corner_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_corner_coefficient

/-- info: 'SkewClassInflation.SaturationInner.power_first_inner_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_first_inner_rows

/-- info: 'SkewClassInflation.SaturationInner.power_last_inner_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_last_inner_rows

/-- info: 'SkewClassInflation.SaturationInner.chain_order_ge_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_order_ge_inner

/-- info: 'SkewClassInflation.SaturationInner.chain_first_inner_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_first_inner_rows

/-- info: 'SkewClassInflation.SaturationInner.chain_last_inner_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_last_inner_rows

/-- info: 'SkewClassInflation.SaturationInner.diagram_order_ge_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_order_ge_inner

/-- info: 'SkewClassInflation.SaturationInner.diagram_first_inner_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_first_inner_rows

/-- info: 'SkewClassInflation.SaturationInner.diagram_last_inner_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_last_inner_rows

/-- info: 'SkewClassInflation.SaturationInner.chain_total_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_total_contraction

/-- info: 'SkewClassInflation.SaturationInner.diagram_total_contraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_total_contraction

/-- info: 'SkewClassInflation.SaturationInner.fractionLift_algebraMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.fractionLift_algebraMap

/-- info: 'SkewClassInflation.SaturationInner.normalizationLift_algebraMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalizationLift_algebraMap

/-- info: 'SkewClassInflation.SaturationInner.fractionLift_invSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.fractionLift_invSelf

/-- info: 'SkewClassInflation.SaturationInner.normalizationLift_invSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalizationLift_invSelf

/-- info: 'SkewClassInflation.SaturationInner.fractionLift_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.fractionLift_injective

/-- info: 'SkewClassInflation.SaturationInner.fractionLift_comp_substitution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.fractionLift_comp_substitution

/-- info: 'SkewClassInflation.SaturationInner.normalizationLift_comp_substitution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalizationLift_comp_substitution

/-- info: 'SkewClassInflation.SaturationInner.localizedSubstitution_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.localizedSubstitution_injective

/-- info: 'SkewClassInflation.SaturationInner.diagram_schur_eq_iff_ribbon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_schur_eq_iff_ribbon

/-- info: 'SkewClassInflation.SaturationInner.innerCells_minContent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.innerCells_minContent

/-- info: 'SkewClassInflation.SaturationInner.innerCells_maxContent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.innerCells_maxContent

/-- info: 'SkewClassInflation.SaturationInner.marked_middle_content_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.marked_middle_content_bounds

/-- info: 'SkewClassInflation.SaturationInner.lower_middle_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.lower_middle_mem

/-- info: 'SkewClassInflation.SaturationInner.upper_middle_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.upper_middle_mem

/-- info: 'SkewClassInflation.SaturationInner.markedInner_lowerH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_lowerH

/-- info: 'SkewClassInflation.SaturationInner.markedInner_upperH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_upperH

/-- info: 'SkewClassInflation.SaturationInner.markedInner_attachmentMatches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_attachmentMatches

/-- info: 'SkewClassInflation.SaturationInner.markedInner_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_wellFormed

/-- info: 'SkewClassInflation.SaturationInner.markedInner_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_maximal

/-- info: 'SkewClassInflation.SaturationInner.periodic_mark_diagonals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.periodic_mark_diagonals

/-- info: 'SkewClassInflation.SaturationInner.markedInner_hatMark_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_hatMark_empty

/-- info: 'SkewClassInflation.SaturationInner.markedInner_noHatAdjacency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_noHatAdjacency

/-- info: 'SkewClassInflation.SaturationInner.lower_attachmentCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.lower_attachmentCells

/-- info: 'SkewClassInflation.SaturationInner.upper_attachmentCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.upper_attachmentCells

/-- info: 'SkewClassInflation.SaturationInner.markedInner_hypothesisV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_hypothesisV

/-- info: 'SkewClassInflation.SaturationInner.markedInner_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_legal

/-- info: 'SkewClassInflation.SaturationInner.removedLowerProfile_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.removedLowerProfile_beta

/-- info: 'SkewClassInflation.SaturationInner.removedUpperProfile_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.removedUpperProfile_beta

/-- info: 'SkewClassInflation.SaturationInner.lower_mark_removal_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.lower_mark_removal_cells

/-- info: 'SkewClassInflation.SaturationInner.upper_mark_removal_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.upper_mark_removal_cells

/-- info: 'SkewClassInflation.SaturationInner.markedInner_removalsConnected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_removalsConnected

/-- info: 'SkewClassInflation.SaturationInner.mem_innerCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.mem_innerCells

/-- info: 'SkewClassInflation.SaturationInner.mem_lowerMark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.mem_lowerMark

/-- info: 'SkewClassInflation.SaturationInner.mem_upperMark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.mem_upperMark

/-- info: 'SkewClassInflation.SaturationInner.mem_inner_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.mem_inner_bottom

/-- info: 'SkewClassInflation.SaturationInner.mem_inner_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.mem_inner_top

/-- info: 'SkewClassInflation.SaturationInner.lowerMark_content_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.lowerMark_content_bounds

/-- info: 'SkewClassInflation.SaturationInner.upperMark_content_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.upperMark_content_bounds

/-- info: 'SkewClassInflation.SaturationInner.lower_content_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.lower_content_margin

/-- info: 'SkewClassInflation.SaturationInner.upper_content_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.upper_content_margin

/-- info: 'SkewClassInflation.SaturationInner.inner_span_gt_twice_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.inner_span_gt_twice_seam

/-- info: 'SkewClassInflation.SaturationInner.inner_content_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.inner_content_bounds

/-- info: 'SkewClassInflation.SaturationInner.lower_mark_of_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.lower_mark_of_content

/-- info: 'SkewClassInflation.SaturationInner.upper_mark_of_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.upper_mark_of_content

/-- info: 'SkewClassInflation.SaturationInner.markedInner_subsets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_subsets

/-- info: 'SkewClassInflation.SaturationInner.innerCells_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.innerCells_connected

/-- info: 'SkewClassInflation.SaturationInner.lowerMark_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.lowerMark_connected

/-- info: 'SkewClassInflation.SaturationInner.markedInner_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_width

/-- info: 'SkewClassInflation.SaturationInner.markedInner_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_period

/-- info: 'SkewClassInflation.SaturationInner.markedInner_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_narrow

/-- info: 'SkewClassInflation.SaturationInner.power_mate_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_mate_reduction

/-- info: 'SkewClassInflation.SaturationInner.merged_power_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.merged_power_inverse

/-- info: 'SkewClassInflation.SaturationInner.merged_power_inverse_of_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.merged_power_inverse_of_function

/-- info: 'SkewClassInflation.SaturationInner.normalizeSeams_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalizeSeams_complete

/-- info: 'SkewClassInflation.SaturationInner.normalizeSeams_vars_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalizeSeams_vars_subset

/-- info: 'SkewClassInflation.SaturationInner.privateLabel_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.privateLabel_value

/-- info: 'SkewClassInflation.SaturationInner.privateLabel_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.privateLabel_strictMono

/-- info: 'SkewClassInflation.SaturationInner.privateLabel_above_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.privateLabel_above_seam

/-- info: 'SkewClassInflation.SaturationInner.normalizeSeams_privateLabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalizeSeams_privateLabel

/-- info: 'SkewClassInflation.SaturationInner.normalized_power_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalized_power_corner

/-- info: 'SkewClassInflation.SaturationInner.normalized_residual_vars_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalized_residual_vars_lt

/-- info: 'SkewClassInflation.SaturationInner.normalized_power_private_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalized_power_private_degree

/-- info: 'SkewClassInflation.SaturationInner.normalized_power_later_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalized_power_later_degree

/-- info: 'SkewClassInflation.SaturationInner.normalized_substitution_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.normalized_substitution_injective

/-- info: 'SkewClassInflation.SaturationInner.ribbonFirstBlock_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.ribbonFirstBlock_word

/-- info: 'SkewClassInflation.SaturationInner.ribbon_middle_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.ribbon_middle_positive

/-- info: 'SkewClassInflation.SaturationInner.overlapWord_merged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.overlapWord_merged

/-- info: 'SkewClassInflation.SaturationInner.ribbonRepeatBlock_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.ribbonRepeatBlock_word

/-- info: 'SkewClassInflation.SaturationInner.power_deflated_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_deflated_blocks

/-- info: 'SkewClassInflation.SaturationInner.power_deflated_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_deflated_word

/-- info: 'SkewClassInflation.SaturationInner.powerRibbonComposition_eq_overlap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.powerRibbonComposition_eq_overlap

/-- info: 'SkewClassInflation.SaturationInner.powerRibbonComposition_no_right_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.powerRibbonComposition_no_right_factor

/-- info: 'SkewClassInflation.SaturationInner.power_mate_overlap_ribbon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_mate_overlap_ribbon

/-- info: 'SkewClassInflation.SaturationInner.oriented_profile_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.oriented_profile_reconstruction

/-- info: 'SkewClassInflation.SaturationInner.powerFunctions_are_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.powerFunctions_are_actual

/-- info: 'SkewClassInflation.SaturationInner.connected_factor_of_power_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.connected_factor_of_power_product

/-- info: 'SkewClassInflation.SaturationInner.merge_powers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.merge_powers

/-- info: 'SkewClassInflation.SaturationInner.power_mate_eq_or_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_mate_eq_or_rotate

/-- info: 'SkewClassInflation.SaturationInner.power_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_full_class

/-- info: 'SkewClassInflation.SaturationInner.merger_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.merger_bound

/-- info: 'SkewClassInflation.SaturationInner.row_above_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.row_above_gap

/-- info: 'SkewClassInflation.SaturationInner.powerRows_above_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.powerRows_above_gap

/-- info: 'SkewClassInflation.SaturationInner.power_interior_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_interior_bound

/-- info: 'SkewClassInflation.SaturationInner.power_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_thick

/-- info: 'SkewClassInflation.SaturationInner.power_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_first

/-- info: 'SkewClassInflation.SaturationInner.power_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_last

/-- info: 'SkewClassInflation.SaturationInner.power_rows_above_seam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_rows_above_seam

/-- info: 'SkewClassInflation.SaturationInner.power_cofactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_cofactor

/-- info: 'SkewClassInflation.SaturationInner.power_one_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_one_rows

/-- info: 'SkewClassInflation.SaturationInner.power_one_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_one_word

/-- info: 'SkewClassInflation.SaturationInner.power_one_deflated_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_one_deflated_word

/-- info: 'SkewClassInflation.SaturationInner.diagram_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_single

/-- info: 'SkewClassInflation.SaturationInner.diagram_eq_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_eq_chain

/-- info: 'SkewClassInflation.SaturationInner.chain_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_blocks

/-- info: 'SkewClassInflation.SaturationInner.diagram_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_prepend

/-- info: 'SkewClassInflation.SaturationInner.power_corner_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_corner_expansion

/-- info: 'SkewClassInflation.SaturationInner.power_mate_ribbon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_mate_ribbon

/-- info: 'SkewClassInflation.SaturationInner.power_mate_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_mate_endpoints

/-- info: 'SkewClassInflation.SaturationInner.power_one_profile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_one_profile

/-- info: 'SkewClassInflation.SaturationInner.power_one_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_one_cells

/-- info: 'SkewClassInflation.SaturationInner.markedInner_origin_east' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_origin_east

/-- info: 'SkewClassInflation.SaturationInner.markedInner_origin_north' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.markedInner_origin_north

/-- info: 'SkewClassInflation.SaturationInner.row_compose_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.row_compose_one

/-- info: 'SkewClassInflation.SaturationInner.row_compose_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.row_compose_succ

/-- info: 'SkewClassInflation.SaturationInner.row_compose_eq_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.row_compose_eq_power

/-- info: 'SkewClassInflation.SaturationInner.chain_rows_above_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_rows_above_seam

/-- info: 'SkewClassInflation.SaturationInner.chain_gap_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_gap_values

/-- info: 'SkewClassInflation.SaturationInner.diagram_rows_above_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_rows_above_seam

/-- info: 'SkewClassInflation.SaturationInner.diagram_gap_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_gap_values

/-- info: 'SkewClassInflation.SaturationInner.source_mate_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.source_mate_reduction

/-- info: 'SkewClassInflation.compositionPrefix_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionPrefix_length

/-- info: 'SkewClassInflation.SaturationInner.power_split_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_split_row

/-- info: 'SkewClassInflation.SaturationInner.prefix_core_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.prefix_core_row_count

/-- info: 'SkewClassInflation.SaturationInner.prefix_split_position' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.prefix_split_position

/-- info: 'SkewClassInflation.SaturationInner.chain_schur_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_schur_recurrence

/-- info: 'SkewClassInflation.SaturationInner.large_generator_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.large_generator_nonzero

/-- info: 'SkewClassInflation.SaturationInner.localizedSubstitution_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.localizedSubstitution_complete

/-- info: 'SkewClassInflation.SaturationInner.chain_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_substitution

/-- info: 'SkewClassInflation.SaturationInner.diagram_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_substitution

/-- info: 'SkewClassInflation.SaturationInner.diagram_schur_eq_of_ribbon_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_schur_eq_of_ribbon_eq

/-- info: 'SkewClassInflation.SaturationInner.prescribed_class_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.prescribed_class_subset

/-- info: 'SkewClassInflation.SaturationInner.power_deflated_palindrome_of_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_deflated_palindrome_of_base

/-- info: 'SkewClassInflation.SaturationInner.power_mate_eq_of_symmetric_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_mate_eq_of_symmetric_inner

/-- info: 'SkewClassInflation.SaturationInner.power_full_class_of_symmetric_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_full_class_of_symmetric_inner

/-- info: 'SkewClassInflation.SaturationInner.power_one_deflated_palindrome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_one_deflated_palindrome

/-- info: 'SkewClassInflation.SaturationInner.power_full_class_of_palindromic_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_full_class_of_palindromic_inner

/-- info: 'SkewClassInflation.SaturationInner.every_mate_legal_presentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.every_mate_legal_presentation

/-- info: 'SkewClassInflation.SaturationInner.repeated_block_saturation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.repeated_block_saturation

/-- info: 'SkewClassInflation.SaturationInner.arbitrary_mate_total_core_rigidity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.arbitrary_mate_total_core_rigidity

/-- info: 'SkewClassInflation.SaturationInner.arbitrary_mate_total_core_row_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.arbitrary_mate_total_core_row_count

/-- info: 'SkewClassInflation.SaturationInner.power_row_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_row_weight

/-- info: 'SkewClassInflation.SaturationInner.chain_row_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.chain_row_weight

/-- info: 'SkewClassInflation.SaturationInner.diagram_row_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_row_weight

/-- info: 'SkewClassInflation.SaturationInner.spanIncrement_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.spanIncrement_pos

/-- info: 'SkewClassInflation.SaturationInner.power_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_span

/-- info: 'SkewClassInflation.SaturationInner.power_largest_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.power_largest_label

/-- info: 'SkewClassInflation.SaturationInner.diagram_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_span

/-- info: 'SkewClassInflation.SaturationInner.diagram_largest_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_largest_label

/-- info: 'SkewClassInflation.SaturationInner.diagram_maximal_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.SaturationInner.diagram_maximal_derivative

