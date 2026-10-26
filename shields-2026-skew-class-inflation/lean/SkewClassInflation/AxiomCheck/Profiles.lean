/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ConstantGapSubstitution
import SkewClassInflation.OrdinaryComposition
import SkewClassInflation.PeriodicCutPowers
import SkewClassInflation.PrivateCornerBounds
import SkewClassInflation.ProfileMergeInverse
import SkewClassInflation.ProfileRotationSets
import SkewClassInflation.RibbonCellChains
import SkewClassInflation.SaturationBoundaryExamples
import SkewClassInflation.SaturationExamples
import SkewClassInflation.ThresholdExampleProfiles
import SkewClassInflation.TriangularSubstitution
import SkewClassInflation.UnboundedSplitting

/-!
# Exact Profiles axiom footprints

Every expected message is the observed kernel footprint of the declaration it guards.
-/

/-- info: 'SkewClassInflation.binaryRibbonFactor_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonFactor_sum

/-- info: 'SkewClassInflation.binaryRibbonFactor_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonFactor_pos

/-- info: 'SkewClassInflation.binaryRibbonFactor_powerEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonFactor_powerEquiv

/-- info: 'SkewClassInflation.binaryRibbonWord_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonWord_sum

/-- info: 'SkewClassInflation.binaryRibbonWord_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonWord_pos

/-- info: 'SkewClassInflation.binaryRibbonWord_powerEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonWord_powerEquiv

/-- info: 'SkewClassInflation.binaryRibbonFactor_first_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonFactor_first_cut

/-- info: 'SkewClassInflation.binaryRibbonWord_head_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonWord_head_cut

/-- info: 'SkewClassInflation.binaryRibbonWord_internal_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbonWord_internal_cut

/-- info: 'SkewClassInflation.binaryRibbon_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbon_injective

/-- info: 'SkewClassInflation.binaryRibbon_mem_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbon_mem_class

/-- info: 'SkewClassInflation.binaryRibbon_class_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.binaryRibbon_class_lower_bound

/-- info: 'SkewJacobiNegative.strictAnti_add_index_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.strictAnti_add_index_antitone

/-- info: 'SkewJacobiNegative.BetaDiagram.bottomCol_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.bottomCol_le

/-- info: 'SkewJacobiNegative.BetaDiagram.translated_col_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.translated_col_nonneg

/-- info: 'SkewJacobiNegative.BetaDiagram.ofDiagram_toDiagram_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ofDiagram_toDiagram_translation

/-- info: 'SkewJacobiNegative.BetaDiagram.ofDiagram_connected_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ofDiagram_connected_iff

/-- info: 'SkewJacobiNegative.BetaDiagram.ofDiagram_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ofDiagram_matrix

/-- info: 'SkewJacobiNegative.BetaDiagram.ofDiagram_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.ofDiagram_schur

/-- info: 'SkewJacobiNegative.BetaDiagram.toDiagram_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.toDiagram_schur

/-- info: 'SkewClassInflation.boundary_realization_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.boundary_realization_connected

/-- info: 'SkewClassInflation.boundary_realization_tail_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.boundary_realization_tail_schur

/-- info: 'SkewClassInflation.boundary_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.boundary_reconstruction

/-- info: 'SkewClassInflation.reindexOrder_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.reindexOrder_rowSet

/-- info: 'SkewClassInflation.reindexOrder_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.reindexOrder_colSet

/-- info: 'SkewClassInflation.positive_grid_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.positive_grid_eq

/-- info: 'SkewClassInflation.arithmeticGrid_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.arithmeticGrid_shift

/-- info: 'SkewClassInflation.inflate_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflate_rowSet

/-- info: 'SkewClassInflation.inflate_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflate_colSet

/-- info: 'SkewClassInflation.gluingProfile_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.gluingProfile_xi

/-- info: 'SkewClassInflation.gluingProfile_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.gluingProfile_zeta

/-- info: 'SkewClassInflation.gluing_hh_eq_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.gluing_hh_eq_complete

/-- info: 'SkewClassInflation.gluingProfile_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.gluingProfile_schur

/-- info: 'SkewClassInflation.mem_profileCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mem_profileCells

/-- info: 'SkewClassInflation.profileCells_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_connected

/-- info: 'SkewClassInflation.profileCells_translation_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_translation_injective

/-- info: 'SkewClassInflation.profileCells_contents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_contents

/-- info: 'SkewClassInflation.profileCells_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_span

/-- info: 'SkewClassInflation.profile_span_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_span_sum

/-- info: 'SkewClassInflation.mem_twoRow_profileCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mem_twoRow_profileCells

/-- info: 'SkewClassInflation.positiveCutInventory_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.positiveCutInventory_connected

/-- info: 'SkewClassInflation.zeroCutInventory_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroCutInventory_connected

/-- info: 'SkewClassInflation.positiveCutInventory_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.positiveCutInventory_product

/-- info: 'SkewClassInflation.zeroCutInventory_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroCutInventory_product

/-- info: 'SkewClassInflation.positive_cut_inventory_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.positive_cut_inventory_matching

/-- info: 'SkewClassInflation.zero_cut_inventory_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_cut_inventory_matching

/-- info: 'SkewClassInflation.suffixSet_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.suffixSet_mem_iff

/-- info: 'SkewClassInflation.suffixSet_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.suffixSet_subset

/-- info: 'SkewClassInflation.suffixSet_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.suffixSet_injective

/-- info: 'SkewClassInflation.suffixSet_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.suffixSet_card

/-- info: 'SkewClassInflation.zero_gap_noOpening_of_inflate_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_gap_noOpening_of_inflate_thick

/-- info: 'SkewClassInflation.constant_gap_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.constant_gap_equality_iff

/-- info: 'SkewClassInflation.constantGap_denominator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.constantGap_denominator_ne_zero

/-- info: 'SkewClassInflation.constantGapSubstitution_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.constantGapSubstitution_complete

/-- info: 'SkewClassInflation.contract_first_deflated_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_first_deflated_word

/-- info: 'SkewClassInflation.contract_first_rows_above_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_first_rows_above_gap

/-- info: 'SkewClassInflation.constant_gap_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.constant_gap_substitution

/-- info: 'SkewClassInflation.distinguishedCutInventory_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguishedCutInventory_connected

/-- info: 'SkewClassInflation.distinguishedCutInventory_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguishedCutInventory_product

/-- info: 'SkewJacobiNegative.BetaDiagram.square_initial_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.square_initial_monomial

/-- info: 'SkewJacobiNegative.BetaDiagram.initialForm_rat_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.initialForm_rat_smul

/-- info: 'SkewJacobiNegative.BetaDiagram.schur_eq_of_proportional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.schur_eq_of_proportional

/-- info: 'SkewJacobiNegative.BetaDiagram.schur_eq_of_associated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.schur_eq_of_associated

/-- info: 'SkewJacobiNegative.BetaDiagram.connected_product_functions_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.connected_product_functions_eq

/-- info: 'SkewJacobiNegative.BetaDiagram.product_component_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.product_component_matching

/-- info: 'SkewClassInflation.periodicUnion_sub_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodicUnion_sub_smul

/-- info: 'SkewClassInflation.hatMark_sub_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.hatMark_sub_smul

/-- info: 'SkewClassInflation.noHatAdjacency_of_hatMark_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.noHatAdjacency_of_hatMark_empty

/-- info: 'SkewClassInflation.cofactor_monomial_iff_hessenberg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cofactor_monomial_iff_hessenberg

/-- info: 'SkewClassInflation.profile_cofactor_monomial_iff_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_cofactor_monomial_iff_thick

/-- info: 'SkewClassInflation.hessenberg_of_equal_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.hessenberg_of_equal_schur

/-- info: 'SkewClassInflation.mem_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mem_rowCells

/-- info: 'SkewClassInflation.contents_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contents_rowCells

/-- info: 'SkewClassInflation.span_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.span_rowCells

/-- info: 'SkewClassInflation.rowCells_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowCells_nonempty

/-- info: 'SkewClassInflation.minContent_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.minContent_rowCells

/-- info: 'SkewClassInflation.maxContent_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.maxContent_rowCells

/-- info: 'SkewClassInflation.diagLo_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.diagLo_rowCells

/-- info: 'SkewClassInflation.sw_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.sw_rowCells

/-- info: 'SkewClassInflation.ne_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ne_rowCells

/-- info: 'SkewClassInflation.isConnectedSkew_rowCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.isConnectedSkew_rowCells

/-- info: 'SkewClassInflation.ConnectedProfile.inflate_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.inflate_injective

/-- info: 'SkewClassInflation.ConnectedProfile.inflate_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.inflate_rotate

/-- info: 'SkewClassInflation.ConnectedProfile.schur_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.schur_rotate

/-- info: 'SkewClassInflation.ConnectedProfile.rotate_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.rotate_rotate

/-- info: 'SkewClassInflation.ConnectedProfile.schurClass_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.schurClass_rotate

/-- info: 'SkewClassInflation.ConnectedProfile.inflation_no_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.inflation_no_escape

/-- info: 'SkewClassInflation.ConnectedProfile.equality_at_earlier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.equality_at_earlier

/-- info: 'SkewClassInflation.ConnectedProfile.class_transport_of_noOpening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ConnectedProfile.class_transport_of_noOpening

/-- info: 'SkewClassInflation.image_joined_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.image_joined_word

/-- info: 'SkewClassInflation.Profile.join_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_rowSet

/-- info: 'SkewClassInflation.Profile.join_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_colSet

/-- info: 'SkewClassInflation.Profile.join_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_span

/-- info: 'SkewClassInflation.Profile.prod_join_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.prod_join_gaps

/-- info: 'SkewClassInflation.complete_totalDegree_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.complete_totalDegree_le_one

/-- info: 'SkewClassInflation.top_component_complete_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.top_component_complete_prod

/-- info: 'SkewClassInflation.lowerSubstitution_shifted_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.lowerSubstitution_shifted_slot

/-- info: 'SkewClassInflation.lowering_shifted_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.lowering_shifted_prod

/-- info: 'SkewClassInflation.lowering_shifted_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.lowering_shifted_det

/-- info: 'SkewClassInflation.lowering_inflated_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.lowering_inflated_profile

/-- info: 'SkewClassInflation.profileSchur_eq_of_inflate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileSchur_eq_of_inflate_eq

/-- info: 'SkewClassInflation.Profile.zeroJoin_seam_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroJoin_seam_xi

/-- info: 'SkewClassInflation.Profile.zeroJoin_seam_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroJoin_seam_zeta

/-- info: 'SkewClassInflation.Profile.merge_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_rowSet

/-- info: 'SkewClassInflation.Profile.merge_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_colSet

/-- info: 'SkewClassInflation.isMonomial_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.isMonomial_of_dvd

/-- info: 'SkewClassInflation.isMonomial_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.isMonomial_mul_iff

/-- info: 'SkewClassInflation.irreducible_monomial_degree_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.irreducible_monomial_degree_le_one

/-- info: 'SkewClassInflation.connected_schur_not_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.connected_schur_not_monomial

/-- info: 'SkewClassInflation.profileSchur_eq_inherited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileSchur_eq_inherited

/-- info: 'SkewClassInflation.profile_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_invariants

/-- info: 'SkewClassInflation.mate_deflation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mate_deflation

/-- info: 'SkewClassInflation.equality_at_earlier_inflation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.equality_at_earlier_inflation

/-- info: 'SkewClassInflation.inequality_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inequality_persists

/-- info: 'SkewClassInflation.shiftHom_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.shiftHom_entry

/-- info: 'SkewClassInflation.profileSchur_inflate_eq_shiftHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileSchur_inflate_eq_shiftHom

/-- info: 'SkewClassInflation.inflate_eq_of_noOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflate_eq_of_noOpening

/-- info: 'SkewClassInflation.inflate_eq_iff_of_noOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflate_eq_iff_of_noOpening

/-- info: 'SkewClassInflation.noOpening_of_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.noOpening_of_depth

/-- info: 'SkewClassInflation.sign_ordered_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.sign_ordered_blocks

/-- info: 'SkewClassInflation.ordinary_origin_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ordinary_origin_add

/-- info: 'SkewClassInflation.ordinary_compose_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ordinary_compose_union

/-- info: 'SkewClassInflation.ordinary_compose_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ordinary_compose_translate

/-- info: 'SkewClassInflation.overlap_cut_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.overlap_cut_obstruction

/-- info: 'SkewClassInflation.periodic_nat_gcd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_nat_gcd

/-- info: 'SkewClassInflation.periodic_int_remainder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_int_remainder

/-- info: 'SkewClassInflation.overlap_period_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.overlap_period_obstruction

/-- info: 'SkewClassInflation.periodicCutPower_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodicCutPower_internal

/-- info: 'SkewClassInflation.periodicCutPower_no_right_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodicCutPower_no_right_factor

/-- info: 'SkewJacobiNegative.BetaDiagram.cornerResidual_vars_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewJacobiNegative.BetaDiagram.cornerResidual_vars_lt

/-- info: 'SkewClassInflation.BetaDiagram.last_column_minor_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BetaDiagram.last_column_minor_ne_zero

/-- info: 'SkewClassInflation.BetaDiagram.private_last_variable_occurs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BetaDiagram.private_last_variable_occurs

/-- info: 'SkewClassInflation.BetaDiagram.residue_private_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BetaDiagram.residue_private_last

/-- info: 'SkewClassInflation.BetaDiagram.private_residue_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BetaDiagram.private_residue_support

/-- info: 'SkewClassInflation.BetaDiagram.row_beta_occurs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BetaDiagram.row_beta_occurs

/-- info: 'SkewClassInflation.BetaDiagram.row_list_eq_of_private_residues' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BetaDiagram.row_list_eq_of_private_residues

/-- info: 'SkewClassInflation.rowInterval_connected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowInterval_connected

/-- info: 'SkewClassInflation.diagonal_cofactor_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.diagonal_cofactor_split

/-- info: 'SkewClassInflation.private_irreducible_row_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.private_irreducible_row_boundary

/-- info: 'SkewClassInflation.shortest_row_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.shortest_row_private

/-- info: 'SkewClassInflation.shortest_first_row_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.shortest_first_row_coefficient

/-- info: 'SkewClassInflation.profile_merge_join_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_merge_join_assoc

/-- info: 'SkewClassInflation.Profile.inflate_r' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.inflate_r

/-- info: 'SkewClassInflation.Profile.inflate_g' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.inflate_g

/-- info: 'SkewClassInflation.Profile.inflate_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.inflate_zero

/-- info: 'SkewClassInflation.Profile.inflate_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.inflate_add

/-- info: 'SkewClassInflation.Profile.inflate_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.inflate_injective

/-- info: 'SkewClassInflation.Profile.inflate_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.inflate_rotate

/-- info: 'SkewClassInflation.Profile.zeta_inflate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeta_inflate

/-- info: 'SkewClassInflation.Profile.xi_inflate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.xi_inflate

/-- info: 'SkewClassInflation.Profile.index_inflate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.index_inflate

/-- info: 'SkewClassInflation.Profile.canDeflate_inflate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.canDeflate_inflate

/-- info: 'SkewClassInflation.Profile.deflate_inflate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.deflate_inflate

/-- info: 'SkewClassInflation.Profile.inflate_deflate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.inflate_deflate

/-- info: 'SkewClassInflation.Profile.exists_inflate_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.exists_inflate_iff

/-- info: 'SkewClassInflation.Profile.join_coordinates_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_coordinates_rows

/-- info: 'SkewClassInflation.Profile.join_coordinates_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_coordinates_last

/-- info: 'SkewClassInflation.Profile.join_coordinates_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_coordinates_gaps

/-- info: 'SkewClassInflation.Profile.join_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_beta

/-- info: 'SkewClassInflation.Profile.join_xi_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_xi_left

/-- info: 'SkewClassInflation.Profile.join_zeta_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_zeta_left

/-- info: 'SkewClassInflation.Profile.join_xi_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_xi_right

/-- info: 'SkewClassInflation.Profile.join_zeta_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_zeta_right

/-- info: 'SkewClassInflation.profileCells_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_join

/-- info: 'SkewClassInflation.inflate_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inflate_join

/-- info: 'SkewClassInflation.profileCells_inflate_zeroJoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_inflate_zeroJoin

/-- info: 'SkewClassInflation.Profile.joinRows_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.joinRows_left

/-- info: 'SkewClassInflation.Profile.joinRows_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.joinRows_right

/-- info: 'SkewClassInflation.Profile.joinGaps_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.joinGaps_left

/-- info: 'SkewClassInflation.Profile.joinGaps_middle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.joinGaps_middle

/-- info: 'SkewClassInflation.Profile.joinGaps_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.joinGaps_right

/-- info: 'SkewClassInflation.Profile.merge_joined_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_joined_row

/-- info: 'SkewClassInflation.Profile.zeroJoin_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroJoin_thick

/-- info: 'SkewClassInflation.Profile.merge_xi_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_xi_left

/-- info: 'SkewClassInflation.Profile.merge_zeta_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_zeta_left

/-- info: 'SkewClassInflation.Profile.merge_xi_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_xi_right

/-- info: 'SkewClassInflation.Profile.merge_zeta_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_zeta_right

/-- info: 'SkewClassInflation.profileCells_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_merge

/-- info: 'SkewClassInflation.Profile.join_right_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_right_congr

/-- info: 'SkewClassInflation.Profile.join_left_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_left_congr

/-- info: 'SkewClassInflation.Profile.merge_right_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_right_congr

/-- info: 'SkewClassInflation.Profile.merge_pair_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_pair_injective

/-- info: 'SkewClassInflation.contract_row_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_row_of_ne

/-- info: 'SkewClassInflation.contract_xi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_xi_zero

/-- info: 'SkewClassInflation.profileSigma_eq_of_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileSigma_eq_of_words

/-- info: 'SkewClassInflation.Profile.merge_r_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_r_left

/-- info: 'SkewClassInflation.Profile.merge_r_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_r_right

/-- info: 'SkewClassInflation.Profile.merge_g_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_g_left

/-- info: 'SkewClassInflation.Profile.merge_g_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_g_right

/-- info: 'SkewClassInflation.Profile.merge_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.merge_span

/-- info: 'SkewClassInflation.profile_rotate_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_rotate_rowSet

/-- info: 'SkewClassInflation.profile_rotate_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_rotate_colSet

/-- info: 'SkewClassInflation.profile_rotate_thick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_rotate_thick

/-- info: 'SkewClassInflation.Profile.join_row_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_row_weight

/-- info: 'SkewClassInflation.punctured_cycle_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.punctured_cycle_endpoints

/-- info: 'SkewClassInflation.punctured_cycle_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.punctured_cycle_completion

/-- info: 'SkewClassInflation.regroup_sign_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.regroup_sign_count

/-- info: 'SkewClassInflation.deletionSign_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.deletionSign_count

/-- info: 'SkewClassInflation.join_row_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.join_row_word

/-- info: 'SkewClassInflation.profileCells_ribbonRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileCells_ribbonRow

/-- info: 'SkewClassInflation.outerRibbon_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.outerRibbon_word

/-- info: 'SkewClassInflation.outerRibbon_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.outerRibbon_schur

/-- info: 'SkewClassInflation.outerRibbon_eq_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.outerRibbon_eq_chain

/-- info: 'SkewClassInflation.first_contract_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.first_contract_rows

/-- info: 'SkewClassInflation.right_first_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.right_first_rows

/-- info: 'SkewClassInflation.intervalMask_coarsenRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.intervalMask_coarsenRows

/-- info: 'SkewClassInflation.rowPartition_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowPartition_positive

/-- info: 'SkewClassInflation.sum_coarsening_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.sum_coarsening_top

/-- info: 'SkewClassInflation.selectedSeams_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.selectedSeams_eq_zero_iff

/-- info: 'SkewClassInflation.rowPartition_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowPartition_values

/-- info: 'SkewClassInflation.rowPartition_card' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowPartition_card

/-- info: 'SkewClassInflation.rowPartition_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowPartition_mem

/-- info: 'SkewClassInflation.maximal_coarseningPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.maximal_coarseningPartition

/-- info: 'SkewClassInflation.zero_gaps_thick' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_gaps_thick

/-- info: 'SkewClassInflation.contract_first_row_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_first_row_word

/-- info: 'SkewClassInflation.zero_gaps_ribbon_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_gaps_ribbon_polynomial

/-- info: 'SkewClassInflation.word_ofFn_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.word_ofFn_rev

/-- info: 'SkewClassInflation.ambiguous_inner_ribbon_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_inner_ribbon_eq

/-- info: 'SkewClassInflation.ambiguous_inner_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_inner_schur_eq

/-- info: 'SkewClassInflation.ambiguous_inner_nonrotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_inner_nonrotation

/-- info: 'SkewClassInflation.ambiguous_inner_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_inner_endpoints

/-- info: 'SkewClassInflation.ambiguous_power_partition_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_power_partition_counts

/-- info: 'SkewClassInflation.ambiguous_power_schur_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_power_schur_ne

/-- info: 'SkewClassInflation.ambiguous_parent_schur_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_parent_schur_ne

/-- info: 'SkewClassInflation.ambiguous_equal_gap_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_equal_gap_schur_eq

/-- info: 'SkewClassInflation.ambiguous_equal_gap_nonrotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_equal_gap_nonrotation

/-- info: 'SkewClassInflation.ambiguous_parent_nonrotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ambiguous_parent_nonrotation

/-- info: 'SkewClassInflation.colliding_inner_merger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.colliding_inner_merger

/-- info: 'SkewClassInflation.colliding_inner_power_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.colliding_inner_power_rows

/-- info: 'SkewClassInflation.colliding_inner_source_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.colliding_inner_source_rows

/-- info: 'SkewClassInflation.colliding_inner_source_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.colliding_inner_source_gaps

/-- info: 'SkewClassInflation.zero_gap_inner_power_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_gap_inner_power_rows

/-- info: 'SkewClassInflation.zero_gap_inner_source_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_gap_inner_source_thick

/-- info: 'SkewClassInflation.minimumPolynomial_eq_C_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.minimumPolynomial_eq_C_of_not_mem

/-- info: 'SkewClassInflation.distinguished_index_iff_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_index_iff_seam

/-- info: 'SkewClassInflation.distinguished_not_mem_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_not_mem_component

/-- info: 'SkewClassInflation.distinguished_cut_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_cut_product

/-- info: 'SkewClassInflation.distinguished_entry_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_entry_top

/-- info: 'SkewClassInflation.distinguished_highest_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_highest_layer

/-- info: 'SkewClassInflation.contract_rows_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_rows_above

/-- info: 'SkewClassInflation.contractAll_rows_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAll_rows_above

/-- info: 'SkewClassInflation.distinguished_not_mem_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_not_mem_contraction

/-- info: 'SkewClassInflation.distinguished_degree_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.distinguished_degree_exact

/-- info: 'SkewClassInflation.Profile.join_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_thick

/-- info: 'SkewClassInflation.outer_one_two_ribbon_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.outer_one_two_ribbon_eq

/-- info: 'SkewClassInflation.original_two_order_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.original_two_order_equality

/-- info: 'SkewClassInflation.original_two_orders_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.original_two_orders_distinct

/-- info: 'SkewClassInflation.threshold_one_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_separation

/-- info: 'SkewClassInflation.threshold_two_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_survival

/-- info: 'SkewClassInflation.threshold_two_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_separation

/-- info: 'SkewClassInflation.noOpening_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.noOpening_rotate

/-- info: 'SkewClassInflation.suffixSet_mem_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.suffixSet_mem_partial

/-- info: 'SkewClassInflation.wordSuffixSet_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordSuffixSet_blocks

/-- info: 'SkewClassInflation.wordSuffixSet_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordSuffixSet_single

/-- info: 'SkewClassInflation.wordSuffixSet_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordSuffixSet_cons

/-- info: 'SkewClassInflation.arithmeticGrid_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.arithmeticGrid_join

/-- info: 'SkewClassInflation.wordSuffixSet_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordSuffixSet_bounds

/-- info: 'SkewClassInflation.wordSuffixSet_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordSuffixSet_head

/-- info: 'SkewClassInflation.zeroSeamCount_eq_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroSeamCount_eq_count

/-- info: 'SkewClassInflation.zeroSeamCount_eq_of_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroSeamCount_eq_of_schur_eq

/-- info: 'SkewClassInflation.profile_eq_of_beta_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_eq_of_beta_translation

/-- info: 'SkewClassInflation.zeroSeamCount_zeroJoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroSeamCount_zeroJoin

/-- info: 'SkewClassInflation.arithmeticGrid_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.arithmeticGrid_residue

/-- info: 'SkewClassInflation.arithmeticGrid_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.arithmeticGrid_disjoint

/-- info: 'SkewClassInflation.arithmeticGrid_multiple_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.arithmeticGrid_multiple_disjoint

/-- info: 'SkewClassInflation.separated_union_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.separated_union_sdiff

/-- info: 'SkewClassInflation.inserted_sdiff_inserted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inserted_sdiff_inserted

/-- info: 'SkewClassInflation.threshold_one_first_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_first_rows

/-- info: 'SkewClassInflation.threshold_one_first_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_first_gaps

/-- info: 'SkewClassInflation.threshold_one_second_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_second_rows

/-- info: 'SkewClassInflation.threshold_one_second_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_second_gaps

/-- info: 'SkewClassInflation.threshold_one_first_core_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_first_core_rows

/-- info: 'SkewClassInflation.threshold_one_second_core_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_second_core_rows

/-- info: 'SkewClassInflation.threshold_one_core_cols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_core_cols

/-- info: 'SkewClassInflation.threshold_two_inner_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_inner_cells

/-- info: 'SkewClassInflation.threshold_two_mark_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_mark_cells

/-- info: 'SkewClassInflation.threshold_two_mark_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_mark_legal

/-- info: 'SkewClassInflation.threshold_two_mark_not_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_two_mark_not_legal

/-- info: 'SkewClassInflation.threshold_one_first_core_private_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_first_core_private_derivative

/-- info: 'SkewClassInflation.threshold_one_second_core_private_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threshold_one_second_core_private_absent

/-- info: 'SkewClassInflation.eval_ne_zero_of_new_variable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.eval_ne_zero_of_new_variable

/-- info: 'SkewClassInflation.degreeOf_aeval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.degreeOf_aeval_zero

/-- info: 'SkewClassInflation.aeval_fin_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.aeval_fin_split

/-- info: 'SkewClassInflation.triangular_finite_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.triangular_finite_nonzero

/-- info: 'SkewClassInflation.triangular_finite_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.triangular_finite_injective

/-- info: 'SkewClassInflation.triangular_nat_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.triangular_nat_injective

/-- info: 'SkewClassInflation.triangular_pnat_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.triangular_pnat_injective

/-- info: 'SkewClassInflation.degreeOf_zero_of_vars_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.degreeOf_zero_of_vars_lt

/-- info: 'SkewClassInflation.triangular_substitution_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.triangular_substitution_injective

/-- info: 'SkewClassInflation.splittingSource_class_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_class_finite

/-- info: 'SkewClassInflation.splittingSource_class_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_class_lower_bound

/-- info: 'SkewClassInflation.splittingSource_image_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_image_lower_bound

/-- info: 'SkewClassInflation.splittingSource_image_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_image_classes

/-- info: 'SkewClassInflation.splittingSource_image_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splittingSource_image_closed

/-- info: 'SkewClassInflation.unbounded_class_splitting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unbounded_class_splitting

/-- info: 'SkewClassInflation.left_principal_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.left_principal_det

/-- info: 'SkewClassInflation.right_principal_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.right_principal_det

/-- info: 'SkewClassInflation.unit_constant_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unit_constant_slice

/-- info: 'SkewClassInflation.unit_zero_cut_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unit_zero_cut_constant

/-- info: 'SkewClassInflation.unit_single_row_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unit_single_row_constant

/-- info: 'SkewClassInflation.unitEntry_coeff_zero_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitEntry_coeff_zero_of_nonpos

/-- info: 'SkewClassInflation.unitSchur_zeroJoin_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitSchur_zeroJoin_constant

/-- info: 'SkewClassInflation.thick_positive_gaps_zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.thick_positive_gaps_zeroFree

/-- info: 'SkewClassInflation.unitSchur_eq_C_of_zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitSchur_eq_C_of_zeroFree

/-- info: 'SkewClassInflation.isMonomial_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.isMonomial_complete

/-- info: 'SkewClassInflation.isMonomial_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.isMonomial_prod

/-- info: 'SkewClassInflation.weak_board_factor_at_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.weak_board_factor_at_cut

/-- info: 'SkewClassInflation.weak_board_monomial_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.weak_board_monomial_iff

/-- info: 'SkewClassInflation.antitone_max_after_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.antitone_max_after_difference

/-- info: 'SkewClassInflation.antitone_min_after_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.antitone_min_after_difference

/-- info: 'SkewClassInflation.first_upper_not_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.first_upper_not_column

/-- info: 'SkewClassInflation.first_lower_not_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.first_lower_not_row

/-- info: 'SkewClassInflation.last_upper_not_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.last_upper_not_column

/-- info: 'SkewClassInflation.contractAllZeros_first_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_first_row

/-- info: 'SkewClassInflation.contractAllZeros_last_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_last_row

/-- info: 'SkewClassInflation.contractAllZeros_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_span

/-- info: 'SkewClassInflation.image_delete_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.image_delete_index

/-- info: 'SkewClassInflation.contract_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_rowSet

/-- info: 'SkewClassInflation.contract_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_colSet

/-- info: 'SkewClassInflation.erase_common_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.erase_common_sdiff

/-- info: 'SkewClassInflation.contract_zero_residualSets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_zero_residualSets

/-- info: 'SkewClassInflation.contractAllZeros_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_thick

/-- info: 'SkewClassInflation.contractAllZeros_residualSets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_residualSets

/-- info: 'SkewClassInflation.contractAllZeros_sets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_sets

/-- info: 'SkewClassInflation.profileSigma_eq_of_full_sets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profileSigma_eq_of_full_sets

/-- info: 'SkewClassInflation.image_at_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.image_at_cut

/-- info: 'SkewClassInflation.zero_cut_reassembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_cut_reassembly

/-- info: 'SkewClassInflation.Profile.join_left_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_left_function

/-- info: 'SkewClassInflation.Profile.join_right_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_right_function

/-- info: 'SkewClassInflation.Profile.join_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.join_schur

/-- info: 'SkewClassInflation.Profile.zeroJoin_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.zeroJoin_schur

/-- info: 'SkewClassInflation.contractAllZeros_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_self

/-- info: 'SkewClassInflation.exists_first_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_first_zero

/-- info: 'SkewClassInflation.first_zero_prefix_zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.first_zero_prefix_zeroFree

/-- info: 'SkewClassInflation.profile_rowSet_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_rowSet_bounds

/-- info: 'SkewClassInflation.profile_colSet_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_colSet_bounds

/-- info: 'SkewClassInflation.profile_zero_mem_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.profile_zero_mem_colSet

/-- info: 'SkewClassInflation.schur_eq_of_full_sets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.schur_eq_of_full_sets

/-- info: 'SkewClassInflation.touching_span_differences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.touching_span_differences

/-- info: 'SkewClassInflation.zero_merge_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_merge_rowSet

/-- info: 'SkewClassInflation.zero_merge_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_merge_colSet

/-- info: 'SkewClassInflation.zero_prefix_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_prefix_contraction

/-- info: 'SkewClassInflation.undoOdd_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undoOdd_complete

/-- info: 'SkewClassInflation.undoOdd_minimum_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undoOdd_minimum_entry

/-- info: 'SkewClassInflation.unitSchur_eq_lifted_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitSchur_eq_lifted_minimum

/-- info: 'SkewClassInflation.contract_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contract_lift

/-- info: 'SkewClassInflation.undoOdd_lifted_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undoOdd_lifted_schur

/-- info: 'SkewClassInflation.unitSchur_constant_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitSchur_constant_matrix

/-- info: 'SkewClassInflation.unitEval_hTilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitEval_hTilde

/-- info: 'SkewClassInflation.unitEval_schurHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitEval_schurHom

/-- info: 'SkewClassInflation.unitSchur_eq_of_schur_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unitSchur_eq_of_schur_eq

/-- info: 'SkewClassInflation.zeroSeamCount_eq_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroSeamCount_eq_lift

/-- info: 'SkewClassInflation.lift_contractAllZeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.lift_contractAllZeros

/-- info: 'SkewClassInflation.twoOne_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.twoOne_thick

/-- info: 'SkewClassInflation.twoOne_rows_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.twoOne_rows_above

/-- info: 'SkewClassInflation.contractAllZeros_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_size

/-- info: 'SkewClassInflation.contractAllZeros_gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.contractAllZeros_gap_pos

/-- info: 'SkewClassInflation.zeroCutComponent_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroCutComponent_lift

/-- info: 'SkewClassInflation.zeroCutComponent_gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zeroCutComponent_gap_pos

/-- info: 'SkewClassInflation.minimumPolynomial_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.minimumPolynomial_coeff_zero

/-- info: 'SkewClassInflation.zero_seam_constant_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_seam_constant_coefficient

/-- info: 'SkewClassInflation.zero_seam_highest_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_seam_highest_coefficient

/-- info: 'SkewClassInflation.Profile.sum_join_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.Profile.sum_join_gaps

