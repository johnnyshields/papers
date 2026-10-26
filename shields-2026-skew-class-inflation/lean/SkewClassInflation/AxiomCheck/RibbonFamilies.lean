/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundedEvenPropagation
import SkewClassInflation.RibbonCellChains
import SkewClassInflation.RibbonEndpoints
import SkewClassInflation.RibbonReconstructionWords
import SkewClassInflation.StableCutCodeFactorization
import SkewClassInflation.SymmetricRibbonReconstruction

/-!
# Exact RibbonFamilies axiom footprints

Every expected message is the observed kernel footprint of the declaration it guards.
-/

/-- info: 'SkewClassInflation.undetermined_even_discrepancy_options' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_even_discrepancy_options

/-- info: 'SkewClassInflation.bounded_even_discrepancy_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.bounded_even_discrepancy_agrees

/-- info: 'SkewClassInflation.rowPrefixCut_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowPrefixCut_zero

/-- info: 'SkewClassInflation.rowPrefixCut_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowPrefixCut_succ

/-- info: 'SkewClassInflation.rowPrefixCut_merge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowPrefixCut_merge

/-- info: 'SkewClassInflation.coarsenRows_properCuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_properCuts

/-- info: 'SkewClassInflation.rowComposition_properCuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.rowComposition_properCuts

/-- info: 'SkewClassInflation.coarsenedComposition_cuts_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenedComposition_cuts_subset

/-- info: 'SkewClassInflation.coarsenRows_exists_iff_cuts_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_exists_iff_cuts_subset

/-- info: 'SkewClassInflation.coarseningPartition_eq_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartition_eq_pair

/-- info: 'SkewClassInflation.coarsenRows_two_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_two_exists

/-- info: 'SkewClassInflation.coarsenRows_preimage_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_preimage_card

/-- info: 'SkewClassInflation.coarseningPartitions_count_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_count_pair

/-- info: 'SkewClassInflation.coarsening_two_cut_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsening_two_cut_type

/-- info: 'SkewClassInflation.reflected_cut_type_of_coarsening_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.reflected_cut_type_of_coarsening_eq

/-- info: 'SkewClassInflation.coarseningInventory_of_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_of_nil

/-- info: 'SkewClassInflation.coarseningInventory_eq_of_blocks_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_eq_of_blocks_eq

/-- info: 'SkewClassInflation.exists_positive_row_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_positive_row_word

/-- info: 'SkewClassInflation.coarseningInventory_rowComposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_rowComposition

/-- info: 'SkewClassInflation.coarseningInventory_eq_of_row_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_eq_of_row_word

/-- info: 'SkewClassInflation.ribbon_eq_iff_coarseningInventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_eq_iff_coarseningInventory

/-- info: 'SkewClassInflation.coarseningInventory_count_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_count_pair

/-- info: 'SkewClassInflation.coarseningInventory_two_cut_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_two_cut_type

/-- info: 'SkewClassInflation.properCuts_eq_sizeUpTo_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_eq_sizeUpTo_image

/-- info: 'SkewClassInflation.sizeUpTo_injOn_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.sizeUpTo_injOn_internal

/-- info: 'SkewClassInflation.properCuts_sum_sizeUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_sum_sizeUpTo

/-- info: 'SkewClassInflation.composition_eq_of_sizeUpTo_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.composition_eq_of_sizeUpTo_internal

/-- info: 'SkewClassInflation.composition_eq_of_ordered_cut_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.composition_eq_of_ordered_cut_sums

/-- info: 'SkewClassInflation.wordPadEnds_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordPadEnds_sum

/-- info: 'SkewClassInflation.wordPadEnds_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordPadEnds_pos

/-- info: 'SkewClassInflation.wordPadEnds_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordPadEnds_length

/-- info: 'SkewClassInflation.wordPadEnds_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordPadEnds_cuts

/-- info: 'SkewClassInflation.wordPadEnds_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordPadEnds_mod

/-- info: 'SkewClassInflation.composition_part_lt_of_multipart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.composition_part_lt_of_multipart

/-- info: 'SkewClassInflation.paddedComposition_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.paddedComposition_cuts

/-- info: 'SkewClassInflation.paddedComposition_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.paddedComposition_length

/-- info: 'SkewClassInflation.paddedComposition_residueWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.paddedComposition_residueWord

/-- info: 'SkewClassInflation.cutCode_periodic_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutCode_periodic_cuts

/-- info: 'SkewClassInflation.proper_factorization_of_cutCode_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.proper_factorization_of_cutCode_period

/-- info: 'SkewClassInflation.undeterminedPrefixGcd_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedPrefixGcd_dvd

/-- info: 'SkewClassInflation.cutDetermined_of_prefix_divisibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_of_prefix_divisibility

/-- info: 'SkewClassInflation.undetermined_prefix_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_prefix_period

/-- info: 'SkewClassInflation.undeterminedGcd_signed_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedGcd_signed_period

/-- info: 'SkewClassInflation.nonreconstructible_exists_signed_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonreconstructible_exists_signed_period

/-- info: 'SkewClassInflation.compositionCutSign_eq_zero_of_not_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSign_eq_zero_of_not_one

/-- info: 'SkewClassInflation.compositionCutSign_of_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSign_of_one

/-- info: 'SkewClassInflation.cutDetermined_of_two_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_of_two_single

/-- info: 'SkewClassInflation.cutDetermined_of_three_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_of_three_single

/-- info: 'SkewClassInflation.exists_first_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_first_undetermined

/-- info: 'SkewClassInflation.undetermined_cut_types' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_cut_types

/-- info: 'SkewClassInflation.undetermined_cutSign_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_cutSign_antisymm

/-- info: 'SkewClassInflation.first_undetermined_cutSign_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.first_undetermined_cutSign_antisymm

/-- info: 'SkewClassInflation.compositionCutSign_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSign_reflect

/-- info: 'SkewClassInflation.undetermined_cutSign_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_cutSign_shift

/-- info: 'SkewClassInflation.evenCutDisagreements_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutDisagreements_bounds

/-- info: 'SkewClassInflation.evenCutClosureStep_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosureStep_pos

/-- info: 'SkewClassInflation.evenCutClosureStep_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosureStep_dvd

/-- info: 'SkewClassInflation.evenCutClosureStep_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosureStep_lt

/-- info: 'SkewClassInflation.evenCutClosure_iterate_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosure_iterate_pos

/-- info: 'SkewClassInflation.evenCutClosure_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosure_terminates

/-- info: 'SkewClassInflation.undetermined_evenCutClosure_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_evenCutClosure_terminates

/-- info: 'SkewClassInflation.evenCutCode_frontier_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutCode_frontier_periods

/-- info: 'SkewClassInflation.evenCutClosure_code_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosure_code_refinement

/-- info: 'SkewClassInflation.coarseningInventory_count_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_count_singleton

/-- info: 'SkewClassInflation.compositionProduct_inner_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_inner_inventory

/-- info: 'SkewClassInflation.inventory_mate_inner_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_mate_inner_inventory

/-- info: 'SkewClassInflation.inventory_mate_factor_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_mate_factor_transport

/-- info: 'SkewClassInflation.coarseningInventory_member_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_member_weight

/-- info: 'SkewClassInflation.coarseningInventory_eq_of_weighted_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_eq_of_weighted_counts

/-- info: 'SkewClassInflation.coarseningInventory_count_scaled_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_count_scaled_outer

/-- info: 'SkewClassInflation.inventory_mate_outer_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_mate_outer_inventory

/-- info: 'SkewClassInflation.compositionWindow_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_cuts

/-- info: 'SkewClassInflation.compositionWindow_compositionProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_compositionProduct

/-- info: 'SkewClassInflation.compositionWindow_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_length_le

/-- info: 'SkewClassInflation.nonmultipleCuts_eq_window_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonmultipleCuts_eq_window_union

/-- info: 'SkewClassInflation.compositionWindow_images_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_images_disjoint

/-- info: 'SkewClassInflation.nonmultipleCuts_card_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonmultipleCuts_card_eq_sum

/-- info: 'SkewClassInflation.compositionProduct_nonmultiple_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_nonmultiple_card

/-- info: 'SkewClassInflation.properCuts_card_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_card_add_one

/-- info: 'SkewClassInflation.compositionWindow_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_length_eq

/-- info: 'SkewClassInflation.mate_coarsening_residue_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mate_coarsening_residue_bound

/-- info: 'SkewClassInflation.compositionWindow_prefix_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_prefix_antitone

/-- info: 'SkewClassInflation.compositionWindow_endpoints_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_endpoints_eq

/-- info: 'SkewClassInflation.compositionWindow_all_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_all_eq

/-- info: 'SkewClassInflation.inventory_mate_cut_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_mate_cut_periodic

/-- info: 'SkewClassInflation.inventory_mate_periodic_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_mate_periodic_factorization

/-- info: 'SkewClassInflation.compositionCutType_endpoint_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutType_endpoint_windows

/-- info: 'SkewClassInflation.compositionWindow_endpoint_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_endpoint_balance

/-- info: 'SkewClassInflation.compositionWindow_endpoint_cut_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionWindow_endpoint_cut_sum

/-- info: 'SkewClassInflation.actualCutBool_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.actualCutBool_zero

/-- info: 'SkewClassInflation.actualCutBool_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.actualCutBool_weight

/-- info: 'SkewClassInflation.actualCutBool_reflect_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.actualCutBool_reflect_one

/-- info: 'SkewClassInflation.actualCutBool_reflect_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.actualCutBool_reflect_even

/-- info: 'SkewClassInflation.actualCutBool_even_opposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.actualCutBool_even_opposite

/-- info: 'SkewClassInflation.fourPartLeftCuts_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPartLeftCuts_pattern

/-- info: 'SkewClassInflation.fourPartRightCuts_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPartRightCuts_pattern

/-- info: 'SkewClassInflation.fourPart_actual_discrepancy_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPart_actual_discrepancy_count

/-- info: 'SkewClassInflation.fourPart_mask_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPart_mask_single

/-- info: 'SkewClassInflation.fourPart_mask_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPart_mask_pair

/-- info: 'SkewClassInflation.fourPart_mask_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPart_mask_complement

/-- info: 'SkewClassInflation.compositionCutCodeNat_eq_of_cut_bools' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutCodeNat_eq_of_cut_bools

/-- info: 'SkewClassInflation.equal_cutSign_bool_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.equal_cutSign_bool_pairs

/-- info: 'SkewClassInflation.fourPart_even_discrepancy_alternatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPart_even_discrepancy_alternatives

/-- info: 'SkewClassInflation.fourPartDiscrepancy_alternatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPartDiscrepancy_alternatives

/-- info: 'SkewClassInflation.wordProperCuts_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_four

/-- info: 'SkewClassInflation.fourPart_retained_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPart_retained_iff

/-- info: 'SkewClassInflation.labeled_fourPart_mask_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.labeled_fourPart_mask_count

/-- info: 'SkewClassInflation.fourPart_mask_count_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.fourPart_mask_count_invariant

/-- info: 'SkewClassInflation.compositionCutSignInt_masked_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSignInt_masked_period

/-- info: 'SkewClassInflation.compositionCutCode_masked_whole_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutCode_masked_whole_period

/-- info: 'SkewClassInflation.nonreconstructible_initial_code_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonreconstructible_initial_code_periods

/-- info: 'SkewClassInflation.coarseningInventory_member_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_member_composition

/-- info: 'SkewClassInflation.compositionPartition_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionPartition_values

/-- info: 'SkewClassInflation.coarseningInventory_contains_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_contains_composition

/-- info: 'SkewClassInflation.compositionPartition_residue_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionPartition_residue_values

/-- info: 'SkewClassInflation.positivePartitionResidues_compositionPartition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.positivePartitionResidues_compositionPartition

/-- info: 'SkewClassInflation.coarseningInventory_residue_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_residue_bound

/-- info: 'SkewClassInflation.labeledOrderFiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.labeledOrderFiber_card

/-- info: 'SkewClassInflation.labeledCoarseningOrders_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.labeledCoarseningOrders_card

/-- info: 'SkewClassInflation.labeledCoarseningOrders_card_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.labeledCoarseningOrders_card_invariant

/-- info: 'SkewClassInflation.tuple_perm_exists_index_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.tuple_perm_exists_index_perm

/-- info: 'SkewClassInflation.word_perm_exists_index_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.word_perm_exists_index_perm

/-- info: 'SkewClassInflation.partitionOrders_ofFn_perms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_ofFn_perms

/-- info: 'SkewClassInflation.partitionOrders_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_length

/-- info: 'SkewClassInflation.partitionOrders_part_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_part_lt

/-- info: 'SkewClassInflation.insertLargePart_mem_partitionOrders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_mem_partitionOrders

/-- info: 'SkewClassInflation.compositionProduct_largePart_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_largePart_count

/-- info: 'SkewClassInflation.insertLargePart_idxOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_idxOf

/-- info: 'SkewClassInflation.insertLargePart_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_erase

/-- info: 'SkewClassInflation.insertLargePart_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_injective

/-- info: 'SkewClassInflation.partitionOrders_cons_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_cons_insert

/-- info: 'SkewClassInflation.insertLargePart_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_length

/-- info: 'SkewClassInflation.take_insertLargePart_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.take_insertLargePart_of_le

/-- info: 'SkewClassInflation.take_insertLargePart_sum_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.take_insertLargePart_sum_of_gt

/-- info: 'SkewClassInflation.insertLargePart_internal_cut_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_internal_cut_origin

/-- info: 'SkewClassInflation.insertLargePart_cut_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_cut_lift

/-- info: 'SkewClassInflation.mem_largePartRanks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mem_largePartRanks

/-- info: 'SkewClassInflation.largePartRanks_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.largePartRanks_card

/-- info: 'SkewClassInflation.insertLargePart_retained_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_retained_iff

/-- info: 'SkewClassInflation.compositionProduct_copy_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_copy_cut

/-- info: 'SkewClassInflation.insertLargePart_internal_retained_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_internal_retained_iff

/-- info: 'SkewClassInflation.prefixEnds_eq_insert_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.prefixEnds_eq_insert_sum

/-- info: 'SkewClassInflation.compositionProduct_multiple_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_multiple_cut

/-- info: 'SkewClassInflation.insertLargePart_first_retained_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_first_retained_iff

/-- info: 'SkewClassInflation.insertLargePart_last_retained_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.insertLargePart_last_retained_iff

/-- info: 'SkewClassInflation.period_divisibility_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.period_divisibility_shift

/-- info: 'SkewClassInflation.periodMask_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodMask_periodic

/-- info: 'SkewClassInflation.periodMask_periodic_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodMask_periodic_value

/-- info: 'SkewClassInflation.periodMask_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodMask_refine

/-- info: 'SkewClassInflation.periodic_finset_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_finset_gcd

/-- info: 'SkewClassInflation.periodic_gcd_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_gcd_frontier

/-- info: 'SkewClassInflation.periodic_nat_of_dvd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_nat_of_dvd

/-- info: 'SkewClassInflation.periodic_of_residue_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_of_residue_check

/-- info: 'SkewClassInflation.guarded_overlap_period_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.guarded_overlap_period_vanish

/-- info: 'SkewClassInflation.compositionCutSign_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSign_reverse

/-- info: 'SkewClassInflation.nonreconstructible_signed_period_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonreconstructible_signed_period_witness

/-- info: 'SkewClassInflation.OverlapWord.cut_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.cut_shift

/-- info: 'SkewClassInflation.OverlapWord.cutSign_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.cutSign_shift

/-- info: 'SkewClassInflation.OverlapWord.cutSign_initial_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.cutSign_initial_zero

/-- info: 'SkewClassInflation.OverlapWord.reconstructible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.reconstructible

/-- info: 'SkewClassInflation.partitionOrders_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_mem_iff

/-- info: 'SkewClassInflation.partitionOrders_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_pos

/-- info: 'SkewClassInflation.partitionOrders_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_sum

/-- info: 'SkewClassInflation.coarseningPartition_eq_list_iff_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartition_eq_list_iff_order

/-- info: 'SkewClassInflation.coarseningInventory_count_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_count_orders

/-- info: 'SkewClassInflation.compositionCutResidue_cast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutResidue_cast

/-- info: 'SkewClassInflation.compositionCutResidue_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutResidue_lt

/-- info: 'SkewClassInflation.compositionCutResidue_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutResidue_nat

/-- info: 'SkewClassInflation.compositionCutResidue_periodic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutResidue_periodic

/-- info: 'SkewClassInflation.compositionCutResidue_add_nat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutResidue_add_nat

/-- info: 'SkewClassInflation.compositionCutResidue_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutResidue_dvd

/-- info: 'SkewClassInflation.compositionCutCodeNat_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutCodeNat_eq_iff

/-- info: 'SkewClassInflation.compositionCutCodeNat_cut_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutCodeNat_cut_iff

/-- info: 'SkewClassInflation.compositionCutCodeNat_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutCodeNat_disagreement

/-- info: 'SkewClassInflation.compositionCutSignInt_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSignInt_periodic

/-- info: 'SkewClassInflation.compositionCutCode_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutCode_periodic

/-- info: 'SkewClassInflation.prefixEnds_take_subset_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.prefixEnds_take_subset_cuts

/-- info: 'SkewClassInflation.wordProperCuts_take_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_take_subset

/-- info: 'SkewClassInflation.wordProperCuts_drop_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_drop_translate

/-- info: 'SkewClassInflation.take_sum_mem_wordProperCuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.take_sum_mem_wordProperCuts

/-- info: 'SkewClassInflation.word_splice_cuts_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.word_splice_cuts_subset

/-- info: 'SkewClassInflation.residueWord_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.residueWord_append

/-- info: 'SkewClassInflation.residueWord_eq_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.residueWord_eq_self

/-- info: 'SkewClassInflation.splice_residue_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splice_residue_word

/-- info: 'SkewClassInflation.splice_residue_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splice_residue_sum

/-- info: 'SkewClassInflation.splice_residue_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.splice_residue_length

/-- info: 'SkewClassInflation.residueWord_wordPadEnds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.residueWord_wordPadEnds

/-- info: 'SkewClassInflation.reflected_subset_cut_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.reflected_subset_cut_card

/-- info: 'SkewClassInflation.nonmultipleCuts_as_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonmultipleCuts_as_window

/-- info: 'SkewClassInflation.inventory_nonmultiple_cut_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_nonmultiple_cut_card

/-- info: 'SkewClassInflation.reflected_zero_mass_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.reflected_zero_mass_moment

/-- info: 'SkewClassInflation.reflected_balanced_cut_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.reflected_balanced_cut_sum

/-- info: 'SkewClassInflation.compositionCutType_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutType_le_two

/-- info: 'SkewClassInflation.compositionCutType_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutType_outside

/-- info: 'SkewClassInflation.compositionCutType_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutType_one_iff

/-- info: 'SkewClassInflation.coarseningInventory_cut_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_cut_type

/-- info: 'SkewClassInflation.coarseningInventory_cut_membership_of_not_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_cut_membership_of_not_one

/-- info: 'SkewClassInflation.coarseningInventory_reconstruct_of_no_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_reconstruct_of_no_single

/-- info: 'SkewClassInflation.ribbonReconstructible_of_no_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonReconstructible_of_no_single

/-- info: 'SkewClassInflation.exists_nonrotation_inventory_mate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_nonrotation_inventory_mate

/-- info: 'SkewClassInflation.exists_single_cut_of_not_reconstructible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_single_cut_of_not_reconstructible

/-- info: 'SkewClassInflation.exists_first_single_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_first_single_cut

/-- info: 'SkewClassInflation.properCuts_reverse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_reverse_iff

/-- info: 'SkewClassInflation.coarseningInventory_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningInventory_reverse

/-- info: 'SkewClassInflation.ribbonReconstructible_reverse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonReconstructible_reverse_iff

/-- info: 'SkewClassInflation.inventory_oriented_of_type_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_oriented_of_type_one

/-- info: 'SkewClassInflation.inventory_mate_oriented_at_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.inventory_mate_oriented_at_cut

/-- info: 'SkewClassInflation.exists_normalized_first_single_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_normalized_first_single_cut

/-- info: 'SkewClassInflation.exists_oriented_nonrotation_mate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_oriented_nonrotation_mate

/-- info: 'SkewClassInflation.residue_coarsening_cuts_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.residue_coarsening_cuts_subset

/-- info: 'SkewClassInflation.residue_coarsening_length_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.residue_coarsening_length_bound

/-- info: 'SkewClassInflation.nonzero_filter_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.nonzero_filter_sum

/-- info: 'SkewClassInflation.prefixEnds_mem_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.prefixEnds_mem_partial

/-- info: 'SkewClassInflation.wordProperCuts_prefixEnds_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_prefixEnds_of_lt

/-- info: 'SkewClassInflation.prefixEnds_filter_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.prefixEnds_filter_nonzero

/-- info: 'SkewClassInflation.sum_mod_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.sum_mod_map

/-- info: 'SkewClassInflation.residueWord_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.residueWord_pos

/-- info: 'SkewClassInflation.residueWord_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.residueWord_sum

/-- info: 'SkewClassInflation.ribbonChain_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonChain_word

/-- info: 'SkewClassInflation.ribbonChain_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonChain_gaps

/-- info: 'SkewClassInflation.ribbonChain_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonChain_schur

/-- info: 'SkewClassInflation.ribbonChain_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonChain_span

/-- info: 'SkewClassInflation.ribbonChain_eq_ribbonRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonChain_eq_ribbonRows

/-- info: 'SkewClassInflation.generatorSign_comp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorSign_comp_self

/-- info: 'SkewClassInflation.generatorSign_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorSign_injective

/-- info: 'SkewClassInflation.generatorSign_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorSign_complete

/-- info: 'SkewClassInflation.generatorSign_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorSign_product

/-- info: 'SkewClassInflation.generatorSign_ribbon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorSign_ribbon

/-- info: 'SkewClassInflation.generatorsOne_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorsOne_complete

/-- info: 'SkewClassInflation.generatorsOne_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorsOne_product

/-- info: 'SkewClassInflation.generatorsOne_unsignedCoarsening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.generatorsOne_unsignedCoarsening

/-- info: 'SkewClassInflation.unsignedCoarsening_eq_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unsignedCoarsening_eq_row_count

/-- info: 'SkewClassInflation.ribbon_eq_iff_unsignedCoarsening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_eq_iff_unsignedCoarsening

/-- info: 'SkewClassInflation.ribbon_coarsening_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_coarsening_expansion

/-- info: 'SkewClassInflation.coarseningWords_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningWords_composition

/-- info: 'SkewClassInflation.ribbon_coarsening_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_coarsening_formula

/-- info: 'SkewClassInflation.positiveWord_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.positiveWord_cons

/-- info: 'SkewClassInflation.positiveWord_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.positiveWord_values

/-- info: 'SkewClassInflation.positiveWord_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.positiveWord_length

/-- info: 'SkewClassInflation.positiveWord_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms SkewClassInflation.positiveWord_congr

/-- info: 'SkewClassInflation.positiveWord_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.positiveWord_monomial

/-- info: 'SkewClassInflation.coarseningPartition_card' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartition_card

/-- info: 'SkewClassInflation.coarseningPartition_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartition_values

/-- info: 'SkewClassInflation.coarseningPartitions_count_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_count_filter

/-- info: 'SkewClassInflation.coarseningPartition_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartition_mem

/-- info: 'SkewClassInflation.coarseningPartitions_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_card

/-- info: 'SkewClassInflation.coarsening_partition_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsening_partition_weight

/-- info: 'SkewClassInflation.partitionPolynomial_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionPolynomial_coefficient

/-- info: 'SkewClassInflation.partitionPolynomial_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionPolynomial_injective

/-- info: 'SkewClassInflation.unsignedCoarsening_eq_partitionPolynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.unsignedCoarsening_eq_partitionPolynomial

/-- info: 'SkewClassInflation.coarsening_partition_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsening_partition_count

/-- info: 'SkewClassInflation.ribbon_eq_iff_coarseningPartitions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_eq_iff_coarseningPartitions

/-- info: 'SkewClassInflation.coarseningPartition_cons_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartition_cons_false

/-- info: 'SkewClassInflation.coarseningPartition_cons_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartition_cons_true

/-- info: 'SkewClassInflation.coarseningPartitions_positive_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_positive_split

/-- info: 'SkewClassInflation.coarseningPartitions_positive_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_positive_one

/-- info: 'SkewClassInflation.coarsenRows_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_false

/-- info: 'SkewClassInflation.coarseningPartitions_rowPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_rowPartition

/-- info: 'SkewClassInflation.coarseningPartitions_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_row_sum

/-- info: 'SkewClassInflation.coarseningPartitions_eq_of_row_word_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningPartitions_eq_of_row_word_eq

/-- info: 'SkewClassInflation.coarsenRows_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_sum

/-- info: 'SkewClassInflation.coarsenRows_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_length

/-- info: 'SkewClassInflation.coarsenRows_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_pos

/-- info: 'SkewClassInflation.coarsenRows_ne_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_ne_nil

/-- info: 'SkewClassInflation.coarsenRows_head_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_head_lower

/-- info: 'SkewClassInflation.coarsenRows_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarsenRows_injective

/-- info: 'SkewClassInflation.ribbonRows_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonRows_word

/-- info: 'SkewClassInflation.ribbonRows_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonRows_schur

/-- info: 'SkewClassInflation.ribbonWord_eq_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonWord_eq_length

/-- info: 'SkewClassInflation.source_mem_normalizedInventoryMates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.source_mem_normalizedInventoryMates

/-- info: 'SkewClassInflation.cutDetermined_of_not_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_of_not_one

/-- info: 'SkewClassInflation.cutDetermined_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_first

/-- info: 'SkewClassInflation.undeterminedCuts_type_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedCuts_type_one

/-- info: 'SkewClassInflation.undeterminedCuts_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedCuts_nonempty

/-- info: 'SkewClassInflation.cutDetermined_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_reflect

/-- info: 'SkewClassInflation.undeterminedCuts_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedCuts_reflect

/-- info: 'SkewClassInflation.undeterminedCuts_after_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedCuts_after_first

/-- info: 'SkewClassInflation.undeterminedGcd_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedGcd_dvd

/-- info: 'SkewClassInflation.undeterminedGcd_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedGcd_pos

/-- info: 'SkewClassInflation.undeterminedGcd_lt_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedGcd_lt_weight

/-- info: 'SkewClassInflation.undeterminedGcd_dvd_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedGcd_dvd_weight

/-- info: 'SkewClassInflation.undeterminedGcd_periodic_divisors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedGcd_periodic_divisors

/-- info: 'SkewClassInflation.nonreconstructible_undeterminedGcd_properties' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonreconstructible_undeterminedGcd_properties

/-- info: 'SkewClassInflation.coarseningDeficit_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningDeficit_add

/-- info: 'SkewClassInflation.coarseningDeficit_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningDeficit_prefix

/-- info: 'SkewClassInflation.coarseningDeficit_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningDeficit_eq_sum

/-- info: 'SkewClassInflation.coarseningDeficit_positive_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningDeficit_positive_rec

/-- info: 'SkewClassInflation.coarseningDeficit_endpoint_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.coarseningDeficit_endpoint_count

/-- info: 'SkewClassInflation.ribbonEndpoints_of_coarsening_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonEndpoints_of_coarsening_eq

/-- info: 'SkewClassInflation.ribbon_endpoints_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_endpoints_of_eq

/-- info: 'SkewClassInflation.ribbonFactorComplete_of_reconstructible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonFactorComplete_of_reconstructible

/-- info: 'SkewClassInflation.ribbonFactorComplete_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonFactorComplete_congr

/-- info: 'SkewClassInflation.ribbonFactorComplete_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonFactorComplete_compose

/-- info: 'SkewClassInflation.exists_minimal_factor_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_minimal_factor_counterexample

/-- info: 'SkewClassInflation.factor_reversal_power_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.factor_reversal_power_equiv

/-- info: 'SkewClassInflation.factor_reversal_ribbon_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.factor_reversal_ribbon_eq

/-- info: 'SkewClassInflation.factor_reversal_inventory_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.factor_reversal_inventory_eq

/-- info: 'SkewClassInflation.factor_reversal_of_reconstructible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.factor_reversal_of_reconstructible

/-- info: 'SkewClassInflation.ribbonReconstructible_of_blocks_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonReconstructible_of_blocks_eq

/-- info: 'SkewClassInflation.ribbon_eq_reconstruct_of_reconstructible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_eq_reconstruct_of_reconstructible

/-- info: 'SkewClassInflation.ribbon_eq_blocks_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_eq_blocks_perm

/-- info: 'SkewClassInflation.ribbonClass_ones' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonClass_ones

/-- info: 'SkewClassInflation.ribbonWord_ofFn_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonWord_ofFn_reverse

/-- info: 'SkewClassInflation.ribbonWord_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonWord_reverse

/-- info: 'SkewClassInflation.ribbonWord_reverse_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonWord_reverse_word

/-- info: 'SkewClassInflation.sum_map_mul_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.sum_map_mul_right

/-- info: 'SkewClassInflation.wordProperCuts_map_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_map_mul

/-- info: 'SkewClassInflation.scalePositivePart_values' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.scalePositivePart_values

/-- info: 'SkewClassInflation.partitionOrders_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_scale

/-- info: 'SkewClassInflation.scaled_word_cuts_subset_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.scaled_word_cuts_subset_iff

/-- info: 'SkewClassInflation.cutDetermined_of_undeterminedGcd_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_of_undeterminedGcd_not_dvd

/-- info: 'SkewClassInflation.cutSign_shift_of_divisor_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutSign_shift_of_divisor_period

/-- info: 'SkewClassInflation.compositionCutType_one_of_nonzero_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutType_one_of_nonzero_sign

/-- info: 'SkewClassInflation.cutCodeNat_eq_of_nonzero_sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutCodeNat_eq_of_nonzero_sign_eq

/-- info: 'SkewClassInflation.actualCutBool_eq_of_nonzero_sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.actualCutBool_eq_of_nonzero_sign_eq

/-- info: 'SkewClassInflation.not_dvd_even_single_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.not_dvd_even_single_sum

/-- info: 'SkewClassInflation.off_multiple_period_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.off_multiple_period_mod

/-- info: 'SkewClassInflation.cut_membership_of_nonzero_sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cut_membership_of_nonzero_sign_eq

/-- info: 'SkewClassInflation.compositionCutSign_ne_zero_of_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSign_ne_zero_of_one

/-- info: 'SkewClassInflation.signed_period_cut_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.signed_period_cut_membership

/-- info: 'SkewClassInflation.ribbonReconstructible_of_prime_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonReconstructible_of_prime_weight

/-- info: 'SkewClassInflation.ribbonFactorComplete_of_prime_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonFactorComplete_of_prime_weight

/-- info: 'SkewClassInflation.stable_frontier_cutCode_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.stable_frontier_cutCode_period

/-- info: 'SkewClassInflation.undetermined_factorization_of_stable_frontier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_factorization_of_stable_frontier

/-- info: 'SkewClassInflation.symmetric_cuts_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.symmetric_cuts_reconstruct

/-- info: 'SkewClassInflation.ribbon_eq_reconstruct_of_symmetric_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_eq_reconstruct_of_symmetric_cuts

/-- info: 'SkewClassInflation.ribbon_eq_reconstruct_of_reverse_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_eq_reconstruct_of_reverse_word

/-- info: 'SkewClassInflation.wordProperCuts_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_three

/-- info: 'SkewClassInflation.partitionOrders_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.partitionOrders_three

/-- info: 'SkewClassInflation.threePart_retained_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threePart_retained_iff

/-- info: 'SkewClassInflation.threePart_partition_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threePart_partition_present

/-- info: 'SkewClassInflation.single_cut_reflect_iff_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.single_cut_reflect_iff_not

/-- info: 'SkewClassInflation.three_single_agree_iff_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.three_single_agree_iff_absent

/-- info: 'SkewClassInflation.three_single_agreement_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.three_single_agreement_invariant

/-- info: 'SkewClassInflation.threePart_count_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.threePart_count_distinct

/-- info: 'SkewClassInflation.even_cut_reflect_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.even_cut_reflect_iff

/-- info: 'SkewClassInflation.two_single_agreement_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.two_single_agreement_invariant

/-- info: 'SkewClassInflation.cutDetermined_actual_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutDetermined_actual_pair

/-- info: 'SkewClassInflation.exists_undetermined_bool_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.exists_undetermined_bool_flip

/-- info: 'SkewClassInflation.undetermined_fourPart_alternatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undetermined_fourPart_alternatives

