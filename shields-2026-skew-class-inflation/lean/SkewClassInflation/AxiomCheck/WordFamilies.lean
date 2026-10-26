/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CutClosureFactorization
import SkewClassInflation.EvenCutFrontierReflection
import SkewClassInflation.SmallRibbonReconstruction
import SkewClassInflation.QuaternaryRibbonFactorization

/-!
# Exact WordFamilies axiom footprints

Every expected message is the observed kernel footprint of the declaration it guards.
-/

/-- info: 'SkewClassInflation.antisymmetric_residue_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.antisymmetric_residue_cycle

/-- info: 'SkewClassInflation.antisymmetric_interval_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.antisymmetric_interval_extension

/-- info: 'SkewClassInflation.antisymmetric_interval_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.antisymmetric_interval_gcd

/-- info: 'SkewClassInflation.properCuts_eq_suffixSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_eq_suffixSet

/-- info: 'SkewClassInflation.properCuts_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_bounds

/-- info: 'SkewClassInflation.mem_properCuts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.mem_properCuts_iff

/-- info: 'SkewClassInflation.properCuts_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_nonempty

/-- info: 'SkewClassInflation.properCuts_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_injective

/-- info: 'SkewClassInflation.properCuts_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_cast

/-- info: 'SkewClassInflation.properCuts_eq_of_blocks_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_eq_of_blocks_eq

/-- info: 'SkewClassInflation.compositionProduct_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_cuts

/-- info: 'SkewClassInflation.compositionProduct_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_internal

/-- info: 'SkewClassInflation.proper_factorization_of_actual_frontier_propagation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.proper_factorization_of_actual_frontier_propagation

/-- info: 'SkewClassInflation.cutClosureState_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutClosureState_succ

/-- info: 'SkewClassInflation.cutClosureState_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutClosureState_pos

/-- info: 'SkewClassInflation.cutClosureState_dvd_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutClosureState_dvd_weight

/-- info: 'SkewClassInflation.cutClosurePrevious_dvd_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutClosurePrevious_dvd_weight

/-- info: 'SkewClassInflation.cutClosureState_lt_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutClosureState_lt_weight

/-- info: 'SkewClassInflation.cutClosureState_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutClosureState_gcd

/-- info: 'SkewClassInflation.cutClosureState_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.cutClosureState_invariants

/-- info: 'SkewClassInflation.compositionCutType_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutType_reflect

/-- info: 'SkewClassInflation.evenCutDisagreements_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutDisagreements_negative

/-- info: 'SkewClassInflation.evenCutClosure_nonzero_signed_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosure_nonzero_signed_refinement

/-- info: 'SkewClassInflation.evenCutClosure_strong_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutClosure_strong_refinement

/-- info: 'SkewClassInflation.guarded_period_reduce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.guarded_period_reduce

/-- info: 'SkewClassInflation.guarded_period_extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.guarded_period_extend

/-- info: 'SkewClassInflation.compositionCutSignInt_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCutSignInt_neg

/-- info: 'SkewClassInflation.evenCutDisagreements_negative_sign_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.evenCutDisagreements_negative_sign_zero

/-- info: 'SkewClassInflation.nonzero_forward_perm_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nonzero_forward_perm_invariant

/-- info: 'SkewClassInflation.periodic_of_nonzero_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_of_nonzero_forward

/-- info: 'SkewClassInflation.masked_period_of_odd_shift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.masked_period_of_odd_shift_zero

/-- info: 'SkewClassInflation.OverlapWord.merged_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.merged_eq

/-- info: 'SkewClassInflation.OverlapWord.merged_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.merged_sum

/-- info: 'SkewClassInflation.OverlapWord.prefix_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.prefix_succ

/-- info: 'SkewClassInflation.OverlapWord.prefix_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.prefix_pos

/-- info: 'SkewClassInflation.OverlapWord.prefix_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.prefix_sum

/-- info: 'SkewClassInflation.OverlapWord.cuts_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.cuts_bounds

/-- info: 'SkewClassInflation.OverlapWord.delta_lt_period' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.delta_lt_period

/-- info: 'SkewClassInflation.OverlapWord.prefix_cuts_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.prefix_cuts_succ

/-- info: 'SkewClassInflation.OverlapWord.properCuts_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.properCuts_composition

/-- info: 'SkewClassInflation.OverlapWord.properCuts_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.properCuts_periodic

/-- info: 'SkewClassInflation.OverlapWord.composition_eq_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.composition_eq_periodic

/-- info: 'SkewClassInflation.OverlapWord.no_right_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.no_right_factor

/-- info: 'SkewClassInflation.OverlapWord.composition_palindrome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.composition_palindrome

/-- info: 'SkewClassInflation.OverlapWord.composition_palindrome_of_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.OverlapWord.composition_palindrome_of_base

/-- info: 'SkewClassInflation.compositionFromCuts_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionFromCuts_internal

/-- info: 'SkewClassInflation.periodic_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_factorization

/-- info: 'SkewClassInflation.periodicInner_multipart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodicInner_multipart

/-- info: 'SkewClassInflation.compositionProduct_cut_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_cut_periodic

/-- info: 'SkewClassInflation.periodic_factorization_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodic_factorization_iff

/-- info: 'SkewClassInflation.periodicOuter_compositionProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodicOuter_compositionProduct

/-- info: 'SkewClassInflation.periodicInner_compositionProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodicInner_compositionProduct

/-- info: 'SkewClassInflation.ribbon_cons_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_cons_near

/-- info: 'SkewClassInflation.ribbon_concat_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_concat_near

/-- info: 'SkewClassInflation.wordCompose_near_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_near_head

/-- info: 'SkewClassInflation.ribbon_append_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_append_near

/-- info: 'SkewClassInflation.ribbonProductSubstitution_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonProductSubstitution_complete

/-- info: 'SkewClassInflation.ribbonProductSubstitution_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonProductSubstitution_word

/-- info: 'SkewClassInflation.ribbon_composition_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbon_composition_substitution

/-- info: 'SkewClassInflation.compositionProduct_ribbon_eq_of_outer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_ribbon_eq_of_outer_eq

/-- info: 'SkewClassInflation.compositionProduct_outer_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_outer_reverse

/-- info: 'SkewClassInflation.ribbonPowerEquiv_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonPowerEquiv_refl

/-- info: 'SkewClassInflation.ribbonPowerEquiv_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonPowerEquiv_reverse

/-- info: 'SkewClassInflation.ribbonProductSubstitution_eq_of_powerEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonProductSubstitution_eq_of_powerEquiv

/-- info: 'SkewClassInflation.ribbonPowerEquiv_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonPowerEquiv_compose

/-- info: 'SkewClassInflation.wordCompose_eq_flatten' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_eq_flatten

/-- info: 'SkewClassInflation.wordCompose_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_sum

/-- info: 'SkewClassInflation.wordCompose_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_pos

/-- info: 'SkewClassInflation.wordProperCuts_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_cons

/-- info: 'SkewClassInflation.wordProperCuts_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_bounds

/-- info: 'SkewClassInflation.wordCompose_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_cuts

/-- info: 'SkewClassInflation.wordCompose_cuts_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_cuts_mod

/-- info: 'SkewClassInflation.compositionProduct_eq_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_eq_literal

/-- info: 'SkewClassInflation.compositionProduct_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionProduct_blocks

/-- info: 'SkewClassInflation.wordCompose_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_append

/-- info: 'SkewClassInflation.wordCompose_near' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_near

/-- info: 'SkewClassInflation.wordCompose_nearPower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordCompose_nearPower

/-- info: 'SkewClassInflation.wordProperCuts_append_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_append_single

/-- info: 'SkewClassInflation.wordProperCuts_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_blocks

/-- info: 'SkewClassInflation.wordNear_append_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_append_cons

/-- info: 'SkewClassInflation.wordNear_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_sum

/-- info: 'SkewClassInflation.wordNear_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_pos

/-- info: 'SkewClassInflation.wordProperCuts_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_append

/-- info: 'SkewClassInflation.wordProperCuts_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_near

/-- info: 'SkewClassInflation.wordProperCuts_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_nil

/-- info: 'SkewClassInflation.wordProperCuts_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_single

/-- info: 'SkewClassInflation.wordNear_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_nil

/-- info: 'SkewClassInflation.word_ne_nil_of_sum_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.word_ne_nil_of_sum_pos

/-- info: 'SkewClassInflation.wordNearPower_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNearPower_sum

/-- info: 'SkewClassInflation.wordNearPower_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNearPower_pos

/-- info: 'SkewClassInflation.wordNearPower_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNearPower_cuts

/-- info: 'SkewClassInflation.wordNear_append_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_append_left

/-- info: 'SkewClassInflation.wordNear_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_assoc

/-- info: 'SkewClassInflation.wordNearPower_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNearPower_add

/-- info: 'SkewClassInflation.wordNear_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_ne_nil

/-- info: 'SkewClassInflation.wordNear_append_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_append_right

/-- info: 'SkewClassInflation.wordNear_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_cons

/-- info: 'SkewClassInflation.wordNear_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNear_reverse

/-- info: 'SkewClassInflation.wordNearPower_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordNearPower_reverse

/-- info: 'SkewClassInflation.wordProperCuts_mem_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_mem_partial

/-- info: 'SkewClassInflation.wordProperCuts_reverse_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_reverse_sum

/-- info: 'SkewClassInflation.wordProperCuts_reverse_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordProperCuts_reverse_reflect

/-- info: 'SkewClassInflation.prefixEnds_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.prefixEnds_append

/-- info: 'SkewClassInflation.prefixEnds_head_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.prefixEnds_head_add

/-- info: 'SkewClassInflation.wordSuffixSet_reverse_append_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.wordSuffixSet_reverse_append_single

/-- info: 'SkewClassInflation.properCuts_blocks_append_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.properCuts_blocks_append_single

/-- info: 'SkewClassInflation.prefixEnds_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.prefixEnds_bounds

/-- info: 'SkewClassInflation.zero_frontier_masked_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_frontier_masked_periods

/-- info: 'SkewClassInflation.zero_frontier_mask_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_frontier_mask_vanishes

/-- info: 'SkewClassInflation.zero_frontier_masks_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_frontier_masks_eq

/-- info: 'SkewClassInflation.zero_frontier_preserves_nonzero_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.zero_frontier_preserves_nonzero_witness

/-- info: 'SkewClassInflation.periodMask_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.periodMask_neg

/-- info: 'SkewClassInflation.odd_two_periodic_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.odd_two_periodic_eq_zero

/-- info: 'SkewClassInflation.undeterminedGcd_ge_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.undeterminedGcd_ge_three

/-- info: 'SkewClassInflation.three_mul_undeterminedGcd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.three_mul_undeterminedGcd_le

/-- info: 'SkewClassInflation.nine_le_weight_of_not_reconstructible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.nine_le_weight_of_not_reconstructible

/-- info: 'SkewClassInflation.ribbonReconstructible_of_small_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonReconstructible_of_small_weight

/-- info: 'SkewClassInflation.ribbonFactorComplete_of_small_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ribbonFactorComplete_of_small_weight

