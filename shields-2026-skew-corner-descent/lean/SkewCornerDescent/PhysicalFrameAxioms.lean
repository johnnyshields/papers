/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalPeriodActivityJets
import SkewCornerDescent.Matrix.OriginalFirstNormalBalance
import SkewCornerDescent.Matrix.OriginalInternalFrontierActivities
import SkewCornerDescent.Matrix.OriginalOneActiveIntervalAlternative
import SkewCornerDescent.Matrix.OriginalClosureSelectedTranslation
import SkewCornerDescent.Matrix.OriginalIntrinsicOrder
import SkewCornerDescent.Matrix.OriginalResponsePrimeValuations
import SkewCornerDescent.CyclicPairCharges
import SkewCornerDescent.OrdinaryGaugeClassification

/-!
# Actual physical-frame and complete coverage axiom guards

Guards the complete original coefficient, literal-root, intrinsic-order,
response-valuation and finite ordinary-gauge constructions.
-/

/-- info: 'SkewCornerDescent.Matrix.ordinaryMonomialRatio_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.ordinaryMonomialRatio_constant

/-- info: 'SkewCornerDescent.Matrix.ordinaryMonomialDefect_detection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.ordinaryMonomialDefect_detection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_normal_defect_detection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_normal_defect_detection

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_literal_interval_or_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_literal_interval_or_defect

/-- info: 'SkewCornerDescent.Matrix.interiorBlock_label_le_iff_first_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.interiorBlock_label_le_iff_first_le

/-- info: 'SkewCornerDescent.Matrix.interiorBlock_label_le_iff_le_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.interiorBlock_label_le_iff_le_last

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_card_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_card_balance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_selected_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_selected_card

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_internal_interval_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_internal_interval_card

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_source_row_gap_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_source_row_gap_card

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_endpoint_profiles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_endpoint_profiles

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_end_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_end_length

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_source_row_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_source_row_gap

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_literal_row_gaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_literal_row_gaps

/-- info: 'SkewCornerDescent.Matrix.finite_row_displacement_of_periodic_differences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.finite_row_displacement_of_periodic_differences

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosurePhaseStateIndex_val' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosurePhaseStateIndex_val

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_period_of_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_phase_period_of_constant

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_source_row_displacement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_source_row_displacement

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_row_displacement_of_phase_gaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_row_displacement_of_phase_gaps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_row_displacement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_row_displacement

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_source_beta_gap_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_source_beta_gap_height

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_source_beta_displacement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_source_beta_displacement

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_beta_displacement_of_phase_heights' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_beta_displacement_of_phase_heights

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_periodic_beta_displacement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_periodic_beta_displacement

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedRowRightCell_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedRowRightCell_mem

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSourceRow_strictMono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSourceRow_strictMono

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSourceBeta_strictAnti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedSourceBeta_strictAnti

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedRowRightCell_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedRowRightCell_translate

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_row_rank_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_row_rank_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_selected_between' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_selected_between

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_row_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_row_coverage

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_selected_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_selected_translation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedRow_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedRow_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedRow_ne_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedRow_ne_selected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_row_frame_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_row_frame_bounds

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_interval_row_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_interval_row_bounds

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinal_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinal_injective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinal_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinal_surjective

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.twoPivotRowOrderCast_val' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.twoPivotRowOrderCast_val

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.twoPivotRowOrderCast_symm_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.twoPivotRowOrderCast_symm_val

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinal_lt_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinal_lt_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinalBeta_strictAnti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalRowOrdinalBeta_strictAnti

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_copy_ordinal_strictMono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_copy_ordinal_strictMono

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_copy_relative_row_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInterval_copy_relative_row_rank

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_row_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_row_frame

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_physical_row_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_physical_row_map

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_start_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_start_length

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_row_col_rank_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemoved_row_col_rank_difference

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_selected_endpoint_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_selected_endpoint_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_selected_row_ordinal_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_selected_row_ordinal_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_copy_selected_flags' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_copy_selected_flags

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_physical_both_maps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_physical_both_maps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_col_rank_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_col_rank_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_col_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_consecutive_col_coverage

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalFullSourceIndex_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalFullSourceIndex_bounds

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalFullSourceIndex_relative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalFullSourceIndex_relative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalIntervalShift_eq_beta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalIntervalShift_eq_beta

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_equal_height_pivot_betas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_equal_height_pivot_betas

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_initial_frame_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_initial_frame_bounds

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_initial_last_sub_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_initial_last_sub_start

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_full_pivot_ranks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_full_pivot_ranks

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_full_betas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_full_betas

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_parent_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_parent_rows

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalIntervalShift_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalIntervalShift_symm

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalLiteralCopy_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalLiteralCopy_symm

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalCellShift_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalCellShift_symm

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_parent_strip_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_parent_strip_point

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_parent_strips' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_literal_parent_strips

/-- info: 'SkewCornerDescent.CyclicWindows.phaseCycle_shift_invariant_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.phaseCycle_shift_invariant_periodic

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_incoming_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_incoming_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_parent_strip_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_parent_strip_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralPeriod_fixed_cell_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralPeriod_fixed_cell_shift

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_fixed_parent_strips' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_fixed_parent_strips

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_selected_beta_copy_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_selected_beta_copy_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalCellShift_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalCellShift_content

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_period_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_period_content

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_true_cap_room' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_true_cap_room

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_root_span_strips' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_root_span_strips

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalParentStrip_cover_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalParentStrip_cover_middle

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalParentStrip_cover_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalParentStrip_cover_content

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalMiddleBand_forward_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalMiddleBand_forward_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalMiddleBand_backward_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalMiddleBand_backward_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_middle_betas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_middle_betas

/-- info: 'SkewCornerDescent.twoCopy_middle_period_full_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.twoCopy_middle_period_full_windows

/-- info: 'SkewCornerDescent.fullWindow_period_ordinary_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.fullWindow_period_ordinary_boundary

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_full_windows_of_strip_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinaryClosure_full_windows_of_strip_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_literal_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_no_discrepancy_literal_root

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_normal_interface' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_normal_interface

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_positive_block_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_positive_block_selected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_nonselected_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_nonselected_empty

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_nonselected_single_vertex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_nonselected_single_vertex

/-- info: 'SkewCornerDescent.Matrix.ordinaryEndpointProfile_complete_convolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.ordinaryEndpointProfile_complete_convolution

/-- info: 'SkewCornerDescent.Matrix.betaEndpointLeftPolynomial_column_convolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.betaEndpointLeftPolynomial_column_convolution

/-- info: 'SkewCornerDescent.Matrix.completePrefixRecurrenceValue_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.completePrefixRecurrenceValue_congr

/-- info: 'SkewCornerDescent.Matrix.ordinary_profile_coeff_of_no_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.ordinary_profile_coeff_of_no_distance

/-- info: 'SkewCornerDescent.Matrix.ordinary_profile_nonzero_coefficient_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.ordinary_profile_nonzero_coefficient_support

/-- info: 'SkewCornerDescent.Matrix.betaEndpointLeftPolynomial_column_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.betaEndpointLeftPolynomial_column_coefficient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_visible_nonzero_coefficient_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_visible_nonzero_coefficient_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_visible_left_coefficient_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_visible_left_coefficient_cases

/-- info: 'SkewCornerDescent.Matrix.polynomial_prefix_binary_differences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.polynomial_prefix_binary_differences

/-- info: 'SkewCornerDescent.BinaryTransitions.cyclic_curvature_ne_zero_of_nonconstant_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.BinaryTransitions.cyclic_curvature_ne_zero_of_nonconstant_closure

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_visible_left_coefficient_mem_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_visible_left_coefficient_mem_lower

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_binary_first_differences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_binary_first_differences

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_cross_profile_binary_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_cross_profile_binary_energy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_positive_normal_resolving_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_positive_normal_resolving_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_incoming_low_coeff_eq_of_core_jets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_incoming_low_coeff_eq_of_core_jets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_phase_binary_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_phase_binary_alternative

/-- info: 'SkewCornerDescent.Matrix.normalCyclicFirstCharge_clear_common_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalCyclicFirstCharge_clear_common_residue

/-- info: 'SkewCornerDescent.Matrix.weighted_normalCyclicFirstCharge_clear_common_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.weighted_normalCyclicFirstCharge_clear_common_residue

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_self_polynomial_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_self_polynomial_correction

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_weighted_self_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_weighted_self_correction

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_polynomial_laurent_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selected_core_polynomial_laurent_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_resolving_residue_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_resolving_residue_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalCoefficient_resolving_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalCoefficient_resolving_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cleared_onsite_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cleared_onsite_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_weighted_cleared_onsite_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_weighted_cleared_onsite_derivative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_endpoint_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_endpoint_distance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_adjacent_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_adjacent_distance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cross_residue_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cross_residue_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cyclic_cross_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cyclic_cross_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cyclic_resolving_cross_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cyclic_resolving_cross_gradient

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cyclic_binary_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_cyclic_binary_energy

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_pure_cyclic_first_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_pure_cyclic_first_nonzero

/-- info: 'SkewCornerDescent.BinaryTransitions.binary_profile_square_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.BinaryTransitions.binary_profile_square_sum

/-- info: 'SkewCornerDescent.BinaryTransitions.weighted_binary_profile_energy_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.BinaryTransitions.weighted_binary_profile_energy_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_closure_heights' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_closure_heights

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_constant_internal_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_constant_internal_class

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_constant_core_profiles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_constant_core_profiles

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_center_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_internal_center_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_internal_center_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_internal_center_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_constant_ordinary_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_constant_ordinary_pin

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_constant_internal_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_constant_internal_data

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_constant_internal_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalClosure_constant_internal_data

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_shared_profile_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalComparison_shared_profile_prefix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_component_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_component_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_constant_cycle_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_constant_cycle_alternative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPurePrimitive_first_or_literal_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPurePrimitive_first_or_literal_root

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_internal_eq_unique_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPrimitive_internal_eq_unique_active

/-- info: 'SkewCornerDescent.Matrix.normalCyclicFirstCharge_matrix_length_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normalCyclicFirstCharge_matrix_length_congr

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinary_support_interface' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalOrdinary_support_interface

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalIntrinsic_order_or_literal_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalIntrinsic_order_or_literal_root

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_intrinsic_order_or_literal_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalPure_intrinsic_order_or_literal_root

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalManyActive_intrinsic_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalManyActive_intrinsic_order

/-- info: 'SkewCornerDescent.Matrix.exists_faithful_original_coordinate_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.exists_faithful_original_coordinate_slice

/-- info: 'SkewCornerDescent.Matrix.originalCoordinateFieldSlice_algebraMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.originalCoordinateFieldSlice_algebraMap

/-- info: 'SkewCornerDescent.Matrix.originalCoordinateFieldSlice_off_coordinate_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.originalCoordinateFieldSlice_off_coordinate_unit

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_response_prime_valuations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_response_prime_valuations

/-- info: 'SkewCornerDescent.exists_faithful_rational_evaluation_on_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.exists_faithful_rational_evaluation_on_open

/-- info: 'SkewCornerDescent.profileArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileArea

/-- info: 'SkewCornerDescent.singleRowProfile' does not depend on any axioms -/
#guard_msgs in
#print axioms
  SkewCornerDescent.singleRowProfile

/-- info: 'SkewCornerDescent.prependRowProfile' depends on axioms: [propext] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.prependRowProfile

/-- info: 'SkewCornerDescent.tailRowProfile' does not depend on any axioms -/
#guard_msgs in
#print axioms
  SkewCornerDescent.tailRowProfile

/-- info: 'SkewCornerDescent.profileArea_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileArea_pos

/-- info: 'SkewCornerDescent.profileArea_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileArea_tail

/-- info: 'SkewCornerDescent.profileArea_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileArea_single

/-- info: 'SkewCornerDescent.profileArea_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileArea_prepend

/-- info: 'SkewCornerDescent.prepend_tailRowProfile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.prepend_tailRowProfile

/-- info: 'SkewCornerDescent.profilesWithFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profilesWithFuel

/-- info: 'SkewCornerDescent.profilesOfArea' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profilesOfArea

/-- info: 'SkewCornerDescent.profileRows_le_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileRows_le_area

/-- info: 'SkewCornerDescent.profile_mem_profilesWithFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profile_mem_profilesWithFuel

/-- info: 'SkewCornerDescent.profile_mem_profilesOfArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profile_mem_profilesOfArea

/-- info: 'SkewCornerDescent.mem_profilesWithFuel_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.mem_profilesWithFuel_area

/-- info: 'SkewCornerDescent.mem_profilesOfArea_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.mem_profilesOfArea_area

/-- info: 'SkewCornerDescent.profilesAtMost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profilesAtMost

/-- info: 'SkewCornerDescent.profile_mem_profilesAtMost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profile_mem_profilesAtMost

/-- info: 'SkewCornerDescent.mem_profilesAtMost_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.mem_profilesAtMost_area

/-- info: 'SkewCornerDescent.profileArea_eq_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileArea_eq_card

/-- info: 'SkewCornerDescent.diagram_mem_profile_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.diagram_mem_profile_census

/-- info: 'SkewGluing.MarkedInner.upper_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.upper_translateBy

/-- info: 'SkewGluing.MarkedInner.middle_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.middle_translateBy

/-- info: 'SkewGluing.MarkedInner.lowerH_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.lowerH_translateBy

/-- info: 'SkewGluing.MarkedInner.lowerV_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.lowerV_translateBy

/-- info: 'SkewGluing.MarkedInner.upperH_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.upperH_translateBy

/-- info: 'SkewGluing.MarkedInner.upperV_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.upperV_translateBy

/-- info: 'SkewGluing.MarkedInner.attachmentMatches_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.attachmentMatches_translateBy

/-- info: 'SkewGluing.MarkedInner.isNonemptyMark_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.isNonemptyMark_translateBy

/-- info: 'SkewGluing.MarkedInner.isMaximalAtDisplacement_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.isMaximalAtDisplacement_translateBy

/-- info: 'SkewGluing.MarkedInner.mem_periodicUnion_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.mem_periodicUnion_translateBy

/-- info: 'SkewGluing.MarkedInner.mem_middle_copy_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.mem_middle_copy_translateBy

/-- info: 'SkewGluing.MarkedInner.noHatAdjacency_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.noHatAdjacency_translateBy

/-- info: 'SkewGluing.MarkedInner.isLegal_translateBy_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.isLegal_translateBy_nonempty

/-- info: 'SkewGluing.MarkedInner.translateBy_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.translateBy_add

/-- info: 'SkewGluing.MarkedInner.translateBy_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewGluing.MarkedInner.translateBy_zero

/-- info: 'SkewCornerDescent.censusLowerBand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.censusLowerBand

/-- info: 'SkewCornerDescent.positiveMarkCandidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.positiveMarkCandidates

/-- info: 'SkewCornerDescent.positiveMarkCandidates_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.positiveMarkCandidates_complete

/-- info: 'SkewCornerDescent.ordinaryGeometricMarks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryGeometricMarks

/-- info: 'SkewCornerDescent.ordinaryGeometricMarks_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryGeometricMarks_complete

/-- info: 'SkewCornerDescent.profileDiagramCensus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileDiagramCensus

/-- info: 'SkewCornerDescent.profileDiagramCensus_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.profileDiagramCensus_complete

/-- info: 'SkewCornerDescent.diagramCensusUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.diagramCensusUnion

/-- info: 'SkewCornerDescent.mem_diagramCensusUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.mem_diagramCensusUnion

/-- info: 'SkewCornerDescent.normalizeMarkedInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.normalizeMarkedInner

/-- info: 'SkewCornerDescent.positiveOrdinaryGaugePairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.positiveOrdinaryGaugePairs

/-- info: 'SkewCornerDescent.ordinaryGaugeCensus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryGaugeCensus

/-- info: 'SkewCornerDescent.ordinaryGaugeCensus_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryGaugeCensus_complete

/-- info: 'SkewCornerDescent.ordinaryAdjacentCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryAdjacentCells

/-- info: 'SkewCornerDescent.ordinaryHypothesisV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryHypothesisV

/-- info: 'SkewCornerDescent.ordinaryVFailureCensus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryVFailureCensus

/-- info: 'SkewCornerDescent.ordinaryAdjacentCells_card_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryAdjacentCells_card_one_iff

/-- info: 'SkewCornerDescent.ordinaryHypothesisV_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryHypothesisV_iff

/-- info: 'SkewCornerDescent.ordinaryAdjacentCells_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryAdjacentCells_translate

/-- info: 'SkewCornerDescent.ordinaryHypothesisV_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryHypothesisV_translateBy

/-- info: 'SkewCornerDescent.ordinaryGauge_nonempty_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryGauge_nonempty_other

/-- info: 'SkewCornerDescent.ordinaryVFailureCensus_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryVFailureCensus_complete

/-- info: 'SkewCornerDescent.normalizeMarkedInner_translateBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.normalizeMarkedInner_translateBy

/-- info: 'SkewCornerDescent.normalizeMarkedInner_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.normalizeMarkedInner_eq_iff

/-- info: 'SkewCornerDescent.ordinary_gauge_census_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinary_gauge_census_eight

/-- info: 'SkewCornerDescent.ordinaryGauge_through_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryGauge_through_eight

/-- info: 'SkewCornerDescent.ordinaryVFailure_through_eight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryVFailure_through_eight_iff

/-- info: 'SkewCornerDescent.ordinaryGauge_through_eight_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.ordinaryGauge_through_eight_compose
