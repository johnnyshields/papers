/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowGapAssembly
import SkewCornerDescent.Matrix.TranslatedResponses
import SkewCornerDescent.Matrix.OriginalWindowRemovedBlocks
import SkewCornerDescent.Matrix.OriginalWindowSourceEquiv
import SkewCornerDescent.Matrix.OriginalWholeWindowResponses
import SkewCornerDescent.Matrix.OriginalWindowConvexity
import SkewCornerDescent.Matrix.OriginalWindowRetainedResponses
import SkewCornerDescent.Matrix.OriginalWindowResponsePeriod
import SkewCornerDescent.Matrix.OriginalWindowRestrictionWord
import SkewCornerDescent.Matrix.OriginalAmalgamationWord
import SkewCornerDescent.Matrix.OriginalWindowCommonCaps
import SkewCornerDescent.Matrix.OriginalWindowActiveClasses
import SkewCornerDescent.Matrix.OriginalWindowSingleGaps
import SkewCornerDescent.Matrix.OriginalWindowEndClasses
import SkewCornerDescent.Matrix.OriginalWindowRationalFactors
import SkewCornerDescent.Matrix.OriginalAmalgamationRowAlignment

/-!
# Axiom guards for actual component inventories and complete response translation

Every guarded statement uses only the documented standard Lean axioms.
-/

namespace SkewCornerDescent


/-- info: 'SkewCornerDescent.edgeComponents_prefix_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edgeComponents_prefix_of_gap

/-- info: 'SkewCornerDescent.privateDiagonal_component_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms privateDiagonal_component_inventory

/-- info: 'SkewCornerDescent.literalWindow_component_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalWindow_component_inventory

/-- info: 'SkewCornerDescent.Matrix.intervalMatrix_affine_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.intervalMatrix_affine_reindex

/-- info: 'SkewCornerDescent.Matrix.intervalResponse_affine_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.intervalResponse_affine_reindex

/--
info: 'SkewCornerDescent.edgeComponents_filter_of_no_cross_adj' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.edgeComponents_filter_of_no_cross_adj

/--
info: 'SkewCornerDescent.edgeComponents_interval_of_gaps' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.edgeComponents_interval_of_gaps

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_interval_of_gaps'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_interval_of_gaps

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_private_interval'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_private_interval

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_literal_windows' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.selectedComponentInventory_literal_windows

/--
info: 'SkewCornerDescent.fin_upper_window_ranks' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.fin_upper_window_ranks

/--
info: 'SkewCornerDescent.fin_lower_window_ranks' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.fin_lower_window_ranks

/--
info: 'SkewCornerDescent.fin_end_windows_orderIso_rank' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.fin_end_windows_orderIso_rank

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_occurrence' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_occurrence

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_orderIso' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_orderIso

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_maxContent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_maxContent

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_maxContent_strictAnti' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_maxContent_strictAnti

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_content_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_content_bounds

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_prefix_upper' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_prefix_upper

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_suffix_lower' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_suffix_lower

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_prefix_iff_rank' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_prefix_iff_rank

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_rank_shift' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_rank_shift

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_index_translation' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_index_translation

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_gap_period' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_gap_period

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_inventory_card' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_inventory_card

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_count' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_selected_count

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalProfile_interior_boundary_gaps' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalProfile_interior_boundary_gaps

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_gap_period_from_profile' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_gap_period_from_profile

/--
info: 'SkewCornerDescent.Matrix.originalProfile_row_fiber_endpoints' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalProfile_row_fiber_endpoints

/--
info: 'SkewCornerDescent.Matrix.originalWindow_row_fiber' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalWindow_row_fiber

/--
info: 'SkewCornerDescent.Matrix.originalWindow_row_endpoints' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalWindow_row_endpoints

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_row_exists' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interiorBlockCells_row_exists

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_row_bounds' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interiorBlockCells_row_bounds

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_translated_row_extremes' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interiorBlockCells_translated_row_extremes

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_translated_row_endpoints' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interiorBlockCells_translated_row_endpoints

/--
info: 'SkewCornerDescent.Matrix.interiorBlockCells_translated_length' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interiorBlockCells_translated_length

/--
info: 'SkewCornerDescent.Matrix.originalTranslatedBlockIndex_endpoints' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalTranslatedBlockIndex_endpoints

/--
info: 'SkewCornerDescent.Matrix.originalTranslatedBlock_matrix' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalTranslatedBlock_matrix

/--
info: 'SkewCornerDescent.Matrix.exists_originalBlock_of_component' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.exists_originalBlock_of_component

/--
info: 'SkewCornerDescent.Matrix.originalBlock_nonempty_cells_unique' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalBlock_nonempty_cells_unique

/--
info: 'SkewCornerDescent.Matrix.originalWindow_nonempty_block_occurrence' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalWindow_nonempty_block_occurrence

/--
info: 'SkewCornerDescent.Matrix.originalWindow_cell_translation' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalWindow_cell_translation

/--
info: 'SkewCornerDescent.Matrix.originalWindow_complementary_position' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalWindow_complementary_position

/--
info: 'SkewCornerDescent.Matrix.originalWindow_unit_pivot' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalWindow_unit_pivot

/--
info: 'SkewCornerDescent.Matrix.originalWindow_source_orderIso' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalWindow_source_orderIso

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_translated_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_translated_endpoints

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockSelected_translated_iff' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockSelected_translated_iff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_size' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_size

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_row_position'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_row_position

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_endpoints

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_entry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalTranslatedBlock_removed_entry

/--
info: 'SkewCornerDescent.Matrix.interior_empty_block_extremes' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interior_empty_block_extremes

/--
info: 'SkewCornerDescent.Matrix.interior_empty_block_length' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.interior_empty_block_length

/--
info: 'SkewCornerDescent.Matrix.originalBlocks_last_mono' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalBlocks_last_mono

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalEmptyBlock_remaining_size' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalEmptyBlock_remaining_size

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalEmptyBlock_remaining_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalEmptyBlock_remaining_endpoints

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalEmptyBlock_translated_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalEmptyBlock_translated_endpoints

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_remaining_occurrence' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_remaining_occurrence

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_remaining_orderIso' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_remaining_orderIso

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_remaining_matrix_equiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_remaining_matrix_equiv

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWholeWindowMatrix_blockTriangular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWholeWindowMatrix_blockTriangular

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWholeWindowMatrix_diagonal' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWholeWindowMatrix_diagonal

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalWholeWindowMatrix' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.not_dvd_originalWholeWindowMatrix

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWholeWindowResponse_translate'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWholeWindowResponse_translate

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlock_window_bounds' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlock_window_bounds

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_bounds' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_bounds

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_between' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_between

/--
info: 'SkewCornerDescent.Matrix.originalBlocks_label_strictMono' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalBlocks_label_strictMono

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseInterval_block_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponseInterval_block_bounds

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_retained_interval_equiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_retained_interval_equiv

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_window_translate'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_window_translate

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_window_translate' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_window_translate

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_local_response_period'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_local_response_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_response_period' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_internal_response_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_response_period_from_profile'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_response_period_from_profile

/-- info: 'SkewCornerDescent.Matrix.originalLiteralWindow_profile_bounds' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalLiteralWindow_profile_bounds

/-- info: 'SkewCornerDescent.Matrix.originalLiteralWindow_cell_translation' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalLiteralWindow_cell_translation

/-- info: 'SkewCornerDescent.Matrix.originalLiteralWindow_complementary_position' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalLiteralWindow_complementary_position

/-- info: 'SkewCornerDescent.Matrix.originalLiteralWindow_nonempty_block_occurrence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalLiteralWindow_nonempty_block_occurrence

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_remaining_occurrence' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_remaining_occurrence

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_remaining_orderIso' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_remaining_orderIso

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_retained_interval_equiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_retained_interval_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_literal_window_translate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_literal_window_translate

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_selected_occurrence' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_selected_occurrence

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_selected_orderIso' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_selected_orderIso

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_profile_selected_orderIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_profile_selected_orderIso

/-- info: 'SkewCornerDescent.fin_initial_window_orderIso_rank' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.fin_initial_window_orderIso_rank

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_restriction_selected_rank' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_restriction_selected_rank

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalResponse_eq_local' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalResponse_eq_local

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_selected_count_le' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_selected_count_le

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_restriction_internal_word' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_restriction_internal_word

/-- info: 'SkewCornerDescent.literalOverlap_complete_end_windows' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.literalOverlap_complete_end_windows

/-- info: 'SkewCornerDescent.literalOverlap_content_extrema' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.literalOverlap_content_extrema

/-- info: 'SkewCornerDescent.Matrix.originalAmalgamation_profile_extrema' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalAmalgamation_profile_extrema

/-- info: 'SkewCornerDescent.Matrix.contentZero_translate_filter' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.contentZero_translate_filter

/-- info: 'SkewCornerDescent.Matrix.originalAmalgamation_complete_end_windows' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalAmalgamation_complete_end_windows

/-- info: 'SkewCornerDescent.Matrix.originalAmalgamation_private_end_cuts' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.originalAmalgamation_private_end_cuts

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_selected_inventory' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_selected_inventory

/-- info: 'SkewCornerDescent.fin_final_window_orderIso_rank' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.fin_final_window_orderIso_rank

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_restriction_selected_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_restriction_selected_rank

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_restriction_internal_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_restriction_internal_word

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_internal_word' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_internal_word

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_of_endpoint_bounds' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_of_endpoint_bounds

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_before_selected' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_before_selected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_after_selected' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_after_selected

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_full_profile' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_full_profile

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_mono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalBlockInWindow_mono

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCapInterval_block_bounds' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalCapInterval_block_bounds

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindowCapIntervalEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindowCapIntervalEquiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_cap_interval_equiv' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_cap_interval_equiv

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_full_profile_blocks' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_full_profile_blocks

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_top' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_shift' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_shift

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_row_offset'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_row_offset

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_cap_response' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_cap_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_cap_response' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_cap_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_true_left_eq_local' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_true_left_eq_local

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_true_right_eq_local' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_true_right_eq_local

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_true_left_response' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_true_left_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_true_right_response' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_true_right_response

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_common_true_caps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_common_true_caps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_common_closure_true_caps' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_common_closure_true_caps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_true_cap_product' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_true_cap_product

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_cap_normalized_ratio' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_cap_normalized_ratio

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_monic_dependence' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_monic_dependence

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_residue_dependence' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_residue_dependence

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_active_classes' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_active_classes

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_single_completed_gaps' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_single_completed_gaps

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_end_classes_balanced' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_end_classes_balanced

/-- info: 'SkewCornerDescent.signedRationalFactors_change_coordinate' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.signedRationalFactors_change_coordinate

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_rational_factorization' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_rational_factorization

/-- info: 'SkewCornerDescent.planeClass_root_exponent' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.planeClass_root_exponent

/-- info: 'SkewCornerDescent.Matrix.actualResidue_root_class_exponent' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.actualResidue_root_class_exponent

/-- info: 'SkewCornerDescent.transcendental_rational_representation_unique' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.transcendental_rational_representation_unique

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_row_fibers' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_row_fibers

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_zeta' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_zeta

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_xi' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_xi

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_core_xi' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_core_xi

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_row_offset' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_row_offset

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_row_fibers' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_row_fibers

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_endpoints' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_endpoints

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_core_zeta' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_core_zeta

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_prefix_bound' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_prefix_bound

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_suffix_bound' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_suffix_bound

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_core_negative' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_core_negative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_core_negative' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_core_negative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_core_zero' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_core_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_core_zero' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_core_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_row_alignment' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_row_alignment

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_corner_matrix' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_lower_corner_matrix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_corner_matrix' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalLiteralWindow_upper_corner_matrix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_row_alignment' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_row_alignment

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_prefix_xi_suffix_zeta' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_prefix_xi_suffix_zeta

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_suffix_xi_prefix_zeta' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_suffix_xi_prefix_zeta

end SkewCornerDescent
