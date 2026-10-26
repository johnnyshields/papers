/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinCompositionCells
import SkewClassInflation.ThinFactorReversal
import SkewClassInflation.ThinMarkBoundary
import SkewClassInflation.ThinOrientationMultisets
import SkewClassInflation.ThinWeightReadings
import SkewClassInflation.UnboundedSplitting

/-!
# Exact ThinFamilies axiom footprints

Every expected message is the observed kernel footprint of the declaration it guards.
-/

/-- info: 'SkewClassInflation.BoundaryParameters.bit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.bit_le

/-- info: 'SkewClassInflation.BoundaryParameters.upper_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.upper_strictAnti

/-- info: 'SkewClassInflation.BoundaryParameters.lower_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.lower_strictAnti

/-- info: 'SkewClassInflation.BoundaryParameters.lower_lt_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.lower_lt_upper

/-- info: 'SkewClassInflation.BoundaryParameters.core_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_connected

/-- info: 'SkewClassInflation.BoundaryParameters.core_last_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_last_col

/-- info: 'SkewClassInflation.BoundaryParameters.residue_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.residue_ne

/-- info: 'SkewClassInflation.BoundaryParameters.residue_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.residue_separation

/-- info: 'SkewClassInflation.BoundaryParameters.core_row_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_row_residue

/-- info: 'SkewClassInflation.BoundaryParameters.core_col_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_col_residue

/-- info: 'SkewClassInflation.BoundaryParameters.core_zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_zeroFree

/-- info: 'SkewClassInflation.BoundaryParameters.core_hessenberg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_hessenberg

/-- info: 'SkewClassInflation.BoundaryParameters.core_rows_eq_of_schur_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_rows_eq_of_schur_eq

/-- info: 'SkewClassInflation.BoundaryParameters.core_suffix_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_suffix_mem_iff

/-- info: 'SkewClassInflation.BoundaryParameters.core_suffix_set_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_suffix_set_injective

/-- info: 'SkewClassInflation.BoundaryParameters.core_support_iff_mem_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_support_iff_mem_suffix

/-- info: 'SkewClassInflation.BoundaryParameters.core_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_rowSet

/-- info: 'SkewClassInflation.BoundaryParameters.core_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_colSet

/-- info: 'SkewClassInflation.BoundaryParameters.upper_lt_suffix_grid_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.upper_lt_suffix_grid_iff

/-- info: 'SkewClassInflation.BoundaryParameters.lower_lt_suffix_grid_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.lower_lt_suffix_grid_iff

/-- info: 'SkewClassInflation.BoundaryParameters.core_row_crossing_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_row_crossing_count

/-- info: 'SkewClassInflation.BoundaryParameters.core_col_crossing_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.core_col_crossing_count

/-- info: 'SkewClassInflation.BoundaryParameters.restoredParent_deletionSign_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.restoredParent_deletionSign_one

/-- info: 'SkewClassInflation.BoundaryParameters.restoredParent_lowest_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.restoredParent_lowest_component

/-- info: 'SkewClassInflation.BoundaryParameters.restoredParent_component_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.restoredParent_component_below

/-- info: 'SkewClassInflation.ThinParameters.boundary_function_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_function_injective

/-- info: 'SkewClassInflation.ThinParameters.superthreshold_function_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.superthreshold_function_injective

/-- info: 'SkewClassInflation.ThinParameters.superthreshold_functions_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.superthreshold_functions_ne

/-- info: 'SkewClassInflation.ThinParameters.boundary_lowest_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_lowest_component

/-- info: 'SkewClassInflation.ThinParameters.boundary_component_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_component_below

/-- info: 'SkewClassInflation.ThinParameters.boundary_least_ordinary_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_least_ordinary_degree

/-- info: 'SkewClassInflation.ThinParameters.boundary_core_lowest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_core_lowest

/-- info: 'SkewClassInflation.ThinParameters.boundary_core_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_core_rows

/-- info: 'SkewClassInflation.ThinParameters.boundary_core_cols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_core_cols

/-- info: 'SkewClassInflation.ThinParameters.boundary_schur_eq_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_schur_eq_restored

/-- info: 'SkewClassInflation.BoundaryParameters.restoredParent_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.restoredParent_rowSet

/-- info: 'SkewClassInflation.BoundaryParameters.restoredParent_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.restoredParent_colSet

/-- info: 'SkewClassInflation.BoundaryParameters.commonBetas_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.commonBetas_card

/-- info: 'SkewClassInflation.ThinParameters.boundary_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_rowSet

/-- info: 'SkewClassInflation.ThinParameters.boundary_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_colSet

/-- info: 'SkewClassInflation.BoundaryParameters.q_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.q_pos

/-- info: 'SkewClassInflation.BoundaryParameters.grid_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.grid_eq_iff

/-- info: 'SkewClassInflation.BoundaryParameters.suffix_grid_not_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.suffix_grid_not_upper

/-- info: 'SkewClassInflation.BoundaryParameters.suffix_grid_not_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.suffix_grid_not_lower

/-- info: 'SkewClassInflation.BoundaryParameters.commonBetas_available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.commonBetas_available

/-- info: 'SkewClassInflation.BoundaryParameters.restoredParent_connected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.restoredParent_connected

/-- info: 'SkewClassInflation.BoundaryParameters.restoredParent_lowest_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.BoundaryParameters.restoredParent_lowest_nonzero

/-- info: 'SkewClassInflation.compositionCore_schur_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.compositionCore_schur_injective

/-- info: 'SkewClassInflation.ThinParameters.grid_negative_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.grid_negative_depth

/-- info: 'SkewClassInflation.ThinParameters.diagram_negative_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_negative_depth

/-- info: 'SkewClassInflation.ThinParameters.diagram_noOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_noOpening

/-- info: 'SkewClassInflation.ThinParameters.subthreshold_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.subthreshold_full_class

/-- info: 'SkewClassInflation.ThinParameters.superthreshold_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.superthreshold_full_class

/-- info: 'SkewClassInflation.ThinParameters.inflated_diagram_ne_rotated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflated_diagram_ne_rotated

/-- info: 'SkewClassInflation.ThinParameters.superthreshold_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.superthreshold_class_card

/-- info: 'SkewClassInflation.ThinParameters.chain_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_span

/-- info: 'SkewClassInflation.ThinParameters.chain_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_rowSet

/-- info: 'SkewClassInflation.ThinParameters.chain_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_colSet

/-- info: 'SkewClassInflation.ThinParameters.diagram_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_span

/-- info: 'SkewClassInflation.ThinParameters.diagram_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_rowSet

/-- info: 'SkewClassInflation.ThinParameters.diagram_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_colSet

/-- info: 'SkewClassInflation.ThinParameters.powerFunctions_are_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.powerFunctions_are_actual

/-- info: 'SkewClassInflation.ThinParameters.connected_factor_of_power_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.connected_factor_of_power_product

/-- info: 'SkewClassInflation.ThinParameters.first_gap_positive_of_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.first_gap_positive_of_product

/-- info: 'SkewClassInflation.ThinParameters.rotated_source_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.rotated_source_constant

/-- info: 'SkewClassInflation.ThinParameters.last_gap_positive_of_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.last_gap_positive_of_product

/-- info: 'SkewClassInflation.ThinParameters.grid_excludes_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.grid_excludes_multiple

/-- info: 'SkewClassInflation.ThinParameters.erase_grid_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.erase_grid_boundary

/-- info: 'SkewClassInflation.ThinParameters.merge_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.merge_chain

/-- info: 'SkewClassInflation.ThinParameters.powerFunctions_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.powerFunctions_cons

/-- info: 'SkewClassInflation.ThinParameters.innerPower_unit_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_unit_constant

/-- info: 'SkewClassInflation.ThinParameters.chain_constant_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_constant_coefficient

/-- info: 'SkewClassInflation.ThinParameters.diagram_constant_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_constant_coefficient

/-- info: 'SkewClassInflation.ThinParameters.blockInventory_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.blockInventory_connected

/-- info: 'SkewClassInflation.ThinParameters.blockInventory_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.blockInventory_product

/-- info: 'SkewClassInflation.ThinParameters.arbitrary_mate_component_matching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.arbitrary_mate_component_matching

/-- info: 'SkewClassInflation.ThinParameters.chain_compose_eq_inflation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_compose_eq_inflation

/-- info: 'SkewClassInflation.ThinParameters.ribbonRows_compose_eq_inflation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.ribbonRows_compose_eq_inflation

/-- info: 'SkewClassInflation.ThinParameters.diagram_compose_eq_inflation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_compose_eq_inflation

/-- info: 'SkewClassInflation.ThinParameters.subthreshold_literal_chart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.subthreshold_literal_chart

/-- info: 'SkewClassInflation.ThinParameters.chain_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_row_count

/-- info: 'SkewClassInflation.ThinParameters.chain_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_thick

/-- info: 'SkewClassInflation.ThinParameters.diagram_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_row_count

/-- info: 'SkewClassInflation.ThinParameters.diagram_thick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_thick

/-- info: 'SkewClassInflation.ThinParameters.diagram_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_single

/-- info: 'SkewClassInflation.ThinParameters.factor_reversal_mate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.factor_reversal_mate

/-- info: 'SkewClassInflation.ThinParameters.factor_reversal_subthreshold_mate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.factor_reversal_subthreshold_mate

/-- info: 'SkewClassInflation.ThinParameters.factor_reversal_rotated_subthreshold_mate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.factor_reversal_rotated_subthreshold_mate

/-- info: 'SkewClassInflation.ThinParameters.thin_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.thin_full_class

/-- info: 'SkewClassInflation.ThinParameters.thin_orientations_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.thin_orientations_disjoint

/-- info: 'SkewClassInflation.ThinParameters.rotated_diagram_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.rotated_diagram_injective

/-- info: 'SkewClassInflation.ThinParameters.thin_full_class_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.thin_full_class_finite

/-- info: 'SkewClassInflation.ThinParameters.thin_full_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.thin_full_class_card

/-- info: 'SkewClassInflation.ThinParameters.inflation_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflation_full_class

/-- info: 'SkewClassInflation.ThinParameters.inflation_full_class_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflation_full_class_card

/-- info: 'SkewClassInflation.ThinParameters.lower_attachmentCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.lower_attachmentCells

/-- info: 'SkewClassInflation.ThinParameters.upper_attachmentCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.upper_attachmentCells

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_hypothesisV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_hypothesisV

/-- info: 'SkewClassInflation.ThinParameters.lowerMark_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.lowerMark_span

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_width

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_period

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_subsets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_subsets

/-- info: 'SkewClassInflation.ThinParameters.lowerMark_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.lowerMark_connected

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_narrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_narrow

/-- info: 'SkewClassInflation.ThinParameters.mem_inflation_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.mem_inflation_middle

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_lowerH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_lowerH

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_upperH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_upperH

/-- info: 'SkewClassInflation.ThinParameters.upper_mark_removal_not_skew' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.upper_mark_removal_not_skew

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_legal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_legal_iff

/-- info: 'SkewClassInflation.ThinParameters.mem_inflationPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.mem_inflationPeriodic

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_hatMark_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_hatMark_empty

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_noHatAdjacency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_noHatAdjacency

/-- info: 'SkewClassInflation.ThinParameters.innerCells_extremes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerCells_extremes

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_nonempty

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_empty

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_wellformed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_wellformed

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_legal

/-- info: 'SkewClassInflation.ThinParameters.inner_cell_on_lower_mark_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inner_cell_on_lower_mark_content

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_maximal

/-- info: 'SkewClassInflation.ThinParameters.lower_mark_removal_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.lower_mark_removal_cells

/-- info: 'SkewClassInflation.ThinParameters.upper_mark_removal_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.upper_mark_removal_cells

/-- info: 'SkewClassInflation.ThinParameters.inflationMark_removals_connected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.inflationMark_removals_connected

/-- info: 'SkewClassInflation.ThinParameters.mem_innerCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.mem_innerCells

/-- info: 'SkewClassInflation.ThinParameters.mem_lowerMark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.mem_lowerMark

/-- info: 'SkewClassInflation.ThinParameters.mem_upperMark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.mem_upperMark

/-- info: 'SkewClassInflation.ThinParameters.innerCells_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerCells_connected

/-- info: 'SkewClassInflation.ThinParameters.arbitrary_mate_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.arbitrary_mate_constant

/-- info: 'SkewClassInflation.ThinParameters.arbitrary_mate_total_contraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.arbitrary_mate_total_contraction

/-- info: 'SkewClassInflation.ThinParameters.arbitrary_mate_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.arbitrary_mate_exterior

/-- info: 'SkewClassInflation.ThinParameters.arbitrary_mate_oriented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.arbitrary_mate_oriented

/-- info: 'SkewClassInflation.ThinParameters.chain_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_first

/-- info: 'SkewClassInflation.ThinParameters.chain_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_last

/-- info: 'SkewClassInflation.ThinParameters.diagram_exteriors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_exteriors

/-- info: 'SkewClassInflation.ThinParameters.arbitrary_mate_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.arbitrary_mate_geometry

/-- info: 'SkewClassInflation.ThinParameters.diagram_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_injective

/-- info: 'SkewClassInflation.ThinParameters.diagram_ne_rotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_ne_rotated

/-- info: 'SkewClassInflation.ThinParameters.right_power_of_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.right_power_of_merge

/-- info: 'SkewClassInflation.ThinParameters.innerPower_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_word

/-- info: 'SkewClassInflation.ThinParameters.innerPower_rowMultiset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_rowMultiset

/-- info: 'SkewClassInflation.ThinParameters.innerPower_orientation_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_orientation_residual

/-- info: 'SkewClassInflation.ThinParameters.arbitrary_mate_orientation_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.arbitrary_mate_orientation_residual

/-- info: 'SkewClassInflation.ThinParameters.oriented_profile_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.oriented_profile_reconstruction

/-- info: 'SkewClassInflation.ThinParameters.boundary_q_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.boundary_q_eq

/-- info: 'SkewClassInflation.ThinParameters.power_coordinates_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.power_coordinates_rows

/-- info: 'SkewClassInflation.ThinParameters.power_coordinates_gaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.power_coordinates_gaps

/-- info: 'SkewClassInflation.ThinParameters.innerPower_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_beta

/-- info: 'SkewClassInflation.ThinParameters.innerPower_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_span

/-- info: 'SkewClassInflation.ThinParameters.innerPower_rowSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_rowSet

/-- info: 'SkewClassInflation.ThinParameters.innerPower_colSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_colSet

/-- info: 'SkewClassInflation.ThinParameters.innerPower_shortest_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_shortest_coefficient

/-- info: 'SkewClassInflation.ThinParameters.innerPower_mate_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_mate_data

/-- info: 'SkewClassInflation.ThinParameters.innerPower_first_mate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_first_mate_eq

/-- info: 'SkewClassInflation.ThinParameters.innerPower_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_rigidity

/-- info: 'SkewClassInflation.ThinParameters.innerPower_full_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_full_class

/-- info: 'SkewClassInflation.ThinParameters.projection_power_first_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.projection_power_first_row

/-- info: 'SkewClassInflation.ThinParameters.projection_power_minor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.projection_power_minor

/-- info: 'SkewClassInflation.ThinParameters.projection_innerPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.projection_innerPower

/-- info: 'SkewClassInflation.ThinParameters.power_substitution_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.power_substitution_injective

/-- info: 'SkewClassInflation.ThinParameters.innerPower_thick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_thick

/-- info: 'SkewClassInflation.ThinParameters.innerPower_shortest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_shortest

/-- info: 'SkewClassInflation.ThinParameters.innerPower_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_gap

/-- info: 'SkewClassInflation.ThinParameters.innerPower_tail_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_tail_connected

/-- info: 'SkewClassInflation.ThinParameters.chain_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_blocks

/-- info: 'SkewClassInflation.ThinParameters.diagram_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_prepend

/-- info: 'SkewClassInflation.ThinParameters.projection_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.projection_residue

/-- info: 'SkewClassInflation.ThinParameters.projection_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.projection_multiple

/-- info: 'SkewClassInflation.ThinParameters.innerPower_zeroSeamCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.innerPower_zeroSeamCount

/-- info: 'SkewClassInflation.ThinParameters.chain_zeroSeamCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_zeroSeamCount

/-- info: 'SkewClassInflation.ThinParameters.diagram_zeroSeamCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_zeroSeamCount

/-- info: 'SkewClassInflation.ThinParameters.remainder_of_merged_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.remainder_of_merged_function

/-- info: 'SkewClassInflation.ThinParameters.chain_schur_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_schur_cons

/-- info: 'SkewClassInflation.ThinParameters.powerSubstitution_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.powerSubstitution_complete

/-- info: 'SkewClassInflation.ThinParameters.chain_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_substitution

/-- info: 'SkewClassInflation.ThinParameters.diagram_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_substitution

/-- info: 'SkewClassInflation.ThinParameters.diagram_schur_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_schur_eq_iff

/-- info: 'SkewClassInflation.ThinParameters.mem_row_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.mem_row_compose

/-- info: 'SkewClassInflation.ThinParameters.row_compose_eq_innerPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.row_compose_eq_innerPower

/-- info: 'SkewClassInflation.ThinParameters.original_residues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.original_residues

/-- info: 'SkewClassInflation.ThinParameters.diagram_residual_sets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_residual_sets

/-- info: 'SkewClassInflation.ThinParameters.diagram_total_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_total_contraction

/-- info: 'SkewClassInflation.ThinParameters.chain_gap_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_gap_sum

/-- info: 'SkewClassInflation.ThinParameters.diagram_gap_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_gap_sum

/-- info: 'SkewClassInflation.ThinParameters.diagram_row_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_row_weight

/-- info: 'SkewClassInflation.ThinParameters.chain_gap_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.chain_gap_monomial

/-- info: 'SkewClassInflation.ThinParameters.diagram_cofactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_cofactor

/-- info: 'SkewClassInflation.ThinParameters.diagram_corner_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_corner_coefficient

/-- info: 'SkewClassInflation.ThinParameters.diagram_largest_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_largest_label

/-- info: 'SkewClassInflation.ThinParameters.diagram_maximal_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.diagram_maximal_derivative

/-- info: 'SkewClassInflation.ThinParameters.all_mates_superthreshold_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewClassInflation.ThinParameters.all_mates_superthreshold_class

