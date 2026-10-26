/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordCounterexample

/-!
# Axiom guards for the complete original square-word example

Guards `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The expected footprints are produced by the elaborated declarations.
-/

/-- info: 'SkewCornerDescent.SquareWordProfiles.source_literal_copies'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.source_literal_copies

/-- info: 'SkewCornerDescent.SquareWordProfiles.source_full_windows'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.source_full_windows

/-- info: 'SkewCornerDescent.SquareWordProfiles.source_corner_power'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.source_corner_power

/-- info: 'SkewCornerDescent.SquareWordProfiles.window_corner_power'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.window_corner_power

/-- info: 'SkewCornerDescent.SquareWordProfiles.source_residue_determinant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.source_residue_determinant

/-- info: 'SkewCornerDescent.SquareWordProfiles.window_residue_determinant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.window_residue_determinant

/-- info: 'SkewCornerDescent.SquareWordProfiles.amalgamation_residue_determinant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.amalgamation_residue_determinant

/-- info: 'SkewCornerDescent.SquareWordProfiles.closure_residue_determinant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.closure_residue_determinant

/-- info: 'SkewCornerDescent.SquareWordProfiles.square_word_actual_closure_coordinate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.square_word_actual_closure_coordinate

/-- info: 'SkewCornerDescent.SquareWordProfiles.square_word_original_residue_matching'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.square_word_original_residue_matching

/-- info: 'SkewCornerDescent.SquareWordProfiles.square_word_window_residue_matching'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.square_word_window_residue_matching

/-- info: 'SkewCornerDescent.SquareWordProfiles.coordinate_chart_pderiv_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.coordinate_chart_pderiv_one

/-- info: 'SkewCornerDescent.SquareWordProfiles.coordinate_normal_coeff_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.coordinate_normal_coeff_one

/-- info: 'SkewCornerDescent.SquareWordProfiles.coordinate_residue_pderiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.coordinate_residue_pderiv

/-- info: 'SkewCornerDescent.SquareWordProfiles.coordinate_source_closure_units'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.coordinate_source_closure_units

/-- info: 'SkewCornerDescent.SquareWordProfiles.sourceMatrix_frame_det'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.sourceMatrix_frame_det

/-- info: 'SkewCornerDescent.SquareWordProfiles.removedMatrix_inverse'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.removedMatrix_inverse

/-- info: 'SkewCornerDescent.SquareWordProfiles.sourceScalarMatrix_diagonal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.sourceScalarMatrix_diagonal

/-- info: 'SkewCornerDescent.SquareWordProfiles.sourceScalarMatrix_subdiagonal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.sourceScalarMatrix_subdiagonal

/-- info: 'SkewCornerDescent.SquareWordProfiles.sourceInternalResponse_actual_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.sourceInternalResponse_actual_word

/-- info: 'SkewCornerDescent.SquareWordProfiles.windowInternalResponse_actual_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.windowInternalResponse_actual_word

/-- info: 'SkewCornerDescent.SquareWordProfiles.sourceClassExponent_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.sourceClassExponent_eq

/-- info: 'SkewCornerDescent.SquareWordProfiles.actualSecondDetector_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.actualSecondDetector_eq

/-- info: 'SkewCornerDescent.SquareWordProfiles.actualSecondDetector_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.actualSecondDetector_ne_zero

/-- info: 'SkewCornerDescent.SquareWordProfiles.marked_isLegal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.marked_isLegal

/-- info: 'SkewCornerDescent.SquareWordProfiles.marked_vertical_edges'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.marked_vertical_edges

/-- info: 'SkewCornerDescent.SquareWordProfiles.marked_complete_window_match'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.marked_complete_window_match

/-- info: 'SkewCornerDescent.SquareWordProfiles.marked_amalgamation_profile'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.marked_amalgamation_profile

/-- info: 'SkewCornerDescent.SquareWordProfiles.source_actual_horizontal_closure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.source_actual_horizontal_closure

/-- info: 'SkewCornerDescent.SquareWordProfiles.square_original_cofactor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.square_original_cofactor

/-- info: 'SkewCornerDescent.SquareWordProfiles.square_selected_interior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.square_selected_interior

/-- info: 'SkewCornerDescent.SquareWordProfiles.four_cell_connected_span_three_square'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.four_cell_connected_span_three_square

/-- info: 'SkewCornerDescent.SquareWordProfiles.source_no_actual_five_copy_line_root'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.source_no_actual_five_copy_line_root

/-- info: 'SkewCornerDescent.SquareWordProfiles.defect_coeff_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.defect_coeff_zero

/-- info: 'SkewCornerDescent.SquareWordProfiles.defect_original_first_mixed_coeff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.defect_original_first_mixed_coeff

/-- info: 'SkewCornerDescent.SquareWordProfiles.defect_coeff_one_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.defect_coeff_one_ne_zero

/-- info: 'SkewCornerDescent.SquareWordProfiles.defect_order_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.defect_order_one

/-- info: 'SkewCornerDescent.SquareWordProfiles.square_word_counterexample'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.SquareWordProfiles.square_word_counterexample

