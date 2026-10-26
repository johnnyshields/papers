/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRowPencil

/-!
# Axiom guards for complete actual all-row plane labels

Guards actual unit inverse pivots, full projected vertex counts, integer
mixed-jet origins and the complete source row-plane label statement supporting
`shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
-/

/-- info: 'SkewCornerDescent.Matrix.row_block_inverse_unit_diagonal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.row_block_inverse_unit_diagonal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_row_projection_count'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_interval_row_projection_count

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_row_response_hessian_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_row_response_hessian_bound

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_row_hessian_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_row_hessian_bound

/-- info: 'SkewCornerDescent.Matrix.residue_affine_label_of_integer_mixed_jets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.residue_affine_label_of_integer_mixed_jets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_row_plane_integer_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_row_plane_integer_origin

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_row_plane_labels'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_row_plane_labels
