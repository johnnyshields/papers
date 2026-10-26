import SkewCornerDescent.Matrix.OriginalDefectFactors

/-!
# Literal closure and full defect-factor guards

Pins original corner inventories and removed determinant cancellation before normal substitution.
-/

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_corner_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_corner_inventory

/-- info: 'SkewCornerDescent.Matrix.originalHorizontalClosure_profile_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalHorizontalClosure_profile_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_removed_square

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_multiplicative_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_multiplicative_cancel

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_defect_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_defect_cancel

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_actual_defect_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_actual_defect_cancel
