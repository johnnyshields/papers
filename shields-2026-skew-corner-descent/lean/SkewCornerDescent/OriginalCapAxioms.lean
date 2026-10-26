import SkewCornerDescent.Matrix.OriginalCapNormalization

/-!
# Actual true-cap normalization guards

Pins actual exterior-product extraction, polynomial internal families and signed normalization.
-/

/-- info: 'SkewCornerDescent.Matrix.prod_two_caps_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.prod_two_caps_internal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_cap_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_cap_product

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_polynomial_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_polynomial_family

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalTrueCapProduct_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalTrueCapProduct_ne_zero

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_cap_normalized_ratio' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_cap_normalized_ratio
