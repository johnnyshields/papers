import SkewCornerDescent.Matrix.OriginalSignedFactors

/-!
# Original determinant cancellation and sign guards

Pins the axiom footprints of full removed-factor cancellation and original determinant signs.
-/

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalComplementary_det_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalComplementary_det_inventory

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_cross_cofactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_cross_cofactor

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_pair_power' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_pair_power

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_local_signed_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_local_signed_factorization

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_signed_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_signed_factorization

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_pair_normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_residue_pair_normalization
