import SkewCornerDescent.Matrix.ResiduePlaneClassification
import SkewCornerDescent.Matrix.ResiduePlaneProduct
import SkewCornerDescent.Matrix.ResiduePlaneIrreducibility
import SkewCornerDescent.Matrix.ActualResiduePlanePrimes

/-! Axiom footprints for original-coordinate rational plane factors and response classes. -/

/-- info: 'SkewCornerDescent.clearedPlanePolynomial_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.clearedPlanePolynomial_map

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_vars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_vars

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_split

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_split_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_split_monic

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_divisor_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_divisor_top

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_eval

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_divisor_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_divisor_root

/-- info: 'SkewCornerDescent.Matrix.residue_plane_cleared_linear_divisor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residue_plane_cleared_linear_divisor

/-- info: 'SkewCornerDescent.Matrix.residueHigherEval_mem_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueHigherEval_mem_lower

/-- info: 'SkewCornerDescent.Matrix.actualResidue_plane_divisor_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_plane_divisor_classification

/-- info: 'SkewCornerDescent.triangularCorrection_split_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularCorrection_split_constant

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_degreeOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_degreeOf

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_nonunit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_nonunit

/-- info: 'SkewCornerDescent.primeProduct_divisor_contains_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.primeProduct_divisor_contains_factor

/-- info: 'SkewCornerDescent.Matrix.actualResidue_plane_product_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_plane_product_factor

/-- info: 'SkewCornerDescent.monic_divisor_descends_of_algebraic_constants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.monic_divisor_descends_of_algebraic_constants

/-- info: 'SkewCornerDescent.irreducible_map_of_algebraic_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.irreducible_map_of_algebraic_constants

/-- info: 'SkewCornerDescent.irreducible_map_rational_generators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.irreducible_map_rational_generators

/-- info: 'SkewCornerDescent.Matrix.residueLowerField_algebraic_constants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueLowerField_algebraic_constants

/-- info: 'SkewCornerDescent.Matrix.residueLowerField_irreducible_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueLowerField_irreducible_map

/-- info: 'SkewCornerDescent.clearedPlanePolynomial_comp_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.clearedPlanePolynomial_comp_affine

/-- info: 'SkewCornerDescent.clearedPlanePolynomial_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.clearedPlanePolynomial_irreducible

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_irreducible

/-- info: 'SkewCornerDescent.Matrix.residueField_mem_adjoin_generators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueField_mem_adjoin_generators

/-- info: 'SkewCornerDescent.Matrix.residueField_algebraic_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueField_algebraic_constants

/-- info: 'SkewCornerDescent.Matrix.residueField_irreducible_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueField_irreducible_map

/-- info: 'SkewCornerDescent.Matrix.residueField_clearedPlane_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.residueField_clearedPlane_irreducible

/-- info: 'SkewCornerDescent.Matrix.actualResidue_plane_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_plane_irreducible

/-- info: 'SkewCornerDescent.Matrix.actualResidue_plane_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_plane_prime
