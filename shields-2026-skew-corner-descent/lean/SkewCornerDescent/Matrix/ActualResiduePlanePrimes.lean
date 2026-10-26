/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualResiduePrimes
import SkewCornerDescent.Matrix.ResidueFieldConstants
import SkewCornerDescent.TriangularPlaneIrreducibility

/-!
# Prime rational plane pullbacks in the actual residue polynomial algebra

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Every irreducible monic rational plane
factor has an irreducible denominator-cleared numerator in the original surviving
coordinates. Its image is prime in the actual polynomial algebra, not in the fraction field.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance actualPlanePrimeRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- The original-coordinate cleared numerator is irreducible with no factorization input. -/
theorem actualResidue_plane_irreducible (N : ℕ+) {K : ResidueHigherIndex N}
    {p : Polynomial ℚ} (hp : p.Monic) (hirr : Irreducible p)
    {A F : ResidueHigherPolynomial N} (hA : ∀ i ∈ A.vars, i < K)
    (hF : ∀ i ∈ F.vars, i < K) (hF0 : residueHigherEval N F ≠ 0) :
    Irreducible (triangularPlanePolynomial K
      (p.map (algebraMap ℚ (residueLowerField N N))) A F) := by
  apply triangularPlanePolynomial_irreducible (residueHigherEval N) (hp.map _) _ hA hF hF0
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ
    (residueLowerField N N) (OtherField N)]
  exact residueField_irreducible_map N hp hirr

/-- The cleared plane factor is prime in the actual residue polynomial algebra. -/
theorem actualResidue_plane_prime (N : ℕ+) {K : ResidueHigherIndex N}
    {p : Polynomial ℚ} (hp : p.Monic) (hirr : Irreducible p)
    {A F : ResidueHigherPolynomial N} (hA : ∀ i ∈ A.vars, i < K)
    (hF : ∀ i ∈ F.vars, i < K) (hF0 : residueHigherEval N F ≠ 0) :
    Prime (actualResiduePolynomialEquiv N (triangularPlanePolynomial K
      (p.map (algebraMap ℚ (residueLowerField N N))) A F)) :=
  (MulEquiv.prime_iff (actualResiduePolynomialEquiv N)).mpr
    (actualResidue_plane_irreducible N hp hirr hA hF hF0).prime

end SkewCornerDescent.Matrix
