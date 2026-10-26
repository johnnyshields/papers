/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResiduePlaneClassification
import SkewCornerDescent.PrimeProductDivisor

/-!
# Rational plane factors in an actual residue response product

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). A cleared irreducible rational plane
factor dividing a product of actual triangular response representatives has degree one.
Its response factor and rational label are produced, rather than assumed.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance planeProductRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- A cleared rational plane factor in a response product is linear and identifies a
complete actual response with the closure-top rational-label correction. -/
theorem actualResidue_plane_product_factor (N : ℕ+) {ι : Type*} (s : Finset ι)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    {K : ResidueHigherIndex N} {p : Polynomial ℚ} (hp : p.Monic)
    (hirr : Irreducible p) {A F : ResidueHigherPolynomial N}
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (hF0 : residueHigherEval N F ≠ 0)
    (hd : triangularPlanePolynomial K (p.map (algebraMap ℚ (residueLowerField N N))) A F ∣
      ∏ i ∈ s, (X (J i) + B i)) :
    p.natDegree = 1 ∧ ∃ i ∈ s, J i = K ∧ ∃ c : ℚ, p.IsRoot c ∧
      residueHigherEval N (B i) = residueHigherEval N A -
        (c : OtherField N) * residueHigherEval N F := by
  have hdeg : 0 < (p.map (algebraMap ℚ (residueLowerField N N))).natDegree := by
    rw [Polynomial.natDegree_map]
    exact hp.natDegree_pos_of_not_isUnit hirr.not_isUnit
  obtain ⟨hq0, hqu⟩ := triangularPlanePolynomial_nonunit (hp.map _) hdeg hA hF
  obtain ⟨i, hi, hdi⟩ := primeProduct_divisor_contains_factor s
    (fun i => X (J i) + B i) (fun i hi => monicTriangularPolynomial_prime (hB i hi))
    hq0 hqu hd
  obtain ⟨htop, hlinear, c, hc, he⟩ := actualResidue_plane_divisor_classification N
    hp hirr hA hF (hB i hi) hF0 hdi
  exact ⟨hlinear, i, hi, htop, c, hc, he⟩

end SkewCornerDescent.Matrix
