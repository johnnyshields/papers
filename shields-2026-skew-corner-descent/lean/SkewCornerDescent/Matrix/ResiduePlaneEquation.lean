/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResiduePlaneFactorization

/-!
# Clearing the exact rational residue equation

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `eq:residue-match`, `lem:residue-classifier`). The equality in the
unchanged residue field is transported through its injective polynomial presentation.
No cleared-polynomial equality or nonvanishing plane denominator is assumed.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance residuePlaneEquationRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Exact evaluation of a rational numerator after cap denominator clearing. -/
theorem actualResidue_plane_eval (N : ℕ+) (K : ResidueHigherIndex N)
    (p : Polynomial ℚ) (A F : ResidueHigherPolynomial N)
    (hF0 : residueHigherEval N F ≠ 0) :
    residueHigherEval N (triangularPlanePolynomial K
      (p.map (algebraMap ℚ (residueLowerField N N))) A F) =
      (residueHigherEval N F) ^ p.natDegree * Polynomial.aeval
        ((residueHigherEval N (X K) + residueHigherEval N A) / residueHigherEval N F) p := by
  rw [triangularPlanePolynomial_eval_all, clearedPlanePolynomial_eval _ _ _ _ hF0,
    Polynomial.natDegree_map]
  congr 1
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    ← IsScalarTower.algebraMap_eq ℚ (residueLowerField N N) (OtherField N)]
  rfl

/-- Every finite product of actual triangular responses is nonzero at residue. -/
theorem actualResidue_response_product_ne_zero (N : ℕ+) {ι : Type*} (s : Finset ι)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i) :
    residueHigherEval N (∏ i ∈ s, (X (J i) + B i)) ≠ 0 := by
  have hp : (∏ i ∈ s, (X (J i) + B i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (monicTriangularPolynomial_prime (hB i hi)).ne_zero
  intro he
  apply hp
  apply residueHigherEval_injective N
  simpa only [map_zero] using he

/-- Exact dependence produces the entire cleared polynomial identity.
The cap exponent and every response multiplicity are retained. -/
theorem actualResidue_clear_equation (N : ℕ+) {K : ResidueHigherIndex N}
    (A F U W c : ResidueHigherPolynomial N) (p q : Polynomial ℚ) (v b d : ℕ)
    (hF0 : residueHigherEval N F ≠ 0) (hU0 : residueHigherEval N U ≠ 0)
    (hW0 : residueHigherEval N W ≠ 0) (hc : IsUnit c)
    (hdep : residueHigherEval N c * (residueHigherEval N U) ^ v /
        ((residueHigherEval N W) ^ b * (residueHigherEval N F) ^ d) =
      Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
          residueHigherEval N F) p /
        Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
          residueHigherEval N F) q) :
    triangularPlanePolynomial K (p.map (algebraMap ℚ (residueLowerField N N))) A F *
        (W ^ b * F ^ (q.natDegree + d)) =
      c * triangularPlanePolynomial K (q.map (algebraMap ℚ (residueLowerField N N))) A F *
        (U ^ v * F ^ p.natDegree) := by
  have hl0 : residueHigherEval N c * (residueHigherEval N U) ^ v /
      ((residueHigherEval N W) ^ b * (residueHigherEval N F) ^ d) ≠ 0 :=
    div_ne_zero (mul_ne_zero (hc.map (residueHigherEval N)).ne_zero (pow_ne_zero _ hU0))
      (mul_ne_zero (pow_ne_zero _ hW0) (pow_ne_zero _ hF0))
  have hq0 : Polynomial.aeval
      ((residueHigherEval N (X K) + residueHigherEval N A) / residueHigherEval N F) q ≠ 0 := by
    intro hq
    rw [hq, div_zero] at hdep
    exact hl0 hdep
  have he := (div_eq_div_iff
    (mul_ne_zero (pow_ne_zero _ hW0) (pow_ne_zero _ hF0)) hq0).mp hdep
  apply residueHigherEval_injective N
  simp only [map_mul, map_pow, actualResidue_plane_eval N K _ A F hF0]
  rw [pow_add]
  linear_combination -((residueHigherEval N F) ^ p.natDegree *
    (residueHigherEval N F) ^ q.natDegree) * he

/-- Exact rational dependence forces both numerator and denominator to split over `ℚ`.
Response nonvanishing and the cleared identity are produced inside the proof. -/
theorem actualResidue_dependence_splits (N : ℕ+) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (L : κ → ResidueHigherIndex N) (D : κ → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K : ResidueHigherIndex N} (A F c : ResidueHigherPolynomial N)
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (hF0 : residueHigherEval N F ≠ 0) (hc : IsUnit c)
    (p q : Polynomial ℚ) (hpq : IsCoprime p q) (v b d : ℕ)
    (hdep : residueHigherEval N c *
        (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
        ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
          (residueHigherEval N F) ^ d) =
      Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
          residueHigherEval N F) p /
        Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
          residueHigherEval N F) q) :
    p.Splits ∧ q.Splits := by
  let U := ∏ i ∈ s, (X (J i) + B i)
  let W := ∏ i ∈ t, (X (L i) + D i)
  have hclear := actualResidue_clear_equation N A F U W c p q v b d hF0
    (actualResidue_response_product_ne_zero N s J B hB)
    (actualResidue_response_product_ne_zero N t L D hD) hc hdep
  constructor
  · exact actualResidue_cross_splits N s J B hB hA hF hF0 hc hpq v p.natDegree hclear
  · apply actualResidue_cross_splits N t L D hD hA hF hF0 isUnit_one hpq.symm b
      (q.natDegree + d) (H := c * (U ^ v * F ^ p.natDegree))
    calc
      triangularPlanePolynomial K (q.map (algebraMap ℚ (residueLowerField N N))) A F *
          (c * (U ^ v * F ^ p.natDegree)) =
        c * triangularPlanePolynomial K
          (q.map (algebraMap ℚ (residueLowerField N N))) A F *
          (U ^ v * F ^ p.natDegree) := by ring
      _ = triangularPlanePolynomial K
          (p.map (algebraMap ℚ (residueLowerField N N))) A F *
          (W ^ b * F ^ (q.natDegree + d)) := hclear.symm
      _ = 1 * triangularPlanePolynomial K
          (p.map (algebraMap ℚ (residueLowerField N N))) A F *
          (W ^ b * F ^ (q.natDegree + d)) := by rw [one_mul]

end SkewCornerDescent.Matrix
