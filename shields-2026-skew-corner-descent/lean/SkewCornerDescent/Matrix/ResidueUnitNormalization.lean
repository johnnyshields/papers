/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueRationalFactorization
import SkewCornerDescent.PlaneUnitNormalization

/-!
# Rational-unit normalization of the actual residue equation

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). The rational leading scalar is exactly
the lower polynomial unit in the original monic response equation.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance residueUnitNormalizationRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- The actual residue equation identifies its original unit with the rational leading scalar.
No root splitting, cleared identity or rationality of the original unit is assumed. -/
theorem actualResidue_unit_normalization (N : ℕ+) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (L : κ → ResidueHigherIndex N) (D : κ → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K J₀ L₀ : ResidueHigherIndex N} (hJ : J₀ < K) (hL : L₀ < K)
    (A B₀ D₀ c : ResidueHigherPolynomial N) (hA : ∀ j ∈ A.vars, j < K)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) (p q : Polynomial ℚ) (hpq : IsCoprime p q) (r v b d : ℕ)
    (hs : s.card + 1 = r * b) (ht : t.card + 1 = r * v) (hd : d + v = b)
    (hdep : let F := (X J₀ + B₀) * (X L₀ + D₀)
      residueHigherEval N c *
          (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
          ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
            (residueHigherEval N F) ^ d) =
        Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) p /
          Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) q) :
    c = C (algebraMap ℚ (residueLowerField N N) (p.leadingCoeff / q.leadingCoeff)) := by
  obtain ⟨hp, hq, _⟩ := actualResidue_plane_degree_balance N s t J B L D hB hD
    hJ hL A B₀ D₀ c hA hB₀ hD₀ hc p q hpq r v b d hs ht hd hdep
  have hcoef := (actualResidue_rational_factorization N s t J B L D hB hD
    hJ hL A B₀ D₀ c hA hB₀ hD₀ hc p q hpq r v b d hs ht hd hdep).1
  have hp0 : p ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (div_ne_zero_iff.mp hcoef).1
  have hq0 : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (div_ne_zero_iff.mp hcoef).2
  let U := ∏ i ∈ s, (X (J i) + B i)
  let W := ∏ i ∈ t, (X (L i) + D i)
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  have hF0 : residueHigherEval N F ≠ 0 := by
    have hf : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime hB₀).ne_zero
      (monicTriangularPolynomial_prime hD₀).ne_zero
    intro hz
    apply hf
    apply residueHigherEval_injective N
    simpa only [map_zero] using hz
  have hU0 := actualResidue_response_product_ne_zero N s J B hB
  have hW0 := actualResidue_response_product_ne_zero N t L D hD
  have hclear := actualResidue_clear_equation N A F U W c p q v b d hF0 hU0 hW0 hc hdep
  have hu := planeFactor_unit_normalization s t J B L D hB hD hJ hL hA hB₀ hD₀ hc
    (p := p.map (algebraMap ℚ (residueLowerField N N)))
    (q := q.map (algebraMap ℚ (residueLowerField N N)))
    (hp.map _) (hq.map _) (Polynomial.map_ne_zero hp0) (Polynomial.map_ne_zero hq0) v b d
    (by simpa only [Polynomial.natDegree_map] using hclear)
  simpa only [Polynomial.leadingCoeff_map_of_injective
    (RingHom.injective (algebraMap ℚ (residueLowerField N N))), ← map_div₀] using hu

end SkewCornerDescent.Matrix
