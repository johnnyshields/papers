/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResiduePlaneClassBalance
import SkewCornerDescent.PlaneClassExponents
import SkewCornerDescent.SplitRationalFactors

/-!
# Multiplicities of actual rational response classes

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`).
The original residue dependence supplies splitting and the cleared identity;
prime multiplicities then identify each rational root exponent with the signed
count of its full monic response class. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance residueClassExponentRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Each rational root exponent equals the signed multiplicity of its actual
full response class. Neither splitting nor the cleared equation is assumed. -/
theorem actualResidue_root_class_exponent (N : ℕ+) {ι κ : Type*}
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
            residueHigherEval N F) q) (α : ℚ) :
    let F := (X J₀ + B₀) * (X L₀ + D₀)
    let T := X K + (A - C (algebraMap ℚ (residueLowerField N N) α) * F)
    (v : ℤ) * triangularClassCount s J B T -
        (b : ℤ) * triangularClassCount t L D T = splitRootExponent p q α := by
  classical
  obtain ⟨hp, hq, _⟩ := actualResidue_plane_degree_balance N s t J B L D hB hD
    hJ hL A B₀ D₀ c hA hB₀ hD₀ hc p q hpq r v b d hs ht hd hdep
  let U := ∏ i ∈ s, (X (J i) + B i)
  let W := ∏ i ∈ t, (X (L i) + D i)
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  change residueHigherEval N c * (residueHigherEval N U) ^ v /
      ((residueHigherEval N W) ^ b * (residueHigherEval N F) ^ d) =
    Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
        residueHigherEval N F) p /
      Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
        residueHigherEval N F) q at hdep
  have hF0 : residueHigherEval N F ≠ 0 := by
    have hf : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime hB₀).ne_zero
      (monicTriangularPolynomial_prime hD₀).ne_zero
    intro hz
    apply hf
    exact residueHigherEval_injective N (hz.trans (map_zero _).symm)
  have hU0 := actualResidue_response_product_ne_zero N s J B hB
  have hW0 := actualResidue_response_product_ne_zero N t L D hD
  have hl0 : residueHigherEval N c * (residueHigherEval N U) ^ v /
      ((residueHigherEval N W) ^ b * (residueHigherEval N F) ^ d) ≠ 0 :=
    div_ne_zero (mul_ne_zero (hc.map (residueHigherEval N)).ne_zero (pow_ne_zero _ hU0))
      (mul_ne_zero (pow_ne_zero _ hW0) (pow_ne_zero _ hF0))
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp, map_zero, zero_div] at hdep
    exact hl0 hdep
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq, map_zero, div_zero] at hdep
    exact hl0 hdep
  have hclear := actualResidue_clear_equation N A F U W c p q v b d hF0 hU0 hW0 hc hdep
  have hm := planeClass_root_exponent s t J B L D hB hD hJ hL hA hB₀ hD₀ hc
    (p.map (algebraMap ℚ (residueLowerField N N)))
    (q.map (algebraMap ℚ (residueLowerField N N)))
    (hp.map _) (hq.map _) (Polynomial.map_ne_zero hp0) (Polynomial.map_ne_zero hq0)
    v b d (by simpa only [Polynomial.natDegree_map] using hclear)
    (algebraMap ℚ (residueLowerField N N) α)
  rw [hp.roots_map_of_injective (RingHom.injective _),
    hq.roots_map_of_injective (RingHom.injective _),
    Multiset.count_map_eq_count' _ _ (RingHom.injective _) α,
    Multiset.count_map_eq_count' _ _ (RingHom.injective _) α] at hm
  exact hm

end SkewCornerDescent.Matrix
