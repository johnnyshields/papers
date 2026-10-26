/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResiduePlaneClassBalance

/-!
# Nonplane classes at the actual closure top

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Rational splitting forces every
closure-top prime in a plane numerator to have its entire rational root correction.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial UniqueFactorizationMonoid

noncomputable local instance residueNonplaneRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- A full correction outside every rational label class cannot divide the plane numerator. -/
theorem actualResidue_nonplane_not_dvd (N : ℕ+) {K : ResidueHigherIndex N}
    {E A F : ResidueHigherPolynomial N} (hE : ∀ j ∈ E.vars, j < K)
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (p : Polynomial ℚ) (hp : p.Splits) (hp0 : p ≠ 0)
    (hmiss : ∀ α : ℚ, E ≠ A - C (algebraMap ℚ (residueLowerField N N) α) * F) :
    ¬ X K + E ∣ triangularPlanePolynomial K
      (p.map (algebraMap ℚ (residueLowerField N N))) A F := by
  apply triangularPlanePolynomial_not_dvd_of_root_classes hE hA hF
    _ (hp.map _) (Polynomial.map_ne_zero hp0)
  intro α hα
  rw [hp.roots_map_of_injective (RingHom.injective _)] at hα
  obtain ⟨β, _, rfl⟩ := Multiset.mem_map.mp hα
  exact hmiss β

/-- Full closure-top classes outside the rational plane balance in the actual field equation. -/
theorem actualResidue_nonplane_class_balance (N : ℕ+) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (L : κ → ResidueHigherIndex N) (D : κ → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K J₀ L₀ : ResidueHigherIndex N} (hJ : J₀ < K) (hL : L₀ < K)
    (A E B₀ D₀ c : ResidueHigherPolynomial N) (hA : ∀ j ∈ A.vars, j < K)
    (hE : ∀ j ∈ E.vars, j < K)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) (p q : Polynomial ℚ) (hpq : IsCoprime p q) (r v b d : ℕ)
    (hs : s.card + 1 = r * b) (ht : t.card + 1 = r * v) (hd : d + v = b)
    (hmiss : let F := (X J₀ + B₀) * (X L₀ + D₀)
      ∀ α : ℚ, E ≠ A - C (algebraMap ℚ (residueLowerField N N) α) * F)
    (hdep : let F := (X J₀ + B₀) * (X L₀ + D₀)
      residueHigherEval N c *
          (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
          ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
            (residueHigherEval N F) ^ d) =
        Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) p /
          Polynomial.aeval ((residueHigherEval N (X K) + residueHigherEval N A) /
            residueHigherEval N F) q) :
    v * triangularClassCount s J B (X K + E) =
      b * triangularClassCount t L D (X K + E) := by
  classical
  let : StrongNormalizationMonoid (ResidueHigherPolynomial N) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  obtain ⟨hp, hq, hdegree⟩ := actualResidue_plane_degree_balance N s t J B L D hB hD
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
  have hF : ∀ j ∈ F.vars, j < K := by
    intro j hj
    rcases Finset.mem_union.mp (vars_mul _ _ hj) with h | h
    · exact monicTriangularPolynomial_vars_below hJ hB₀ j h
    · exact monicTriangularPolynomial_vars_below hL hD₀ j h
  have hFp0 : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime hB₀).ne_zero
    (monicTriangularPolynomial_prime hD₀).ne_zero
  have hF0 : residueHigherEval N F ≠ 0 := by
    intro hz
    apply hFp0
    apply residueHigherEval_injective N
    simpa only [map_zero] using hz
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
  have hUp0 : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hB i hi)).ne_zero
  have hWp0 : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hD i hi)).ne_zero
  have hm := primeClass_cleared_balance (X K + E)
    (triangularPlanePolynomial K (p.map (algebraMap ℚ (residueLowerField N N))) A F)
    (triangularPlanePolynomial K (q.map (algebraMap ℚ (residueLowerField N N))) A F)
    U W F c
    (triangularPlanePolynomial_ne_zero_of_splits K _ (hp.map _)
      (Polynomial.map_ne_zero hp0) hA hF)
    (triangularPlanePolynomial_ne_zero_of_splits K _ (hq.map _)
      (Polynomial.map_ne_zero hq0) hA hF)
    hUp0 hWp0 hFp0 hc
    (actualResidue_nonplane_not_dvd N hE hA hF p hp hp0 hmiss)
    (actualResidue_nonplane_not_dvd N hE hA hF q hq hq0 hmiss)
    v b p.natDegree q.natDegree d hclear
  rw [triangularResponse_factor_count s J B hB (X K + E),
    triangularResponse_factor_count t L D hD (X K + E)] at hm
  have hz : (q.natDegree : ℤ) + d - p.natDegree = 0 := by linarith
  rw [hz, zero_mul, sub_eq_zero] at hm
  exact_mod_cast hm

end SkewCornerDescent.Matrix
