/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueSingleWindowClasses
import SkewCornerDescent.SplitRationalFactors

/-!
# Active rational factors in the actual residue field

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). The actual field equation supplies
splitting and signed degree before equal root occurrences are cancelled. Its unit
is retained explicitly; the determinant sign normalization is a separate obligation.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance residueRationalFactorRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- The actual plane coordinate is not any rational constant. -/
theorem actualResidue_plane_not_rational (N : ℕ+) {K : ResidueHigherIndex N}
    {A F : ResidueHigherPolynomial N} (hA : ∀ j ∈ A.vars, j < K)
    (hF : ∀ j ∈ F.vars, j < K) (hF0 : residueHigherEval N F ≠ 0) (α : ℚ) :
    (residueHigherEval N (X K) + residueHigherEval N A) / residueHigherEval N F ≠
      algebraMap ℚ (OtherField N) α := by
  intro he
  have hr := monicTriangularPolynomial_prime
    (triangularPlaneRoot_lower hA hF (algebraMap ℚ (residueLowerField N N) α))
  apply hr.ne_zero
  apply residueHigherEval_injective N
  rw [map_zero, map_add, map_sub, map_mul]
  have hC : residueHigherEval N (C (algebraMap ℚ (residueLowerField N N) α)) =
      algebraMap ℚ (OtherField N) α := by
    simp only [residueHigherEval, aeval_C, Subfield.algebraMap_ofSubfield]
    exact (IsScalarTower.algebraMap_apply ℚ (residueLowerField N N) (OtherField N) α).symm
  rw [hC]
  have heq := (div_eq_iff hF0).mp he
  linear_combination heq

/-- The original field equation has an exact finite rational-label factorization of degree `d`.
The scalar is the rational leading-coefficient quotient, not an assumed determinant sign. -/
theorem actualResidue_rational_factorization (N : ℕ+) {ι κ : Type*}
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
    let F := (X J₀ + B₀) * (X L₀ + D₀)
    let u := (residueHigherEval N (X K) + residueHigherEval N A) / residueHigherEval N F
    p.leadingCoeff / q.leadingCoeff ≠ 0 ∧
      (∀ α ∈ splitActiveRoots p q, splitRootExponent p q α ≠ 0) ∧
      (∑ α ∈ splitActiveRoots p q, splitRootExponent p q α) = d ∧
      residueHigherEval N c *
          (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
          ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
            (residueHigherEval N F) ^ d) =
        algebraMap ℚ (OtherField N) (p.leadingCoeff / q.leadingCoeff) *
          ∏ α ∈ splitActiveRoots p q,
            (u - algebraMap ℚ (OtherField N) α) ^ splitRootExponent p q α := by
  obtain ⟨hp, hq, hdegree⟩ := actualResidue_plane_degree_balance N s t J B L D hB hD
    hJ hL A B₀ D₀ c hA hB₀ hD₀ hc p q hpq r v b d hs ht hd hdep
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  let u := (residueHigherEval N (X K) + residueHigherEval N A) / residueHigherEval N F
  have hF : ∀ j ∈ F.vars, j < K := by
    intro j hj
    rcases Finset.mem_union.mp (vars_mul _ _ hj) with h | h
    · exact monicTriangularPolynomial_vars_below hJ hB₀ j h
    · exact monicTriangularPolynomial_vars_below hL hD₀ j h
  have hF0 : residueHigherEval N F ≠ 0 := by
    have hf : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime hB₀).ne_zero
      (monicTriangularPolynomial_prime hD₀).ne_zero
    intro hz
    apply hf
    apply residueHigherEval_injective N
    simpa only [map_zero] using hz
  have hx : ∀ α : ℚ, u ≠ algebraMap ℚ (OtherField N) α :=
    actualResidue_plane_not_rational N hA hF hF0
  have hfactor := hdep.trans (splitRational_eval_factorization u p q hp hq hx)
  have hl0 : residueHigherEval N c *
      (residueHigherEval N (∏ i ∈ s, (X (J i) + B i))) ^ v /
      ((residueHigherEval N (∏ i ∈ t, (X (L i) + D i))) ^ b *
        (residueHigherEval N F) ^ d) ≠ 0 :=
    div_ne_zero (mul_ne_zero (hc.map (residueHigherEval N)).ne_zero
      (pow_ne_zero _ (actualResidue_response_product_ne_zero N s J B hB)))
      (mul_ne_zero (pow_ne_zero _ (actualResidue_response_product_ne_zero N t L D hD))
        (pow_ne_zero _ hF0))
  refine ⟨?_, fun _ hα => splitActiveRoots_exponent_ne_zero p q hα,
    (splitActiveRoots_sum p q hp hq).trans hdegree, hfactor⟩
  intro hz
  rw [hz, map_zero, zero_mul] at hfactor
  exact hl0 hfactor

end SkewCornerDescent.Matrix
