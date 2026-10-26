/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualResiduePlanePrimes
import SkewCornerDescent.Matrix.ResiduePlaneProduct
import SkewCornerDescent.TriangularPlaneDivisibility
import SkewCornerDescent.LinearFactorSplitting

/-!
# Rational numerator factors forced by the actual response product

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). A cleared exact residue identity,
not a response-factorization assumption, forces every monic irreducible numerator
factor to be linear with a rational full-response label.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open MvPolynomial

noncomputable local instance residuePlaneFactorRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- Factor classification from cross multiplication of the exact residue equation.
The auxiliary left factor retains every denominator factor and multiplicity. -/
theorem actualResidue_cross_factor (N : ℕ+) {ι : Type*} (s : Finset ι)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    {K : ResidueHigherIndex N} {A F H c : ResidueHigherPolynomial N}
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (hF0 : residueHigherEval N F ≠ 0) (hc : IsUnit c)
    {p q π : Polynomial ℚ} (hpq : IsCoprime p q)
    (hπ : π.Monic) (hirr : Irreducible π) (hπp : π ∣ p) (v m : ℕ)
    (heq : triangularPlanePolynomial K
        (p.map (algebraMap ℚ (residueLowerField N N))) A F * H =
      c * triangularPlanePolynomial K
        (q.map (algebraMap ℚ (residueLowerField N N))) A F *
        ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ m)) :
    π.natDegree = 1 ∧ ∃ i ∈ s, J i = K ∧ ∃ α : ℚ, Polynomial.IsRoot π α ∧
      residueHigherEval N (B i) = residueHigherEval N A -
        algebraMap ℚ (OtherField N) α * residueHigherEval N F := by
  let φ := Polynomial.mapRingHom (algebraMap ℚ (residueLowerField N N))
  let Qπ := triangularPlanePolynomial K (φ π) A F
  have hprime : Prime Qπ := (actualResidue_plane_irreducible N hπ hirr hA hF hF0).prime
  have hdeg : 0 < (φ π).natDegree := by
    change 0 < (π.map (algebraMap ℚ (residueLowerField N N))).natDegree
    rw [Polynomial.natDegree_map]
    exact hπ.natDegree_pos_of_not_isUnit hirr.not_isUnit
  have hcop : IsCoprime (φ π) (φ q) :=
    (hpq.of_isCoprime_of_dvd_left hπp).map φ
  have hnoq : ¬Qπ ∣ triangularPlanePolynomial K (φ q) A F :=
    triangularPlanePolynomial_not_dvd_coprime K (residueHigherEval N)
      (hπ.map _) hdeg hcop hA hF hF0
  have hnoF : ¬Qπ ∣ F := triangularPlanePolynomial_not_dvd_lower K
    (residueHigherEval N) (hπ.map _) hdeg hA hF hF hF0
  have hdp : Qπ ∣ triangularPlanePolynomial K (φ p) A F :=
    triangularPlanePolynomial_dvd K (_root_.map_dvd φ hπp) A F
  have hd : Qπ ∣ c * triangularPlanePolynomial K (φ q) A F *
      ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ m) := by
    change triangularPlanePolynomial K (φ p) A F * H =
      c * triangularPlanePolynomial K (φ q) A F *
        ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ m) at heq
    rw [← heq]
    exact dvd_mul_of_dvd_left hdp H
  have hprod : Qπ ∣ (∏ i ∈ s, (X (J i) + B i)) := by
    rcases hprime.dvd_or_dvd hd with h | h
    · rcases hprime.dvd_or_dvd h with h | h
      · exact (hprime.not_isUnit (isUnit_of_dvd_unit h hc)).elim
      · exact (hnoq h).elim
    · rcases hprime.dvd_or_dvd h with h | h
      · exact hprime.dvd_of_dvd_pow h
      · exact (hnoF (hprime.dvd_of_dvd_pow h)).elim
  obtain ⟨hdeg, i, hi, hJ, α, hα, he⟩ :=
    actualResidue_plane_product_factor N s J B hB hπ hirr hA hF hF0 hprod
  refine ⟨hdeg, i, hi, hJ, α, hα, ?_⟩
  have hcast : algebraMap ℚ (OtherField N) α = (α : OtherField N) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ (OtherField N)) α
  rw [hcast]
  exact he

/-- Every numerator factor is accounted for, so the rational numerator splits completely. -/
theorem actualResidue_cross_splits (N : ℕ+) {ι : Type*} (s : Finset ι)
    (J : ι → ResidueHigherIndex N) (B : ι → ResidueHigherPolynomial N)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    {K : ResidueHigherIndex N} {A F H c : ResidueHigherPolynomial N}
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (hF0 : residueHigherEval N F ≠ 0) (hc : IsUnit c)
    {p q : Polynomial ℚ} (hpq : IsCoprime p q) (v m : ℕ)
    (heq : triangularPlanePolynomial K
        (p.map (algebraMap ℚ (residueLowerField N N))) A F * H =
      c * triangularPlanePolynomial K
        (q.map (algebraMap ℚ (residueLowerField N N))) A F *
        ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ m)) : p.Splits := by
  apply polynomial_splits_of_linear_irreducible_divisors
  intro π hπ hirr hπp
  exact (actualResidue_cross_factor N s J B hB hA hF hF0 hc hpq
    hπ hirr hπp v m heq).1

end SkewCornerDescent.Matrix
