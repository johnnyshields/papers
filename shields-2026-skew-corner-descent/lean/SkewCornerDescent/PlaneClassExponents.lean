/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PlaneClassBalance

/-!
# Exact exponents of rational plane response classes

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`). Full
monic root classes distinguish rational labels; their prime multiplicities in
the cleared numerator retain every repeated root. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial UniqueFactorizationMonoid

variable {k σ : Type*} [Field k] [LinearOrder σ]

/-- Distinct rational labels give distinct full monic prime classes whenever the
cap denominator is nonzero. No independence of derived response functions is assumed. -/
theorem triangularPlaneRoot_associated_iff {K : σ} {A F : MvPolynomial σ k}
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K) (hF0 : F ≠ 0)
    (α β : k) :
    Associated (X K + (A - C α * F)) (X K + (A - C β * F)) ↔ α = β := by
  constructor
  · intro h
    have hh := ((monicTriangularPolynomial_associated_iff
      (triangularPlaneRoot_lower hA hF α) (triangularPlaneRoot_lower hA hF β)).mp h).2
    have he : C α * F = C β * F := by linear_combination -hh
    exact MvPolynomial.C_injective _ _ (mul_right_cancel₀ hF0 he)
  · rintro rfl
    exact Associated.refl _

/-- A full monic rational root class has exactly its polynomial root multiplicity. -/
theorem triangularPlanePolynomial_root_factor_count
    [NormalizationMonoid (MvPolynomial σ k)] [DecidableEq (MvPolynomial σ k)]
    [DecidableEq k]
    (K : σ) (p : Polynomial k) (hp : p.Splits) (hp0 : p ≠ 0)
    {A F : MvPolynomial σ k} (hA : ∀ j ∈ A.vars, j < K)
    (hF : ∀ j ∈ F.vars, j < K) (hF0 : F ≠ 0) (α : k) :
    (normalizedFactors (triangularPlanePolynomial K p A F)).count
      (normalize (X K + (A - C α * F))) = p.roots.count α := by
  classical
  have hu : IsUnit (C p.leadingCoeff : MvPolynomial σ k) :=
    (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0)).map C
  rw [triangularPlanePolynomial_roots K p hp]
  rw [(associated_unit_mul_left _ _ hu).normalizedFactors_eq, normalizedFactors_prod_eq]
  · rw [Multiset.map_map]
    apply Multiset.count_map_eq_count'
    intro β γ he
    apply (triangularPlaneRoot_associated_iff hA hF hF0 β γ).mp
    exact normalize_eq_normalize_iff_associated.mp he
  · intro T hT
    obtain ⟨β, _, rfl⟩ := Multiset.mem_map.mp hT
    exact (monicTriangularPolynomial_prime (triangularPlaneRoot_lower hA hF β)).irreducible

/-- Counting any prime class in the cleared identity retains its two plane multiplicities. -/
theorem primeClass_cleared_exponent {R : Type*} [CommMonoidWithZero R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R] [DecidableEq R]
    (T P Q U W F c : R) (hP : P ≠ 0) (hQ : Q ≠ 0) (hU : U ≠ 0)
    (hW : W ≠ 0) (hF : F ≠ 0) (hc : IsUnit c)
    (hTF : (normalizedFactors F).count (normalize T) = 0) (v b a e d : ℕ)
    (heq : P * (W ^ b * F ^ (e + d)) = c * Q * (U ^ v * F ^ a)) :
    (v : ℤ) * (normalizedFactors U).count (normalize T) -
        (b : ℤ) * (normalizedFactors W).count (normalize T) =
      ((normalizedFactors P).count (normalize T) : ℤ) -
        (normalizedFactors Q).count (normalize T) := by
  classical
  let : Nontrivial R := nontrivial_of_ne P 0 hP
  have hm := congrArg (fun z => (normalizedFactors z).count (normalize T)) heq
  simp only [normalizedFactors_mul hP (mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hF)),
    normalizedFactors_mul (mul_ne_zero hc.ne_zero hQ)
      (mul_ne_zero (pow_ne_zero _ hU) (pow_ne_zero _ hF)),
    normalizedFactors_mul hc.ne_zero hQ,
    normalizedFactors_mul (pow_ne_zero b hW) (pow_ne_zero (e + d) hF),
    normalizedFactors_mul (pow_ne_zero v hU) (pow_ne_zero a hF),
    normalizedFactors_pow, Multiset.count_add, Multiset.count_nsmul,
    normalizedFactors_of_isUnit hc, zero_add,
    hTF, mul_zero, add_zero] at hm
  have hz := congrArg (fun n : ℕ => (n : ℤ)) hm
  simp only [Nat.cast_add, Nat.cast_mul] at hz
  linear_combination -hz

/-- The cleared polynomial identity identifies the signed internal count of every
rational plane class with its numerator-minus-denominator root multiplicity. -/
theorem planeClass_root_exponent [DecidableEq k] {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (J : ι → σ) (B : ι → MvPolynomial σ k) (L : κ → σ) (D : κ → MvPolynomial σ k)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K J₀ L₀ : σ} (hJ : J₀ < K) (hL : L₀ < K)
    {A B₀ D₀ c : MvPolynomial σ k} (hA : ∀ j ∈ A.vars, j < K)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) (p q : Polynomial k) (hp : p.Splits) (hq : q.Splits)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (v b d : ℕ)
    (heq : let F := (X J₀ + B₀) * (X L₀ + D₀)
      triangularPlanePolynomial K p A F *
          ((∏ i ∈ t, (X (L i) + D i)) ^ b * F ^ (q.natDegree + d)) =
        c * triangularPlanePolynomial K q A F *
          ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ p.natDegree)) (α : k) :
    let F := (X J₀ + B₀) * (X L₀ + D₀)
    (v : ℤ) * triangularClassCount s J B (X K + (A - C α * F)) -
        (b : ℤ) * triangularClassCount t L D (X K + (A - C α * F)) =
      (p.roots.count α : ℤ) - q.roots.count α := by
  classical
  dsimp only at heq ⊢
  let : StrongNormalizationMonoid (MvPolynomial σ k) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  let T := X K + (A - C α * F)
  have hF : ∀ j ∈ F.vars, j < K := by
    intro j hj
    rcases Finset.mem_union.mp (vars_mul _ _ hj) with hj | hj
    · exact monicTriangularPolynomial_vars_below hJ hB₀ j hj
    · exact monicTriangularPolynomial_vars_below hL hD₀ j hj
  have hF0 : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime hB₀).ne_zero
    (monicTriangularPolynomial_prime hD₀).ne_zero
  have hT := monicTriangularPolynomial_prime (triangularPlaneRoot_lower hA hF α)
  have hnoF : ¬ T ∣ F := by
    intro hd
    rcases hT.dvd_or_dvd hd with hd | hd
    · have he := hT.associated_of_dvd (monicTriangularPolynomial_prime hB₀) hd
      exact (ne_of_lt hJ) ((monicTriangularPolynomial_associated_iff
        (triangularPlaneRoot_lower hA hF α) hB₀).mp he).1.symm
    · have he := hT.associated_of_dvd (monicTriangularPolynomial_prime hD₀) hd
      exact (ne_of_lt hL) ((monicTriangularPolynomial_associated_iff
        (triangularPlaneRoot_lower hA hF α) hD₀).mp he).1.symm
  have hcountF := normalizedFactor_count_zero_of_not_dvd T F hnoF
  have hU0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hB i hi)).ne_zero
  have hW0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hD i hi)).ne_zero
  have hP0 := triangularPlanePolynomial_ne_zero_of_splits K p hp hp0 hA hF
  have hQ0 := triangularPlanePolynomial_ne_zero_of_splits K q hq hq0 hA hF
  have hm := primeClass_cleared_exponent T
    (triangularPlanePolynomial K p A F) (triangularPlanePolynomial K q A F)
    (∏ i ∈ s, (X (J i) + B i)) (∏ i ∈ t, (X (L i) + D i)) F c
    hP0 hQ0 hU0 hW0 hF0 hc hcountF v b p.natDegree q.natDegree d heq
  rw [triangularResponse_factor_count s J B hB T,
    triangularResponse_factor_count t L D hD T,
    triangularPlanePolynomial_root_factor_count K p hp hp0 hA hF hF0 α,
    triangularPlanePolynomial_root_factor_count K q hq hq0 hA hF hF0 α] at hm
  exact hm

end SkewCornerDescent
