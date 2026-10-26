/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularPlaneFactorMass

/-!
# Plane exponent balance with both true caps

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Prime-factor mass of the exact cleared
identity retains both cap occurrences even when their prime classes coincide.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial UniqueFactorizationMonoid

variable {k σ : Type*} [Field k] [LinearOrder σ]

/-- A triangular response with smaller protected top lies strictly below the closure top. -/
theorem monicTriangularPolynomial_vars_below {J K : σ} (hJK : J < K)
    {B : MvPolynomial σ k} (hB : ∀ i ∈ B.vars, i < J) :
    ∀ i ∈ (X J + B).vars, i < K := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (vars_add_subset _ _ hi) with h | h
  · simp only [vars_X, Finset.mem_singleton] at h
    exact h ▸ hJK
  · exact lt_trans (hB i h) hJK

/-- The sum of plane exponents is fixed by the response counts and the two cap occurrences. -/
theorem planeFactor_degree_balance {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (J : ι → σ) (B : ι → MvPolynomial σ k) (L : κ → σ) (D : κ → MvPolynomial σ k)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K J₀ L₀ : σ} (hJ : J₀ < K) (hL : L₀ < K)
    {A B₀ D₀ c : MvPolynomial σ k} (hA : ∀ j ∈ A.vars, j < K)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) {p q : Polynomial k} (hp : p.Splits) (hq : q.Splits)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (v b d : ℕ)
    (heq : let F := (X J₀ + B₀) * (X L₀ + D₀)
      triangularPlanePolynomial K p A F *
          ((∏ i ∈ t, (X (L i) + D i)) ^ b * F ^ (q.natDegree + d)) =
        c * triangularPlanePolynomial K q A F *
          ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ p.natDegree)) :
    (p.natDegree : ℤ) - q.natDegree =
      (b : ℤ) * t.card - (v : ℤ) * s.card + 2 * d := by
  classical
  let : StrongNormalizationMonoid (MvPolynomial σ k) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let U := ∏ i ∈ s, (X (J i) + B i)
  let W := ∏ i ∈ t, (X (L i) + D i)
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  let P := triangularPlanePolynomial K p A F
  let Q := triangularPlanePolynomial K q A F
  have hF : ∀ j ∈ F.vars, j < K := by
    intro j hj
    rcases Finset.mem_union.mp (vars_mul _ _ hj) with h | h
    · exact monicTriangularPolynomial_vars_below hJ hB₀ j h
    · exact monicTriangularPolynomial_vars_below hL hD₀ j h
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hB i hi)).ne_zero
  have hW0 : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hD i hi)).ne_zero
  have hF0 : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime hB₀).ne_zero
    (monicTriangularPolynomial_prime hD₀).ne_zero
  have hP0 : P ≠ 0 := triangularPlanePolynomial_ne_zero_of_splits K p hp hp0 hA hF
  have hQ0 : Q ≠ 0 := triangularPlanePolynomial_ne_zero_of_splits K q hq hq0 hA hF
  have hmassU : (normalizedFactors U).card = s.card := triangularResponse_factor_mass s J B hB
  have hmassW : (normalizedFactors W).card = t.card := triangularResponse_factor_mass t L D hD
  have hmassF : (normalizedFactors F).card = 2 := by
    rw [normalizedFactors_mul (monicTriangularPolynomial_prime hB₀).ne_zero
      (monicTriangularPolynomial_prime hD₀).ne_zero, Multiset.card_add,
      normalizedFactors_irreducible (monicTriangularPolynomial_prime hB₀).irreducible,
      normalizedFactors_irreducible (monicTriangularPolynomial_prime hD₀).irreducible,
      Multiset.card_singleton, Multiset.card_singleton]
  have hmassP : (normalizedFactors P).card = p.natDegree :=
    triangularPlanePolynomial_factor_mass K p hp hp0 hA hF
  have hmassQ : (normalizedFactors Q).card = q.natDegree :=
    triangularPlanePolynomial_factor_mass K q hq hq0 hA hF
  change P * (W ^ b * F ^ (q.natDegree + d)) = c * Q * (U ^ v * F ^ p.natDegree) at heq
  have hm := congrArg (fun z => (normalizedFactors z).card) heq
  simp only [normalizedFactors_mul hP0 (mul_ne_zero (pow_ne_zero _ hW0) (pow_ne_zero _ hF0)),
    normalizedFactors_mul (mul_ne_zero hc.ne_zero hQ0)
      (mul_ne_zero (pow_ne_zero _ hU0) (pow_ne_zero _ hF0)),
    normalizedFactors_mul hc.ne_zero hQ0,
    normalizedFactors_mul (pow_ne_zero b hW0) (pow_ne_zero (q.natDegree + d) hF0),
    normalizedFactors_mul (pow_ne_zero v hU0) (pow_ne_zero p.natDegree hF0),
    normalizedFactors_pow, Multiset.card_add, Multiset.card_nsmul,
    normalizedFactors_of_isUnit hc,
    hmassU, hmassW, hmassF, hmassP, hmassQ, zero_add] at hm
  have hz := congrArg (fun n : ℕ => (n : ℤ)) hm
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hz
  linarith

end SkewCornerDescent
