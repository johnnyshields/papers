/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularClassCounts

/-!
# Balance of classes outside the rational plane

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Counting a prime class in the exact
cleared identity gives its signed cap contribution. Equal signed degree removes
that contribution even when both caps belong to the same class.

Sorry-free.
-/

namespace SkewCornerDescent

open UniqueFactorizationMonoid MvPolynomial

/-- The cleared equation determines each class not appearing in the two plane numerators. -/
theorem primeClass_cleared_balance {R : Type*} [CommMonoidWithZero R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R] [DecidableEq R]
    (T P Q U W F c : R) (hP : P ≠ 0) (hQ : Q ≠ 0) (hU : U ≠ 0)
    (hW : W ≠ 0) (hF : F ≠ 0) (hc : IsUnit c)
    (hTP : ¬ T ∣ P) (hTQ : ¬ T ∣ Q) (v b a e d : ℕ)
    (heq : P * (W ^ b * F ^ (e + d)) = c * Q * (U ^ v * F ^ a)) :
    (v : ℤ) * (normalizedFactors U).count (normalize T) -
        (b : ℤ) * (normalizedFactors W).count (normalize T) =
      ((e : ℤ) + d - a) * (normalizedFactors F).count (normalize T) := by
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
    normalizedFactors_of_isUnit hc,
    normalizedFactor_count_zero_of_not_dvd T P hTP,
    normalizedFactor_count_zero_of_not_dvd T Q hTQ, zero_add] at hm
  have hz := congrArg (fun n : ℕ => (n : ℤ)) hm
  simp only [Nat.cast_add, Nat.cast_mul] at hz
  linear_combination -hz

variable {k σ : Type*} [Field k] [LinearOrder σ]

/-- Every response class with a nonclosure top balances, including either true cap class. -/
theorem planeClass_off_top_balance {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (J : ι → σ) (B : ι → MvPolynomial σ k) (L : κ → σ) (D : κ → MvPolynomial σ k)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i)
    (hD : ∀ i ∈ t, ∀ j ∈ (D i).vars, j < L i)
    {K H J₀ L₀ : σ} (hHK : H ≠ K) (hJ : J₀ < K) (hL : L₀ < K)
    {A E B₀ D₀ c : MvPolynomial σ k} (hA : ∀ j ∈ A.vars, j < K)
    (hE : ∀ j ∈ E.vars, j < H)
    (hB₀ : ∀ j ∈ B₀.vars, j < J₀) (hD₀ : ∀ j ∈ D₀.vars, j < L₀)
    (hc : IsUnit c) {p q : Polynomial k} (hp : p.Splits) (hq : q.Splits)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (v b d : ℕ)
    (hdegree : (p.natDegree : ℤ) - q.natDegree = d)
    (heq : let F := (X J₀ + B₀) * (X L₀ + D₀)
      triangularPlanePolynomial K p A F *
          ((∏ i ∈ t, (X (L i) + D i)) ^ b * F ^ (q.natDegree + d)) =
        c * triangularPlanePolynomial K q A F *
          ((∏ i ∈ s, (X (J i) + B i)) ^ v * F ^ p.natDegree)) :
    v * triangularClassCount s J B (X H + E) =
      b * triangularClassCount t L D (X H + E) := by
  classical
  let : StrongNormalizationMonoid (MvPolynomial σ k) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let F := (X J₀ + B₀) * (X L₀ + D₀)
  have hF : ∀ j ∈ F.vars, j < K := by
    intro j hj
    rcases Finset.mem_union.mp (vars_mul _ _ hj) with h | h
    · exact monicTriangularPolynomial_vars_below hJ hB₀ j h
    · exact monicTriangularPolynomial_vars_below hL hD₀ j h
  have hU0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hB i hi)).ne_zero
  have hW0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    (monicTriangularPolynomial_prime (hD i hi)).ne_zero
  have hF0 : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime hB₀).ne_zero
    (monicTriangularPolynomial_prime hD₀).ne_zero
  have hm := primeClass_cleared_balance (X H + E)
    (triangularPlanePolynomial K p A F) (triangularPlanePolynomial K q A F)
    (∏ i ∈ s, (X (J i) + B i)) (∏ i ∈ t, (X (L i) + D i)) F c
    (triangularPlanePolynomial_ne_zero_of_splits K p hp hp0 hA hF)
    (triangularPlanePolynomial_ne_zero_of_splits K q hq hq0 hA hF)
    hU0 hW0 hF0 hc
    (triangularPlanePolynomial_not_dvd_of_top_ne hHK hE hA hF p hp hp0)
    (triangularPlanePolynomial_not_dvd_of_top_ne hHK hE hA hF q hq hq0)
    v b p.natDegree q.natDegree d heq
  rw [triangularResponse_factor_count s J B hB (X H + E),
    triangularResponse_factor_count t L D hD (X H + E)] at hm
  have hz : (q.natDegree : ℤ) + d - p.natDegree = 0 := by linarith
  rw [hz, zero_mul, sub_eq_zero] at hm
  exact_mod_cast hm

end SkewCornerDescent
