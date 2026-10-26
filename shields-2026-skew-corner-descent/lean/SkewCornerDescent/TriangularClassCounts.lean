/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PlaneFactorBalance
import Mathlib.Algebra.BigOperators.Associated

/-!
# Exact counts of full triangular response classes

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Class counts preserve repeated equal
responses. A class with a different protected top cannot divide a split plane numerator.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial UniqueFactorizationMonoid

variable {k σ ι : Type*} [Field k] [LinearOrder σ]

/-- Number of occurrences in a full monic response class, including repeated responses. -/
noncomputable def triangularClassCount (s : Finset ι) (J : ι → σ)
    (B : ι → MvPolynomial σ k) (T : MvPolynomial σ k) : ℕ := by
  classical
  exact (s.filter fun i => Associated T (X (J i) + B i)).card

/-- Normalized prime multiplicity counts exactly the original response occurrences. -/
theorem triangularResponse_factor_count [NormalizationMonoid (MvPolynomial σ k)]
    [DecidableEq (MvPolynomial σ k)]
    (s : Finset ι) (J : ι → σ) (B : ι → MvPolynomial σ k)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i) (T : MvPolynomial σ k) :
    (normalizedFactors (∏ i ∈ s, (X (J i) + B i))).count (normalize T) =
      triangularClassCount s J B T := by
  classical
  change (normalizedFactors (s.val.map (fun i => X (J i) + B i)).prod).count _ = _
  rw [normalizedFactors_prod_eq _ (by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
    exact (monicTriangularPolynomial_prime (hB i hi)).irreducible),
    Multiset.map_map, Multiset.count_map]
  simp only [Function.comp_apply, normalize_eq_normalize_iff_associated]
  rfl

/-- A class away from the plane's protected top contributes no prime to its numerator. -/
theorem triangularPlanePolynomial_not_dvd_of_top_ne {J K : σ} (hJK : J ≠ K)
    {B A F : MvPolynomial σ k} (hB : ∀ j ∈ B.vars, j < J)
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (p : Polynomial k) (hp : p.Splits) (hp0 : p ≠ 0) :
    ¬ X J + B ∣ triangularPlanePolynomial K p A F := by
  classical
  intro hd
  rw [triangularPlanePolynomial_roots K p hp A F] at hd
  have hT := monicTriangularPolynomial_prime hB
  rcases hT.dvd_or_dvd hd with hc | hr
  · have hu : IsUnit (C p.leadingCoeff : MvPolynomial σ k) :=
      (isUnit_iff_eq_C_of_isReduced).mpr ⟨p.leadingCoeff,
        isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0), rfl⟩
    exact hT.not_isUnit (isUnit_of_dvd_unit hc hu)
  · obtain ⟨α, _, hα⟩ := hT.exists_mem_multiset_map_dvd hr
    have ha := triangularPlaneRoot_lower hA hF α
    have hassoc := hT.associated_of_dvd (monicTriangularPolynomial_prime ha) hα
    exact hJK ((monicTriangularPolynomial_associated_iff hB ha).mp hassoc).1

/-- At the closure top, only the full root correction classes can divide a plane numerator. -/
theorem triangularPlanePolynomial_not_dvd_of_root_classes {K : σ}
    {E A F : MvPolynomial σ k} (hE : ∀ j ∈ E.vars, j < K)
    (hA : ∀ j ∈ A.vars, j < K) (hF : ∀ j ∈ F.vars, j < K)
    (p : Polynomial k) (hp : p.Splits) (hp0 : p ≠ 0)
    (hmiss : ∀ α ∈ p.roots, E ≠ A - C α * F) :
    ¬ X K + E ∣ triangularPlanePolynomial K p A F := by
  classical
  intro hd
  rw [triangularPlanePolynomial_roots K p hp A F] at hd
  have hT := monicTriangularPolynomial_prime hE
  rcases hT.dvd_or_dvd hd with hc | hr
  · have hu : IsUnit (C p.leadingCoeff : MvPolynomial σ k) :=
      (isUnit_iff_eq_C_of_isReduced).mpr ⟨p.leadingCoeff,
        isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0), rfl⟩
    exact hT.not_isUnit (isUnit_of_dvd_unit hc hu)
  · obtain ⟨α, hα, hdiv⟩ := hT.exists_mem_multiset_map_dvd hr
    have ha := triangularPlaneRoot_lower hA hF α
    have hassoc := hT.associated_of_dvd (monicTriangularPolynomial_prime ha) hdiv
    exact hmiss α hα ((monicTriangularPolynomial_associated_iff hE ha).mp hassoc).2

/-- A nondividing class has zero normalized multiplicity, independently of normalization. -/
theorem normalizedFactor_count_zero_of_not_dvd
    {R : Type*} [CommMonoidWithZero R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R] (T P : R) (h : ¬ T ∣ P) :
    (normalizedFactors P).count (normalize T) = 0 := by
  classical
  apply Multiset.count_eq_zero.mpr
  intro hm
  exact h (normalize_dvd_iff.mp (dvd_of_mem_normalizedFactors hm))

end SkewCornerDescent
