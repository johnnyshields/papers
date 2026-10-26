/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularPlaneRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Prime-factor mass of the full plane numerator

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). The factor mass counts actual polynomial
primes with multiplicity, including repeated end aliases.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial UniqueFactorizationMonoid

variable {k σ : Type*} [Field k] [LinearOrder σ]

/-- Every rationally labeled full correction remains strictly below the closure top. -/
theorem triangularPlaneRoot_lower {K : σ} {A F : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) (α : k) :
    ∀ i ∈ (A - C α * F).vars, i < K := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (vars_sub_subset A hi) with h | h
  · exact hA i h
  · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · simp only [vars_C, Finset.notMem_empty] at h
    · exact hF i h

/-- A split nonzero numerator cannot vanish as an original-coordinate polynomial. -/
theorem triangularPlanePolynomial_ne_zero_of_splits (K : σ) (p : Polynomial k)
    (hp : p.Splits) (hp0 : p ≠ 0) {A F : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) :
    triangularPlanePolynomial K p A F ≠ 0 := by
  rw [triangularPlanePolynomial_roots K p hp]
  apply mul_ne_zero
  · exact (map_ne_zero MvPolynomial.C).mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  · apply Multiset.prod_ne_zero
    intro hz
    obtain ⟨α, _, he⟩ := Multiset.mem_map.mp hz
    exact (monicTriangularPolynomial_prime
      (triangularPlaneRoot_lower hA hF α)).ne_zero he

variable [NormalizationMonoid (MvPolynomial σ k)]

/-- A finite response product has exactly one prime factor for every occurrence. -/
theorem triangularResponse_factor_mass {ι : Type*} (s : Finset ι)
    (J : ι → σ) (B : ι → MvPolynomial σ k)
    (hB : ∀ i ∈ s, ∀ j ∈ (B i).vars, j < J i) :
    (normalizedFactors (∏ i ∈ s, (X (J i) + B i))).card = s.card := by
  classical
  change (normalizedFactors (s.val.map (fun i => X (J i) + B i)).prod).card = s.card
  rw [normalizedFactors_prod_eq]
  · simp only [Multiset.card_map]
    rfl
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hp
    exact (monicTriangularPolynomial_prime (hB i hi)).irreducible

/-- A split nonzero plane numerator has factor mass exactly its rational degree. -/
theorem triangularPlanePolynomial_factor_mass (K : σ) (p : Polynomial k)
    (hp : p.Splits) (hp0 : p ≠ 0) {A F : MvPolynomial σ k}
    (hA : ∀ i ∈ A.vars, i < K) (hF : ∀ i ∈ F.vars, i < K) :
    (normalizedFactors (triangularPlanePolynomial K p A F)).card = p.natDegree := by
  classical
  have hu : IsUnit (C p.leadingCoeff : MvPolynomial σ k) :=
    (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0)).map C
  rw [triangularPlanePolynomial_roots K p hp]
  rw [(associated_unit_mul_left _ _ hu).normalizedFactors_eq, normalizedFactors_prod_eq]
  · rw [Multiset.card_map, Multiset.card_map, hp.natDegree_eq_card_roots]
  · intro q hq
    obtain ⟨α, _, rfl⟩ := Multiset.mem_map.mp hq
    exact (monicTriangularPolynomial_prime (triangularPlaneRoot_lower hA hF α)).irreducible

end SkewCornerDescent
