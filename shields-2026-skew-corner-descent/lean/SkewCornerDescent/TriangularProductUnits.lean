/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularClassCounts

/-!
# Unit uniqueness for products of full monic responses

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Full monic triangular primes have a
unique representative in each associate class, so associated products are equal.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial UniqueFactorizationMonoid

variable {k σ : Type*} [Field k] [LinearOrder σ]

/-- Associated products of full monic triangular primes have exactly the same factors. -/
theorem triangularProducts_associated_eq (s t : Multiset (MvPolynomial σ k))
    (hs : ∀ z ∈ s, ∃ J B, (∀ i ∈ B.vars, i < J) ∧ z = X J + B)
    (ht : ∀ z ∈ t, ∃ J B, (∀ i ∈ B.vars, i < J) ∧ z = X J + B)
    (hassoc : Associated s.prod t.prod) : s = t := by
  classical
  let : StrongNormalizationMonoid (MvPolynomial σ k) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  have hsprime : ∀ z ∈ s, Irreducible z := by
    intro z hz
    obtain ⟨J, B, hB, rfl⟩ := hs z hz
    exact (monicTriangularPolynomial_prime hB).irreducible
  have htprime : ∀ z ∈ t, Irreducible z := by
    intro z hz
    obtain ⟨J, B, hB, rfl⟩ := ht z hz
    exact (monicTriangularPolynomial_prime hB).irreducible
  have hm := hassoc.normalizedFactors_eq
  rw [normalizedFactors_prod_eq s hsprime, normalizedFactors_prod_eq t htprime] at hm
  have hr : Multiset.Rel (fun a b => normalize a = normalize b) s t :=
    Multiset.rel_map.mp (Multiset.rel_eq.mpr hm)
  apply Multiset.rel_eq.mp
  apply hr.mono
  intro a ha b hb hab
  obtain ⟨J, B, hB, rfl⟩ := hs a ha
  obtain ⟨L, D, hD, rfl⟩ := ht b hb
  obtain ⟨hJL, hBD⟩ := (monicTriangularPolynomial_associated_iff hB hD).mp
    (normalize_eq_normalize_iff_associated.mp hab)
  rw [hJL, hBD]

/-- Two unit-scaled products of full monic responses have the same unit scalar. -/
theorem triangularProducts_scalar_eq (s t : Multiset (MvPolynomial σ k))
    (hs : ∀ z ∈ s, ∃ J B, (∀ i ∈ B.vars, i < J) ∧ z = X J + B)
    (ht : ∀ z ∈ t, ∃ J B, (∀ i ∈ B.vars, i < J) ∧ z = X J + B)
    {a b : MvPolynomial σ k} (ha : IsUnit a) (hb : IsUnit b)
    (heq : a * s.prod = b * t.prod) : a = b := by
  have hassoc : Associated s.prod t.prod :=
    (associated_unit_mul_left s.prod a ha).symm.trans
      ((Associated.of_eq heq).trans (associated_unit_mul_left t.prod b hb))
  have hst := triangularProducts_associated_eq s t hs ht hassoc
  have ht0 : t.prod ≠ 0 := Multiset.prod_ne_zero fun hz => by
    obtain ⟨J, B, hB, he⟩ := ht 0 hz
    exact (monicTriangularPolynomial_prime hB).ne_zero he.symm
  rw [hst] at heq
  exact mul_right_cancel₀ ht0 heq

end SkewCornerDescent
