/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Splitting from monic irreducible divisors

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Linear monic prime factors give a
complete polynomial factorization, including units and the zero polynomial.

Sorry-free.
-/

namespace SkewCornerDescent

open UniqueFactorizationMonoid

/-- Every polynomial whose monic irreducible divisors are linear splits over its base field. -/
theorem polynomial_splits_of_linear_irreducible_divisors {k : Type*} [Field k]
    (p : Polynomial k)
    (h : ∀ π : Polynomial k, π.Monic → Irreducible π → π ∣ p → π.natDegree = 1) :
    p.Splits := by
  classical
  by_cases hp : p = 0
  · rw [hp]
    exact Polynomial.Splits.zero
  have hs : (normalizedFactors p).prod.Splits := by
    apply Polynomial.Splits.multisetProd
    intro π hπ
    obtain ⟨hirr, hmonic, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hp).mp hπ
    exact Polynomial.Splits.of_natDegree_eq_one (h π hmonic hirr hdvd)
  apply hs.of_dvd _ (UniqueFactorizationMonoid.prod_normalizedFactors hp).dvd'
  exact Multiset.prod_ne_zero fun hπ => (prime_of_normalized_factor _ hπ).ne_zero rfl

end SkewCornerDescent
