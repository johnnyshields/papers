/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Subfield support at polynomial and Laurent offsets

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete profile products retain coefficient-field support at every integer
offset. Negative exponents remain zero. Sorry-free.
-/

namespace SkewCornerDescent

/-- Lower-field support survives complete endpoint-profile multiplication. -/
theorem polynomial_product_coeff_mem_subfield {F : Type*} [Field F]
    (S : Subfield F) (p q : Polynomial F) (hp : ∀ k, p.coeff k ∈ S)
    (hq : ∀ k, q.coeff k ∈ S) (k : ℕ) : (p * q).coeff k ∈ S := by
  classical
  rw [Polynomial.coeff_mul]
  apply S.sum_mem
  intro a _
  exact S.mul_mem (hp a.1) (hq a.2)

/-- Extending a polynomial to integer exponents does not introduce generators;
negative offsets are genuinely zero rather than the constant coefficient. -/
theorem polynomial_laurent_coeff_mem_subfield {F : Type*} [Field F]
    (S : Subfield F) (p : Polynomial F) (hp : ∀ k, p.coeff k ∈ S) (k : ℤ) :
    p.toLaurent.coeff k ∈ S := by
  rcases k with k | k
  · change (Finsupp.mapDomain (fun z : ℕ => (z : ℤ)) p.toFinsupp.coeff) (k : ℤ) ∈ S
    rw [Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k]
    exact hp k
  · have hn : Int.negSucc k ∉ p.toLaurent.coeff.support := by
      rw [LaurentPolynomial.support_coeff_toLaurent]
      simp only [Finset.mem_map, Nat.castEmbedding_apply, not_exists, not_and]
      intro a _ ha
      omega
    rw [Finsupp.notMem_support_iff.mp hn]
    exact S.zero_mem

end SkewCornerDescent
