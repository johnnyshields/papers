/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.ComponentOrders
import SkewCornerDescent.Matrix.OriginalUpperResponses

/-!
# Polynomial support of full matrix denominators

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Determinants retain the largest generator
bound of their entries, including empty matrices. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Finite addition cannot introduce a generator above the bounds on its summands. -/
theorem polynomialSpan_sum_le {ι : Type*} (s : Finset ι) (f : ι → Lambda) (N : ℕ)
    (hf : ∀ i ∈ s, polynomialSpan (f i) ≤ N) : polynomialSpan (∑ i ∈ s, f i) ≤ N := by
  classical
  apply Finset.sup_le
  intro k hk
  obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hk)
  exact (Finset.le_sup hki).trans (hf i hi)

/-- A full determinant has no generator above any of its actual entries. -/
theorem polynomialSpan_det_le {ν : Type*} [Fintype ν] [DecidableEq ν]
    (M : Matrix ν ν Lambda) (N : ℕ) (hM : ∀ i j, polynomialSpan (M i j) ≤ N) :
    polynomialSpan M.det ≤ N := by
  classical
  rw [Matrix.det_apply']
  apply polynomialSpan_sum_le
  intro σ _
  apply (polynomialSpan_mul_le _ _).trans
  apply max_le
  · change polynomialSpan (MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℚ)) ≤ N
    rw [polynomialSpan_C]
    exact Nat.zero_le _
  · exact polynomialSpan_prod_le _ _ _ fun i _ => hM (σ i) i

/-- A complete-homogeneous entry uses exactly its positive index, or no generator. -/
theorem polynomialSpan_hh_le (z : ℤ) (N : ℕ) (hz : z ≤ (N : ℤ)) :
    polynomialSpan (hh z) ≤ N := by
  by_cases hn : z < 0
  · rw [hh_of_neg hn]
    simp only [polynomialSpan, MvPolynomial.vars_0, Finset.sup_empty, bot_le]
  by_cases h0 : z = 0
  · rw [h0, hh_zero]
    change polynomialSpan (MvPolynomial.C 1) ≤ N
    rw [polynomialSpan_C]
    exact Nat.zero_le _
  let k : ℕ+ := ⟨z.toNat, by omega⟩
  have hk : (k : ℤ) = z := Int.toNat_of_nonneg (by omega)
  rw [← hk, hh_pnat]
  simp only [polynomialSpan, MvPolynomial.vars_X, Finset.sup_singleton]
  change z.toNat ≤ N
  omega

end SkewCornerDescent.Matrix
