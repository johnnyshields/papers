/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularPrimes
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Protected tops of triangular divisors

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). A nonzero polynomial cannot have a monic
triangular divisor whose protected top is absent from its variables.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

variable {σ k : Type*} [LinearOrder σ] [Field k]

/-- The protected generator has degree exactly one, independently of the lower correction. -/
theorem monicTriangularPolynomial_degree_top {K : σ} {a : MvPolynomial σ k}
    (ha : ∀ i ∈ a.vars, i < K) : (X K + a).degreeOf K = 1 := by
  have hzero : a.degreeOf K = 0 :=
    not_not.mp (mt mem_vars_iff_degreeOf_ne_zero.mpr (triangular_correction_notMem ha))
  rw [degreeOf_add_eq_of_degreeOf_lt (by rw [hzero, degreeOf_X_self]; exact zero_lt_one),
    degreeOf_X_self]

/-- Divisibility forces the literal protected top to occur in the dividend. -/
theorem monicTriangularPolynomial_dvd_top_mem {K : σ} {a p : MvPolynomial σ k}
    (ha : ∀ i ∈ a.vars, i < K) (hp : p ≠ 0) (hd : X K + a ∣ p) : K ∈ p.vars := by
  obtain ⟨q, hq⟩ := hd
  have hq0 : q ≠ 0 := by intro h; exact hp (by rw [hq, h, mul_zero])
  have hdeg := degreeOf_mul_eq (n := K) (monicTriangularPolynomial_prime ha).ne_zero hq0
  rw [← hq, monicTriangularPolynomial_degree_top ha] at hdeg
  apply mem_vars_iff_degreeOf_ne_zero.mpr
  omega

/-- The protected top of a response divisor cannot exceed the dividend's generator bound. -/
theorem monicTriangularPolynomial_dvd_top_le {K J : σ} {a p : MvPolynomial σ k}
    (ha : ∀ i ∈ a.vars, i < K) (hp : p ≠ 0)
    (hvars : ∀ i ∈ p.vars, i ≤ J) (hd : X K + a ∣ p) : K ≤ J :=
  hvars K (monicTriangularPolynomial_dvd_top_mem ha hp hd)

/-- A monic polynomial in its largest generator has no lower-top response divisor.
Both inequalities are proved: generator support excludes larger tops, and monicity
excludes a nonunit coefficient-ring divisor at a smaller top. -/
theorem monicTriangularPolynomial_dvd_top_eq {K J : σ} {a p : MvPolynomial σ k}
    (ha : ∀ i ∈ a.vars, i < J) (hvars : ∀ i ∈ p.vars, i ≤ K)
    (hm : (optionEquivLeft k {i // i ≠ K}
      (rename (Equiv.optionSubtypeNe K).symm p)).Monic)
    (hd : X J + a ∣ p) : J = K := by
  classical
  let e : MvPolynomial σ k ≃ₐ[k] Polynomial (MvPolynomial {i // i ≠ K} k) :=
    (renameEquiv k (Equiv.optionSubtypeNe K).symm).trans (optionEquivLeft k _)
  have hp : p ≠ 0 := by
    intro h
    exact hm.ne_zero (by change e p = 0; rw [h, map_zero])
  have hle := monicTriangularPolynomial_dvd_top_le ha hp hvars hd
  apply le_antisymm hle
  by_contra hnot
  have hlt : J < K := lt_of_not_ge hnot
  have hdegree : (X J + a).degreeOf K = 0 := by
    have hmiss : K ∉ (X J + a).vars := by
      intro hK
      rcases Finset.mem_union.mp (vars_add_subset (X J) a hK) with hK | hK
      · rw [vars_X, Finset.mem_singleton] at hK
        exact (ne_of_gt hlt) hK
      · exact (not_lt_of_ge hle) (ha K hK)
    exact not_not.mp (mt mem_vars_iff_degreeOf_ne_zero.mpr hmiss)
  have hunit : ¬ IsUnit (e (X J + a)) := by
    intro h
    apply (monicTriangularPolynomial_prime ha).not_isUnit
    have h' := h.map e.symm.toMonoidHom
    change IsUnit (e.symm (e (X J + a))) at h'
    simpa only [AlgEquiv.symm_apply_apply] using h'
  have hpos := Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hm hunit
    (map_dvd e hd)
  change 0 < (optionEquivLeft k {i // i ≠ K}
    (rename (Equiv.optionSubtypeNe K).symm (X J + a))).natDegree at hpos
  rw [← degreeOf_eq_natDegree, hdegree] at hpos
  exact (lt_irrefl 0) hpos

end SkewCornerDescent
