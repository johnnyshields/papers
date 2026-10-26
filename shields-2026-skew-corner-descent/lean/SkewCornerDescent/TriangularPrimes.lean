/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic

/-!
# Prime classes of monic triangular response polynomials

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`).

A monic protected coordinate plus a polynomial in strictly lower coordinates is prime.
Two such responses are associates exactly when their protected tops and full lower
corrections agree. The coefficient field is arbitrary; no independent-response
assumption or equality of literal component representatives is used.

Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

variable {σ k : Type*} [LinearOrder σ] [Field k]

/-- A strictly lower polynomial correction cannot contain its own protected top. -/
theorem triangular_correction_notMem {a : MvPolynomial σ k} {K : σ}
    (ha : ∀ i ∈ a.vars, i < K) : K ∉ a.vars :=
  fun h => (lt_irrefl K) (ha K h)

/-- The protected-top derivative of a monic triangular response is exactly one. -/
theorem triangular_pderiv_top {a : MvPolynomial σ k} {K : σ}
    (ha : ∀ i ∈ a.vars, i < K) : pderiv K (X K + a) = 1 := by
  rw [map_add, pderiv_X_self, pderiv_eq_zero_of_notMem_vars
    (triangular_correction_notMem ha), add_zero]

/-- A triangular response has no dependence on a coordinate above its protected top. -/
theorem triangular_pderiv_above {a : MvPolynomial σ k} {K J : σ}
    (ha : ∀ i ∈ a.vars, i < K) (hKJ : K < J) : pderiv J (X K + a) = 0 := by
  have hj : J ∉ a.vars := fun h => (not_lt_of_ge hKJ.le) (ha J h)
  rw [map_add, pderiv_X_of_ne hKJ.ne, pderiv_eq_zero_of_notMem_vars hj, add_zero]

/-- A monic triangular response is prime in the polynomial algebra over its coefficient field. -/
theorem monicTriangularPolynomial_prime {a : MvPolynomial σ k} {K : σ}
    (ha : ∀ i ∈ a.vars, i < K) : Prime (X K + a) := by
  apply irreducible_iff_prime.mp
  simpa only [one_mul] using MvPolynomial.irreducible_mul_X_add
    (1 : MvPolynomial σ k) a K one_ne_zero (by
      simp only [vars_one, Finset.notMem_empty, not_false_eq_true])
    (triangular_correction_notMem ha) isRelPrime_one_left

/-- Monic associates are equal as full response polynomials, with equal protected tops. -/
theorem monicTriangularPolynomial_associated_iff {a b : MvPolynomial σ k} {K J : σ}
    (ha : ∀ i ∈ a.vars, i < K) (hb : ∀ i ∈ b.vars, i < J) :
    Associated (X K + a) (X J + b) ↔ K = J ∧ a = b := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨r, hr, hur⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
    rw [hur] at hu
    have hd (i : σ) : C r * pderiv i (X K + a) = pderiv i (X J + b) := by
      have h := congrArg (pderiv i) hu
      rw [mul_comm (X K + a) (C r), pderiv_C_mul] at h
      exact h
    have hKJ : K = J := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hd J
        rw [triangular_pderiv_above ha hlt, triangular_pderiv_top hb, mul_zero] at h
        exact zero_ne_one h
      · have h := hd K
        rw [triangular_pderiv_top ha, triangular_pderiv_above hb hgt, mul_one] at h
        have hr0 : r = 0 := by
          have hc := congrArg constantCoeff h
          simpa only [constantCoeff_C, map_zero] using hc
        exact (isUnit_iff_ne_zero.mp hr) hr0
    subst J
    have h := hd K
    rw [triangular_pderiv_top ha, triangular_pderiv_top hb, mul_one] at h
    have hr1 : r = 1 := by
      have hc := congrArg constantCoeff h
      simpa only [constantCoeff_C, map_one] using hc
    rw [hr1, C_1, mul_one] at hu
    exact ⟨rfl, add_left_cancel hu⟩
  · rintro ⟨rfl, rfl⟩
    exact Associated.refl _

end SkewCornerDescent
