/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalExposedPolynomials
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Nonvanishing of unchanged original monic responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
The protected top derivative of the normalized numerator is the nonzero square of the
original denominator. No coordinate chamber or independent response coordinates are needed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial SelectedCoordinate

/-- Strict triangular support produces nonvanishing in the original fraction field. -/
theorem originalMonicResponse_ne_zero {α : Type*}
    (N : ℕ+) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N) (hNtop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hq0 : ∀ a, q a ≠ 0) (a : α) :
    residueGenerator N ⟨top a, htop a⟩ +
      algebraMap (OtherPolynomial N) (OtherField N) (p a) /
        algebraMap (OtherPolynomial N) (OtherField N) (q a) ≠ 0 := by
  classical
  let P := realResiduePolynomial N (p a)
  let Q := realResiduePolynomial N (q a)
  have hP : (top a : ℕ) ∉ P.vars := by
    intro hj
    exact (lt_irrefl _) (hp a _ hj)
  have hQ : (top a : ℕ) ∉ Q.vars := by
    intro hj
    exact (not_lt_of_ge (hNtop a)) (hq a _ hj)
  have hdP : pderiv (top a : ℕ) P = 0 := pderiv_eq_zero_of_notMem_vars hP
  have hdQ : pderiv (top a : ℕ) Q = 0 := pderiv_eq_zero_of_notMem_vars hQ
  have hnum : originalExposedNumerator N top p q htop a ≠ 0 := by
    intro hz
    have hreal := congrArg (realResiduePolynomial N) hz
    rw [real_originalExposedNumerator, map_zero] at hreal
    have hder := congrArg (pderiv (top a : ℕ)) hreal
    change pderiv (top a : ℕ) ((X (top a : ℕ) * Q + P) * Q) = 0 at hder
    have hsquare : Q * Q = 0 := by
      simpa only [pderiv_mul, map_add, pderiv_X_self, hdP, hdQ, mul_zero, zero_mul,
        one_mul, add_zero] using hder
    exact mul_ne_zero (realResiduePolynomial_ne_zero N (hq0 a))
      (realResiduePolynomial_ne_zero N (hq0 a)) hsquare
  rw [← originalExposedNumerator_fraction N top p q htop a (hq0 a)]
  exact div_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hnum)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (pow_ne_zero _ (hq0 a)))

end SkewCornerDescent.Matrix
