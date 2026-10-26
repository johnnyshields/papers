/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PlanePolynomialFactors
import SkewCornerDescent.TriangularPlanePolynomial
import Mathlib.Algebra.Polynomial.Splits

/-!
# Full root products of denominator-cleared plane numerators

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Every rational root retains its full
correction `A - α F`; repeated roots retain their multiset multiplicities.

Sorry-free.
-/

namespace SkewCornerDescent

open Polynomial MvPolynomial

variable {k R : Type*} [Field k] [CommRing R] [NoZeroDivisors R] [Algebra k R]

/-- Denominator clearing is multiplicative, including zero and constant factors. -/
theorem clearedPlanePolynomial_mul (p q : Polynomial k) (A F : R) :
    clearedPlanePolynomial (p * q) A F =
      clearedPlanePolynomial p A F * clearedPlanePolynomial q A F := by
  rw [clearedPlanePolynomial, Polynomial.map_mul,
    Polynomial.mul_scaleRoots_of_noZeroDivisors, Polynomial.mul_comp]
  rfl

omit [NoZeroDivisors R] in
/-- A rational constant contributes only its coefficient-ring unit. -/
theorem clearedPlanePolynomial_C (c : k) (A F : R) :
    clearedPlanePolynomial (Polynomial.C c) A F = Polynomial.C (algebraMap k R c) := by
  simp only [clearedPlanePolynomial, Polynomial.map_C, Polynomial.scaleRoots_C,
    Polynomial.C_comp]

omit [NoZeroDivisors R] in
/-- A rational root gives the entire affine response, rather than just its leading term. -/
theorem clearedPlanePolynomial_linear (α : k) (A F : R) :
    clearedPlanePolynomial (Polynomial.X - Polynomial.C α) A F =
      Polynomial.X + Polynomial.C (A - algebraMap k R α * F) := by
  simp only [clearedPlanePolynomial, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.X_sub_C_scaleRoots, Polynomial.sub_comp,
    Polynomial.X_comp, Polynomial.mul_comp, Polynomial.C_comp, map_sub, map_mul]
  ring

/-- Clearing preserves a complete multiset product and all repetitions. -/
theorem clearedPlanePolynomial_multisetProd (s : Multiset (Polynomial k)) (A F : R) :
    clearedPlanePolynomial s.prod A F =
      (s.map (fun p => clearedPlanePolynomial p A F)).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero, Multiset.map_zero, clearedPlanePolynomial,
      Polynomial.map_one, Polynomial.one_scaleRoots, Polynomial.one_comp]
  | cons p s ih =>
    rw [Multiset.prod_cons, clearedPlanePolynomial_mul, Multiset.map_cons,
      Multiset.prod_cons, ih]

/-- A split polynomial yields its exact full affine root factorization after cap clearing. -/
theorem clearedPlanePolynomial_roots (p : Polynomial k) (hp : p.Splits) (A F : R) :
    clearedPlanePolynomial p A F = Polynomial.C (algebraMap k R p.leadingCoeff) *
      (p.roots.map (fun α => Polynomial.X +
        Polynomial.C (A - algebraMap k R α * F))).prod := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [clearedPlanePolynomial_mul, clearedPlanePolynomial_C,
    clearedPlanePolynomial_multisetProd, Multiset.map_map]
  congr 2
  apply Multiset.map_congr rfl
  intro α _
  exact clearedPlanePolynomial_linear α A F

/-- The full root product is an identity in the original higher-coordinate polynomial ring. -/
theorem triangularPlanePolynomial_roots {σ : Type*} (K : σ) (p : Polynomial k)
    (hp : p.Splits) (A F : MvPolynomial σ k) :
    triangularPlanePolynomial K p A F = MvPolynomial.C p.leadingCoeff *
      (p.roots.map (fun α => MvPolynomial.X K +
        (A - MvPolynomial.C α * F))).prod := by
  rw [triangularPlanePolynomial, clearedPlanePolynomial_roots p hp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
    Multiset.map_map]
  congr 2
  apply Multiset.map_congr rfl
  intro α _
  simp only [Function.comp_apply, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rfl

end SkewCornerDescent
