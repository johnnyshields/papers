/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Setup

/-!
# Scale invariance of the complete coframe

The complete coframe `1 + ∑ G_s z^s`, with `G = -T⁻¹ v`, does not change when every letter is
multiplied by the same nonzero scalar.  In particular the coframe for the normalized letters
`H_k / ϑ` is the generic complete coframe.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial

/-- Scaling every letter by `c` scales the proper matrix by `c`. -/
theorem properMatrixOf_scale {L : Type*} [Field L] {n : ℕ} (h : ℕ → L) (c : L)
    (D : BetaDiagram (n + 1)) :
    properMatrixOf (fun k => c * h k) D = c • properMatrixOf h D := by
  ext i j
  simp only [properMatrixOf, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, letterOf]
  split_ifs <;> simp

/-- Scaling every letter by `c` scales the top column by `c`. -/
theorem topVecOf_scale {L : Type*} [Field L] {n : ℕ} (h : ℕ → L) (c : L)
    (D : BetaDiagram (n + 1)) :
    topVecOf (fun k => c * h k) D = c • topVecOf h D := by
  ext i
  simp only [topVecOf, Pi.smul_apply, smul_eq_mul, letterOf]
  split_ifs <;> simp

theorem scale_coframeOf {L : Type*} [Field L] {n : ℕ} (h : ℕ → L) (c : L) (hc : c ≠ 0)
    (D : BetaDiagram (n + 1)) : coframeOf (fun k => c * h k) D = coframeOf h D := by
  have hvec : coframeVecOf (fun k => c * h k) D = coframeVecOf h D := by
    unfold coframeVecOf
    rw [properMatrixOf_scale, topVecOf_scale]
    by_cases hd : IsUnit (properMatrixOf h D).det
    · let _ : Invertible c := invertibleOfNonzero hc
      rw [Matrix.inv_smul (k := c) (h := hd), Matrix.smul_mulVec, Matrix.mulVec_smul]
      ext j
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, invOf_eq_inv]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · have hd' : ¬ IsUnit ((c • properMatrixOf h D).det) := by
        rw [Matrix.det_smul]
        intro hu
        exact hd (isUnit_of_mul_isUnit_right hu)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hd, Matrix.nonsing_inv_apply_not_isUnit _ hd']
      simp
  unfold coframeOf
  rw [hvec]

theorem normLetters_eq (k : ℕ) : normLetters k = (cohLetters 0)⁻¹ * cohLetters k := by
  unfold normLetters
  rw [div_eq_inv_mul]

theorem cohLetters_zero_ne_zero : cohLetters 0 ≠ 0 := by
  unfold cohLetters
  refine (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 ?_
  exact MvPolynomial.X_ne_zero 0

theorem coframeOf_normLetters {n : ℕ} (D : BetaDiagram (n + 1)) :
    coframeOf normLetters D = coframe D := by
  have : normLetters = fun k => (cohLetters 0)⁻¹ * cohLetters k := funext normLetters_eq
  rw [this]
  exact scale_coframeOf cohLetters _ (inv_ne_zero cohLetters_zero_ne_zero) D

end SkewCoframeRigidity.UnitCase
