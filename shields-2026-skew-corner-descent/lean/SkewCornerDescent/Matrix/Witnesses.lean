/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalDerivation

/-!
# Original-matrix and derivation witnesses

Supports local algebraic steps in `shields-2026-skew-corner-descent.tex`, «Equal windows and
the determinant defect» (`sec:normal-chart`) and «From response functions to literal copies»
(`sec:one-active`).

Concrete witnesses for the matrix-calculus part of `lem:actual-elimination` and
`lem:profile-derivative`: a nonrow original unit with a nonconstant inverse, a literal `h_0`
midpoint pivot, and a genuine fixed-normal coordinate with a nonconstant lower correction.
These witness the primitive contracts, not the still-unconstructed full-window root hypotheses.
Sorry-free.
-/

open scoped Matrix

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The original nonrow hook determinant is nonzero in the canonical rational field. -/
theorem hook_original_det_ne_zero : (originalMatrix hookProfile).det ≠ 0 := by
  rw [det_originalMatrix, ne_eq, originalMap_eq_zero]
  intro h
  have he := congrArg
    (MvPolynomial.eval (fun j : ℕ+ => if j = 3 then (0 : ℚ) else 1)) h
  norm_num [schur_hook] at he

/-- The same nonrow determinant is an original unit, not a substituted row factor. -/
theorem hook_original_det_isUnit : IsUnit (originalMatrix hookProfile).det :=
  isUnit_iff_ne_zero.mpr hook_original_det_ne_zero

/-- The first original generator differentiates the nonrow hook by its second generator. -/
theorem generatorDeriv_hook :
    generatorDeriv 1 (originalMap hookProfile.schur) = originalMap (hh 2) := by
  rw [schur_hook]
  simp only [map_sub, map_mul, Derivation.leibniz, smul_eq_mul]
  norm_num [generatorDeriv_hh, hh, hPos]

/-- The full inverse of the original nonrow unit has a nonzero derivative. -/
theorem generatorDeriv_hook_inverse_ne_zero :
    generatorDeriv 1 ((originalMap hookProfile.schur)⁻¹) ≠ 0 := by
  rw [Derivation.leibniz_inv, generatorDeriv_hook]
  have hh2 : originalMap (hh 2) ≠ 0 := by
    rw [ne_eq, originalMap_eq_zero]
    norm_num [hh, hPos]
  have hs : originalMap hookProfile.schur ≠ 0 := by
    simpa only [det_originalMatrix] using hook_original_det_ne_zero
  simpa [smul_eq_mul, hs] using hh2

/-- An empty original vertex is precisely an `h_0=1` pivot. -/
theorem h0_pivot_matrix :
    intervalMatrix (ν := Unit) (fun _ => 0) (fun _ => 0) = 1 := by
  ext i k
  simp [intervalMatrix]

@[instance_reducible]
private noncomputable def h0PivotInvertible :
    Invertible (intervalMatrix (ν := Unit) (fun _ => 0) (fun _ => 0)) := by
  rw [h0_pivot_matrix]
  exact invertibleOne

set_option backward.isDefEq.respectTransparency false in
/-- Retaining the true midpoint vertex changes the response by its full quadratic term. -/
theorem h0_midpoint_response :
    let _ := h0PivotInvertible
    intervalResponse 6 (-6) (ν := Unit) (fun _ => 0) (fun _ => 0) =
      originalMap (hh 12) - originalMap (hh 6) ^ 2 := by
  let _ := h0PivotInvertible
  simp [intervalResponse, retainedResponse, h0_pivot_matrix, intervalIncoming,
    intervalOutgoing, Matrix.mul_apply, sq]

set_option backward.isDefEq.respectTransparency false in
/-- The original `h_6` derivative detects the midpoint, invisible in lower profile degrees. -/
theorem h0_midpoint_derivative :
    let _ := h0PivotInvertible
    generatorDeriv 6 (intervalResponse 6 (-6) (ν := Unit) (fun _ => 0) (fun _ => 0)) =
      -2 * originalMap (hh 6) := by
  dsimp only
  let _ := h0PivotInvertible
  rw [h0_midpoint_response]
  simp only [map_sub, Derivation.leibniz_pow, generatorDeriv_hh]
  norm_num [smul_eq_mul]

/-- A nonconstant lower correction has a genuinely fixed-normal lower derivative. -/
theorem fixed_normal_coordinate_witness :
    let a : Lambda := hh 1
    let c : Lambda := hh 2
    normalDeriv 3 a (originalMap (affineCoordinate 3 a c)) = 1 ∧
      fixedNormalDeriv 3 1 a c (originalMap (affineCoordinate 3 a c)) = 0 := by
  dsimp
  have h1 : (hh 1 : Lambda) ≠ 0 := by norm_num [hh, hPos]
  have ha : (3 : ℕ+) ∉ (hh 1).vars := by
    rw [show hh 1 = (MvPolynomial.X (1 : ℕ+) : Lambda) from hh_pnat 1]
    simp
  have hc : (3 : ℕ+) ∉ (hh 2).vars := by
    rw [show hh 2 = (MvPolynomial.X (2 : ℕ+) : Lambda) from hh_pnat 2]
    simp
  exact ⟨normalDeriv_affineCoordinate 3 _ _ h1 ha hc,
    fixedNormalDeriv_affineCoordinate 3 1 _ _ h1 ha hc⟩

/-- Equal-span, equal-function nonrow profiles still have distinct literal row lists. -/
theorem tied_nonrow_profiles_not_literal :
    hookProfile.xi 0 - hookProfile.zeta 1 = 3 ∧
      hookRotatedProfile.xi 0 - hookRotatedProfile.zeta 1 = 3 ∧
      (originalMatrix hookProfile).det = (originalMatrix hookRotatedProfile).det ∧
      hookProfile.r ≠ hookRotatedProfile.r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Profile.xi, Profile.zeta, hookProfile, Fin.sum_univ_succ]
  · norm_num [Profile.xi, Profile.zeta, hookRotatedProfile, Fin.sum_univ_succ]
  · rw [det_originalMatrix, det_originalMatrix, schur_hook, schur_hookRotated]
  · intro h
    have := congrFun h 0
    norm_num [hookProfile, hookRotatedProfile] at this

/-- Integer endpoint differences cannot be truncated before nonnegativity is proved. -/
theorem negative_endpoint_profile_not_ordinary :
    endpointProfile (ν := Unit) (K := ℚ) (fun _ => -1) (fun _ => 1) ≠
      (ordinaryEndpointProfile (ν := Unit) (K := ℚ) (fun _ => 0) (fun _ => 1)).toLaurent := by
  intro h
  have he := congrArg (fun p : LaurentPolynomial ℚ => p.coeff (-1)) h
  have hc : (1 : LaurentPolynomial ℚ).coeff (-1) = 0 := by
    change Finsupp.single (0 : ℤ) (1 : ℚ) (-1) = 0
    simp
  norm_num [endpointProfile, ordinaryEndpointProfile, hc,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at he

/-- With a zero affine slope the claimed normal-coordinate value one is false. -/
theorem zero_slope_normal_coordinate (N : ℕ+) (c : Lambda) :
    normalDeriv N 0 (originalMap (affineCoordinate N 0 c)) = 0 := by
  simp [normalDeriv]

end SkewCornerDescent.Matrix
