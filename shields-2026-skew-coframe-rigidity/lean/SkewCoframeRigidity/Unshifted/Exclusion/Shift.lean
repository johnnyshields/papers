/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.CoequalData
import SkewCoframeRigidity.Unshifted.YExpansion
import SkewCoframeRigidity.Unshifted.Endpoints

/-!
# Naturality of the coframe and the shift of one letter

Formalizes the passage from the generic letters to the polynomial dependence on the top letter
`y = H_m` in `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`).  The coframe, the clipped operator and the letter series commute with
a ring homomorphism of fields.  The shift `H_m ↦ H_m + s` is a field endomorphism of the raw
field, so the unshifted identity holds at the shifted letters for every `s`; an identity that is
a polynomial of degree two in `y` with coefficients independent of `y` therefore has vanishing
coefficients.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

section Hom

variable {K K' : Type*} [Field K] [Field K'] (f : K →+* K') {n : ℕ}

theorem letterOf_map (h : ℕ → K) (k : ℤ) : letterOf (fun j => f (h j)) k = f (letterOf h k) := by
  unfold letterOf; split_ifs <;> simp

theorem properMatrixOf_map (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    properMatrixOf (fun j => f (h j)) D = (properMatrixOf h D).map f := by
  ext i j; simp [properMatrixOf, letterOf_map]

theorem topVecOf_map (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    topVecOf (fun j => f (h j)) D = fun i => f (topVecOf h D i) := by
  funext i; simp [topVecOf, letterOf_map]

theorem matrix_inv_map (A : Matrix (Fin n) (Fin n) K) : (A.map f)⁻¹ = (A⁻¹).map f := by
  have h1 : f.mapMatrix A = A.map f := rfl
  have h2 := f.map_adjugate A
  have h3 := f.map_det A
  rw [h1] at h2 h3
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv', ← h3]
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀]
  rw [← this]
  rfl

theorem coframeVecOf_map (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    coframeVecOf (fun j => f (h j)) D = fun j => f (coframeVecOf h D j) := by
  funext j
  unfold coframeVecOf
  rw [properMatrixOf_map, topVecOf_map, matrix_inv_map]
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem coframeOf_map (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    coframeOf (fun j => f (h j)) D = (coframeOf h D).map f := by
  unfold coframeOf
  rw [coframeVecOf_map]
  simp [Polynomial.map_sum]

theorem clippedOp_map (M : ℕ) (G C : K[X]) (u : PowerSeries K) :
    (clippedOp M G C u).map f =
      clippedOp M (G.map f) (C.map f) (PowerSeries.map f u) := by
  have key : ∀ F : K[X], (PowerSeries.trunc M (u * (F : PowerSeries K))).map f =
      PowerSeries.trunc M (PowerSeries.map f u * ((F.map f : K'[X]) : PowerSeries K')) := by
    intro F
    ext i
    simp [PowerSeries.coeff_trunc, Polynomial.coeff_map, PowerSeries.coeff_mul]
    split_ifs <;> simp [map_sum]
  unfold clippedOp
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, key, key]

end Hom

/-! ### The shift of the letter `H_m` -/

section Shift

/-- The substitution `H_m ↦ H_m + s` in the coherent ring. -/
noncomputable def shiftRing (m : ℕ) (s : ℤ) : CohRing →ₐ[ℚ] CohRing :=
  MvPolynomial.aeval fun k => if k = m then MvPolynomial.X k + (s : CohRing) else MvPolynomial.X k

theorem shiftRing_comp (m : ℕ) (s t : ℤ) :
    (shiftRing m s).comp (shiftRing m t) = shiftRing m (s + t) := by
  apply MvPolynomial.algHom_ext
  intro k
  by_cases hk : k = m
  · subst hk; simp [shiftRing]; ring
  · simp [shiftRing, hk]

theorem shiftRing_zero (m : ℕ) : shiftRing m 0 = AlgHom.id ℚ _ := by
  apply MvPolynomial.algHom_ext
  intro k
  by_cases hk : k = m <;> simp [shiftRing, hk]

theorem shiftRing_injective (m : ℕ) (s : ℤ) : Function.Injective (shiftRing m s) := by
  intro a b hab
  have h := shiftRing_comp m (-s) s
  rw [neg_add_cancel, shiftRing_zero] at h
  have := congrArg (fun x => (shiftRing m (-s)) x) hab
  simpa [← AlgHom.comp_apply, h] using this

/-- The field endomorphism `H_m ↦ H_m + s` of the raw field. -/
noncomputable def shiftField (m : ℕ) (s : ℤ) : CohField →+* CohField :=
  IsFractionRing.lift (A := CohRing) (K := CohField) (g := (algebraMap CohRing CohField).comp
    (shiftRing m s : CohRing →+* CohRing))
    ((IsFractionRing.injective CohRing CohField).comp (shiftRing_injective m s))

theorem shiftField_cohLetters (m : ℕ) (s : ℤ) (k : ℕ) :
    shiftField m s (cohLetters k) = Function.update cohLetters m (cohLetters m + s) k := by
  unfold shiftField cohLetters
  rw [IsFractionRing.lift_algebraMap]
  by_cases hk : k = m
  · subst hk; simp [shiftRing]
  · simp [shiftRing, hk]

end Shift

end SkewCoframeRigidity.Unshifted
