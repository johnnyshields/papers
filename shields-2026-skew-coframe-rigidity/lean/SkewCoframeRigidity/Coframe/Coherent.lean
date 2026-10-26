/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Algebra

/-!
# Coherent and physical normalization

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Diagrams, full flags, and coherent units»
and the identification of coherent homogenizations in `sc:row-degree`, `sc:coequal-data`.

Setting the coherent unit `ϑ` to one maps the coherent Jacobi–Trudi polynomial of a diagram to
its physical one.  Two coherent polynomials that are determinants of `N × N` letter matrices are
equal as soon as their physical specializations are, because the substitution `H_k ↦ ϑ H_k`
multiplies such a determinant by `ϑ^N`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence MvPolynomial
open scoped Matrix

/-- Physical normalization: the coherent unit `ϑ` is replaced by one. -/
noncomputable def physSpec : CohRing →ₐ[ℚ] CohRing :=
  aeval fun k => if k = 0 then 1 else X k

/-- The substitution `H_k ↦ ϑ H_k` for `k > 0`. -/
noncomputable def thetaScale : CohRing →ₐ[ℚ] CohRing :=
  aeval fun k => if k = 0 then X 0 else X 0 * X k

/-- The inclusion of the physical ring into the coherent ring. -/
noncomputable def physInclude : SkewCofactorIndependence.CompleteRing →ₐ[ℚ] CohRing :=
  rename (fun k : ℕ+ => (k : ℕ))

theorem physInclude_injective : Function.Injective physInclude :=
  rename_injective _ PNat.coe_injective

theorem physSpec_letterOf (k : ℤ) :
    physSpec (letterOf (X : ℕ → CohRing) k) = physInclude (complete k) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [letterOf_of_neg _ hk, complete_of_neg hk]
  · simp [letterOf, physSpec]
  · rw [letterOf_of_nonneg _ hk.le, complete_of_pos hk]
    have : k.toNat ≠ 0 := by omega
    have e : physInclude (X (⟨k.toNat, by omega⟩ : ℕ+)) = X k.toNat := rename_X _ _
    rw [e]
    simp only [physSpec, aeval_X, ite_eq_right this]

theorem thetaScale_letterOf (k : ℤ) :
    thetaScale (letterOf (X : ℕ → CohRing) k) = X 0 * physSpec (letterOf X k) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [letterOf_of_neg _ hk]
  · simp [letterOf, thetaScale, physSpec]
  · rw [letterOf_of_nonneg _ hk.le]
    have : k.toNat ≠ 0 := by omega
    simp [thetaScale, physSpec, this]

theorem thetaScale_injective : Function.Injective thetaScale := by
  let ι : CohRing →ₐ[ℚ] CohField := IsScalarTower.toAlgHom ℚ CohRing CohField
  let lam : CohRing →ₐ[ℚ] CohField :=
    aeval fun k => if k = 0 then ι (X 0) else ι (X k) / ι (X 0)
  have hθ : ι (X 0) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 (X_ne_zero 0)
  have h : lam.comp thetaScale = ι := by
    apply algHom_ext
    intro k
    by_cases hk : k = 0
    · simp [lam, thetaScale, hk]
    · have e : thetaScale (X k) = X 0 * X k := by simp [thetaScale, hk]
      rw [AlgHom.comp_apply, e, map_mul]
      simp only [lam, aeval_X, ite_true, hk, ite_false]
      field_simp
  intro a b hab
  apply IsFractionRing.injective CohRing CohField
  have := congrArg lam hab
  simpa [← AlgHom.comp_apply, h, ι] using this

section Matrices

variable {n : ℕ}

theorem letterOf_map {R S : Type*} [Zero R] [Zero S] (f : R → S) (hf : f 0 = 0) (h : ℕ → R)
    (k : ℤ) : letterOf (fun j => f (h j)) k = f (letterOf h k) := by
  unfold letterOf
  split_ifs <;> simp [hf]

theorem thetaScale_det {N : ℕ} (M : Matrix (Fin N) (Fin N) CohRing)
    (hM : ∀ i j, thetaScale (M i j) = X 0 * physSpec (M i j)) :
    thetaScale M.det = X 0 ^ N * physSpec M.det := by
  have h1 := RingHom.map_det (thetaScale : CohRing →+* CohRing) M
  have h2 := RingHom.map_det (physSpec : CohRing →+* CohRing) M
  have e : (thetaScale : CohRing →+* CohRing).mapMatrix M =
      (X 0 : CohRing) • (physSpec : CohRing →+* CohRing).mapMatrix M := by
    refine Matrix.ext fun i j => ?_
    simpa using hM i j
  change thetaScale M.det = _ * physSpec M.det
  rw [show thetaScale M.det = ((thetaScale : CohRing →+* CohRing)) M.det from rfl, h1, e,
    Matrix.det_smul, ← h2]
  simp

theorem thetaScale_fullMatrix (D : BetaDiagram n) (i j : Fin n) :
    thetaScale (fullMatrixOf X D i j) = X 0 * physSpec (fullMatrixOf X D i j) :=
  thetaScale_letterOf _

theorem thetaScale_properMatrix (D : BetaDiagram (n + 1)) (i j : Fin n) :
    thetaScale (properMatrixOf X D i j) = X 0 * physSpec (properMatrixOf X D i j) :=
  thetaScale_letterOf _

theorem physSpec_schurOf (D : BetaDiagram n) :
    physSpec (schurOf (X : ℕ → CohRing) D) = physInclude D.schur := by
  have h1 := RingHom.map_det (physSpec : CohRing →+* CohRing) (fullMatrixOf X D)
  have h2 := RingHom.map_det (physInclude : SkewCofactorIndependence.CompleteRing →+* CohRing)
    D.matrix
  change physSpec (fullMatrixOf X D).det = physInclude D.matrix.det
  rw [show physSpec (fullMatrixOf X D).det =
    ((physSpec : CohRing →+* CohRing)) (fullMatrixOf X D).det from rfl, h1,
    show physInclude D.matrix.det =
    ((physInclude : SkewCofactorIndependence.CompleteRing →+* CohRing)) D.matrix.det from rfl, h2]
  congr 1
  ext i j
  simp [fullMatrixOf, BetaDiagram.matrix, physSpec_letterOf]

theorem physSpec_properDet (D : BetaDiagram (n + 1)) :
    physSpec (properMatrixOf (X : ℕ → CohRing) D).det = physInclude D.cornerPolynomial := by
  have h1 := RingHom.map_det (physSpec : CohRing →+* CohRing) (properMatrixOf X D)
  have h2 := RingHom.map_det (physInclude : SkewCofactorIndependence.CompleteRing →+* CohRing)
    D.cornerBoard
  change physSpec (properMatrixOf X D).det = physInclude D.cornerBoard.det
  rw [show physSpec (properMatrixOf X D).det =
    ((physSpec : CohRing →+* CohRing)) (properMatrixOf X D).det from rfl, h1,
    show physInclude D.cornerBoard.det =
    ((physInclude : SkewCofactorIndependence.CompleteRing →+* CohRing)) D.cornerBoard.det from
      rfl, h2]
  congr 1
  ext i j
  simp [properMatrixOf, BetaDiagram.cornerBoard, betaBoard, physSpec_letterOf]

theorem properDet_ne_zero {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    (properMatrixOf (X : ℕ → CohRing) D).det ≠ 0 := by
  intro h
  have := physSpec_properDet D
  rw [h, map_zero] at this
  exact D.cornerPolynomial_ne_zero hD (physInclude_injective (by simpa using this.symm))

theorem cohSchur_eq_of_schur_eq {D E : BetaDiagram n} (h : D.schur = E.schur) :
    cohSchur D = cohSchur E := by
  apply thetaScale_injective
  have hD := thetaScale_det (fullMatrixOf X D) (thetaScale_fullMatrix D)
  have hE := thetaScale_det (fullMatrixOf X E) (thetaScale_fullMatrix E)
  change thetaScale (schurOf X D) = thetaScale (schurOf X E)
  unfold schurOf
  rw [hD, hE]
  have := physSpec_schurOf D
  have := physSpec_schurOf E
  unfold schurOf at *
  simp_all

theorem properDet_eq_of_corner_eq {D E : BetaDiagram (n + 1)}
    (h : D.cornerCoefficient = E.cornerCoefficient) :
    (properMatrixOf (X : ℕ → CohRing) D).det = (properMatrixOf (X : ℕ → CohRing) E).det := by
  apply thetaScale_injective
  rw [thetaScale_det _ (thetaScale_properMatrix D), thetaScale_det _ (thetaScale_properMatrix E),
    physSpec_properDet, physSpec_properDet]
  have h' : D.cornerPolynomial = E.cornerPolynomial := by
    unfold BetaDiagram.cornerCoefficient at h
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h
  rw [h']

theorem cohCorner_eq_of_corner_eq {D E : BetaDiagram (n + 1)}
    (h : D.cornerCoefficient = E.cornerCoefficient) : cohCorner D = cohCorner E := by
  unfold cohCorner cornerOf
  rw [properDet_eq_of_corner_eq h]

theorem properMatrix_cohLetters (D : BetaDiagram (n + 1)) :
    properMatrixOf cohLetters D =
      (algebraMap CohRing CohField).mapMatrix (properMatrixOf (X : ℕ → CohRing) D) := by
  ext i j
  simp only [properMatrixOf, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact letterOf_map (algebraMap CohRing CohField) (map_zero _) (X : ℕ → CohRing) _

theorem fullMatrix_cohLetters (D : BetaDiagram n) :
    fullMatrixOf cohLetters D =
      (algebraMap CohRing CohField).mapMatrix (fullMatrixOf (X : ℕ → CohRing) D) := by
  ext i j
  simp only [fullMatrixOf, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact letterOf_map (algebraMap CohRing CohField) (map_zero _) (X : ℕ → CohRing) _

theorem properDet_cohLetters_ne_zero {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    (properMatrixOf cohLetters D).det ≠ 0 := by
  rw [properMatrix_cohLetters, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 (properDet_ne_zero hD)

end Matrices

end SkewCoframeRigidity.Coframe
