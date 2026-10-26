/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.SelectedCoordinate
import SkewCornerDescent.Matrix.CornerCofactor
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual complementary component pivots

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:component-elimination`). Retaining
an actual component's first row and last column gives its actual complementary JT minor.
Its inverse is produced from the proved nonzero corner cofactor, including a one-row
component with an empty complementary matrix. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

noncomputable local instance : Algebra ℚ actualField := OreLocalization.instAlgebra

/-- Place one retained endpoint before its complete ordered complement. -/
noncomputable def endpointSplit {n : ℕ} (j : Fin (n + 1)) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => j) j.succAbove
  invFun := fun k => ((finSuccEquiv' j) k).elim (Sum.inl ()) Sum.inr
  left_inv := by
    intro k
    cases k with
    | inl u => cases u; simp
    | inr k => simp
  right_inv := by
    intro k
    refine Fin.succAboveCases j ?_ (fun a => ?_) k
    · simp
    · simp

@[simp]
theorem endpointSplit_inl {n : ℕ} (j : Fin (n + 1)) :
    endpointSplit j (Sum.inl ()) = j := rfl

@[simp]
theorem endpointSplit_inr {n : ℕ} (j : Fin (n + 1)) (k : Fin n) :
    endpointSplit j (Sum.inr k) = j.succAbove k := rfl

/-- The complete component split retains its top row and final column. -/
noncomputable def componentSplit {n : ℕ} (P : Profile n) :
    Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) actualField :=
  splitOriginalMatrix P (endpointSplit 0) (endpointSplit (Fin.last n))

/-- The removed block is precisely the actual top-right deleted minor. -/
theorem componentSplit_removed {n : ℕ} (P : Profile n) :
    (componentSplit P).toBlocks₂₂ = deletedTopRightOriginalMatrix P := by
  ext i j
  simp [componentSplit, splitOriginalMatrix, Matrix.toBlocks₂₂, Matrix.submatrix,
    Fin.succAbove_last, deletedTopRightOriginalMatrix, originalMatrix]

/-- Nonvanishing is supplied by the actual complementary determinant. -/
theorem componentSplit_removed_det_ne_zero {n : ℕ} (P : Profile n) :
    (componentSplit P).toBlocks₂₂.det ≠ 0 := by
  rw [componentSplit_removed, det_deletedTopRightOriginalMatrix]
  simpa using P.minor_ne_zero

/-- A genuine inverse of the actual removed component minor, rather than an assumed bundle. -/
@[instance_reducible]
noncomputable def componentPivotInverse {n : ℕ} (P : Profile n) :
    Invertible (componentSplit P).toBlocks₂₂ :=
  Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (componentSplit_removed_det_ne_zero P))

/-- Exact determinant elimination with the actual component split and its produced inverse.
The row/column permutation sign is kept rather than silently normalized. -/
theorem component_elimination {n : ℕ} (P : Profile n) :
    letI := componentPivotInverse P
    (Equiv.Perm.sign ((endpointSplit (Fin.last n)).symm.trans (endpointSplit 0)) : actualField) *
        originalMap P.schur =
      (componentSplit P).toBlocks₂₂.det *
        (retainedResponse (componentSplit P).toBlocks₁₁ (componentSplit P).toBlocks₁₂
          (componentSplit P).toBlocks₂₁ (componentSplit P).toBlocks₂₂).det := by
  let : Invertible
      (splitOriginalMatrix P (endpointSplit 0) (endpointSplit (Fin.last n))).toBlocks₂₂ :=
    componentPivotInverse P
  exact original_det_eq_removed_mul_response P (endpointSplit 0) (endpointSplit (Fin.last n))

/-- The scalar left after eliminating the actual complementary component minor. -/
noncomputable def componentResponse {n : ℕ} (P : Profile n) : actualField :=
  letI := componentPivotInverse P
  retainedResponse (componentSplit P).toBlocks₁₁ (componentSplit P).toBlocks₁₂
    (componentSplit P).toBlocks₂₁ (componentSplit P).toBlocks₂₂ () ()

set_option backward.isDefEq.respectTransparency false in
/-- The unique top-generator entry remains the retained scalar coordinate. -/
theorem entryDeriv_componentSplit_top {n : ℕ} (P : Profile n) :
    entryDeriv (generatorDeriv P.topVar) (componentSplit P) =
      fun (i j : Unit ⊕ Fin n) =>
        if i = Sum.inl () ∧ j = Sum.inl () then (1 : actualField) else 0 := by
  ext i j
  change entryDeriv (generatorDeriv P.topVar) (originalMatrix P)
    (endpointSplit 0 i) (endpointSplit (Fin.last n) j) = _
  rw [entryDeriv_originalMatrix_top]
  cases i with
  | inl u =>
    cases u
    cases j with
    | inl v => cases v; simp
    | inr j => simp [Fin.succAbove_last]
  | inr i =>
    cases j with
    | inl v => cases v; simp
    | inr j => simp

set_option backward.isDefEq.respectTransparency false in
/-- The complete reduced scalar remains monic in the actual top generator. -/
theorem generatorDeriv_componentResponse_top {n : ℕ} (P : Profile n) :
    generatorDeriv P.topVar (componentResponse P) = 1 := by
  let := componentPivotInverse P
  let D : Derivation ℚ actualField actualField := generatorDeriv P.topVar
  let M := componentSplit P
  have h11 : entryDeriv D M.toBlocks₁₁ = 1 := by
    ext i j
    cases i; cases j
    change entryDeriv D M (Sum.inl ()) (Sum.inl ()) = _
    rw [entryDeriv_componentSplit_top]
    simp
  have h12 : entryDeriv D M.toBlocks₁₂ = 0 := by
    ext i j
    cases i
    change entryDeriv D M (Sum.inl ()) (Sum.inr j) = _
    rw [entryDeriv_componentSplit_top]
    simp
  have h21 : entryDeriv D M.toBlocks₂₁ = 0 := by
    ext i j
    cases j
    change entryDeriv D M (Sum.inr i) (Sum.inl ()) = _
    rw [entryDeriv_componentSplit_top]
    simp
  have h22 : entryDeriv D M.toBlocks₂₂ = 0 := by
    ext i j
    change entryDeriv D M (Sum.inr i) (Sum.inr j) = _
    rw [entryDeriv_componentSplit_top]
    simp
  have h := entryDeriv_retainedResponse D M.toBlocks₁₁ M.toBlocks₁₂
    M.toBlocks₂₁ M.toBlocks₂₂
  rw [h11, h12, h21, h22] at h
  simpa only [Matrix.zero_mul, Matrix.mul_zero, sub_zero, add_zero,
    entryDeriv, componentResponse, Matrix.one_apply, ite_true] using
    congrFun (congrFun h ()) ()

/-- The actual signed top cofactor in the original field. -/
noncomputable def componentCoefficient {n : ℕ} (P : Profile n) : actualField :=
  originalMap ((-1 : Lambda) ^ n *
    cellSchur (diagramInterior P.cells) P.isSkew_cells.interior)

/-- The removed complete minor contains no selected top generator. -/
theorem generatorDeriv_component_removed_top {n : ℕ} (P : Profile n) :
    generatorDeriv P.topVar (componentSplit P).toBlocks₂₂.det = 0 := by
  rw [componentSplit_removed, det_deletedTopRightOriginalMatrix,
    generatorDeriv_originalMap, P.minorDet_eq_interiorSchur]
  have hl : P.topVar ∉
      (cellSchur (diagramInterior P.cells) P.isSkew_cells.interior).vars := by
    rw [← map_integralCellSchur]
    intro h
    exact (lt_irrefl P.topVar)
      ((MvPolynomial.mem_supported.mp P.integralInterior_mem_below)
        (MvPolynomial.vars_map _ _ h))
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hl, map_zero]

/-- The actual component function is its signed cofactor times the fully reduced scalar. -/
theorem component_response_mul_coefficient {n : ℕ} (P : Profile n) :
    originalMap P.schur = componentCoefficient P * componentResponse P := by
  let := componentPivotInverse P
  let σ : actualField :=
    Equiv.Perm.sign ((endpointSplit (Fin.last n)).symm.trans (endpointSplit 0))
  have he : σ * originalMap P.schur =
      (componentSplit P).toBlocks₂₂.det * componentResponse P := by
    simpa only [Matrix.det_unique, componentResponse] using
      component_elimination P
  have hσ : generatorDeriv P.topVar σ = 0 := Derivation.map_intCast _ _
  have htop : generatorDeriv P.topVar (originalMap P.schur) = componentCoefficient P := by
    rw [generatorDeriv_originalMap, P.pderiv_schur_eq_interiorSchur]
    rfl
  have hd := congrArg (generatorDeriv P.topVar) he
  simp only [Derivation.leibniz, smul_eq_mul, hσ, htop,
    generatorDeriv_component_removed_top, generatorDeriv_componentResponse_top,
    mul_zero, add_zero, mul_one] at hd
  have hσ0 : σ ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hd
    exact componentSplit_removed_det_ne_zero P hd.symm
  apply mul_left_cancel₀ hσ0
  rw [← mul_assoc, hd]
  exact he

/-- The retained scalar is exactly `t/a` for the actual connected prime and signed cofactor.
Neither the inverse nor its normal dependence is replaced by a residue approximation. -/
theorem componentResponse_eq_normal_quotient {n : ℕ} (P : Profile n) :
    componentResponse P = originalMap P.schur / componentCoefficient P := by
  have hc : componentCoefficient P ≠ 0 := by
    simp only [componentCoefficient, ne_eq, originalMap_eq_zero]
    apply mul_ne_zero (pow_ne_zero n (by simp))
    rw [← P.minorDet_eq_interiorSchur]
    exact P.minor_ne_zero
  rw [component_response_mul_coefficient, mul_div_cancel_left₀ _ hc]

end SkewCornerDescent.Matrix
