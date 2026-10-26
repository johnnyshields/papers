/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalResponseField

/-!
# Original component field matrices

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). The full actual component source and its
proper selected minor are exactly their canonical profile matrices in the original field.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The complete component interval in its original source coordinates. -/
noncomputable def originalBlockFieldMatrix {n : ℕ} (P : Profile n) (i : Fin n) :
    Matrix (Fin (interiorBlockLength P i + 1)) (Fin (interiorBlockLength P i + 1)) actualField :=
  (jtMatrix (fun j => P.xi (interiorSliceIndex (interiorBlockFirst P i).val
    (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).succ)
    (fun j => P.zeta (interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).castSucc)).map originalMap

/-- Translation normalization identifies every entry of the complete original block. -/
theorem originalBlockFieldMatrix_eq_profile {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    originalBlockFieldMatrix P i = originalMatrix (interiorBlockProfile P i hi) := by
  unfold originalBlockFieldMatrix
  rw [interiorSliceProfile_matrix P _ _ _ (interiorBlock_slice_same P i)
    (interiorBlock_first_nonempty P i hi)]
  rfl

/-- Position zero of a full original interval is its actual first source index. -/
theorem originalBlockInterval_first {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorSliceIndex (interiorBlockFirst P i).val (interiorBlockLength P i)
      (interiorBlock_interval_bound P i) 0 = interiorBlockFirst P i := by
  apply Fin.ext
  simp only [interiorSliceIndex, Fin.val_zero, add_zero]

/-- The last position of a full original interval is its actual last source index. -/
theorem originalBlockInterval_last {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorSliceIndex (interiorBlockFirst P i).val (interiorBlockLength P i)
      (interiorBlock_interval_bound P i) (Fin.last _) = interiorBlockLast P i := by
  apply Fin.ext
  have hb := Fin.le_def.mp (interiorBlockFirst_le_last P i)
  change (interiorBlockFirst P i).val + interiorBlockLength P i = (interiorBlockLast P i).val
  unfold interiorBlockLength
  omega

/-- The canonical component response uses its complete original proper minor contraction. -/
theorem componentResponse_eq_inverseContraction {n : ℕ} (P : Profile n) :
    componentResponse P = originalMatrix P 0 (Fin.last n) -
      inverseContraction (fun j => originalMatrix P 0 j.castSucc)
        (fun j => originalMatrix P j.succ (Fin.last n)) (deletedTopRightOriginalMatrix P) := by
  let := componentPivotInverse P
  unfold componentResponse retainedResponse inverseContraction
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm, componentSplit_removed]
  simp only [componentSplit, splitOriginalMatrix, Matrix.submatrix_apply,
    endpointSplit_inl, endpointSplit_inr, Fin.succAbove_zero, Fin.succAbove_last]

namespace SelectedCoordinate

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Actual selection gives the exact remaining cardinality, without an independent size binder. -/
theorem originalSelectedRemovedSize {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalRemovedSize (hD := hD) P b.val = interiorBlockLength P b.val.val := by
  simp only [originalRemovedSize, ite_eq_left b.property]

/-- The full remaining matrix is the canonical original-field proper minor. -/
theorem originalRemovedDiagonal_selected_field {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    Matrix.reindex (finCongr (originalSelectedRemovedSize P b))
      (finCongr (originalSelectedRemovedSize P b))
      ((originalRemovedDiagonal (hD := hD) P b.val).map originalMap) =
      deletedTopRightOriginalMatrix (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)) := by
  have he := originalRemovedDiagonal_selected (hD := hD) P b.val b.property
  rw [originalSelectedMinor_eq_profile P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)] at he
  have hm := congrArg (fun M => M.map originalMap) he
  exact hm

/-- Reindexing the selected remaining rows gives their literal successor positions. -/
theorem originalSelectedRowPosition {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : Fin (interiorBlockLength P b.val.val)) :
    originalRemovedRowPosition (hD := hD) P b.val
      ((finCongr (originalSelectedRemovedSize P b)).symm j) = j.succ := by
  apply Fin.ext
  rw [originalRemovedRowPosition_val, ite_eq_left b.property]
  rfl

/-- Reindexing the selected remaining columns gives their literal cast-successor positions. -/
theorem originalSelectedColPosition {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : Fin (interiorBlockLength P b.val.val)) :
    originalRemovedColPosition (hD := hD) P b.val
      ((finCongr (originalSelectedRemovedSize P b)).symm j) = j.castSucc := by
  apply Fin.ext
  rfl

/-- The actual retained same-component entry is the canonical profile's top corner entry. -/
theorem originalSelectedCorner_field {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalMap ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inl (some b))) =
      originalMatrix (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)) 0 (Fin.last _) := by
  have he := congrFun (congrFun (originalBlockFieldMatrix_eq_profile P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)) 0) (Fin.last _)
  change originalMap (hh (P.xi (interiorSliceIndex _ _ _ 0).succ -
    P.zeta (interiorSliceIndex _ _ _ (Fin.last _)).castSucc)) = _ at he
  have hf := (originalBlockInterval_first P b.val.val).trans b.val.property
  rw [hf, originalBlockInterval_last] at he
  change originalMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))))) = _
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  exact he

/-- The actual incoming endpoint vector identifies entrywise with the full canonical component. -/
theorem originalSelectedIncoming_field {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : Fin (interiorBlockLength P b.val.val)) :
    originalMap ((originalSplitMatrix (hD := hD) P) (.inl (some b))
      (.inr ⟨b.val, (finCongr (originalSelectedRemovedSize P b)).symm j⟩)) =
      originalMatrix (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)) 0 j.castSucc := by
  have he := congrFun (congrFun (originalBlockFieldMatrix_eq_profile P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)) 0) j.castSucc
  change originalMap (hh (P.xi (interiorSliceIndex _ _ _ 0).succ -
    P.zeta (interiorSliceIndex _ _ _ j.castSucc).castSucc)) = _ at he
  have hf := (originalBlockInterval_first P b.val.val).trans b.val.property
  rw [hf] at he
  change originalMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
    P.zeta (originalColSplitEquiv (hD := hD) P
      (.inr ⟨b.val, (finCongr (originalSelectedRemovedSize P b)).symm j⟩)))) = _
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_removed]
  unfold originalRemovedCol
  rw [originalSelectedColPosition]
  exact he

/-- The actual outgoing endpoint vector identifies entrywise with the full canonical component. -/
theorem originalSelectedOutgoing_field {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : Fin (interiorBlockLength P b.val.val)) :
    originalMap ((originalSplitMatrix (hD := hD) P)
      (.inr ⟨b.val, (finCongr (originalSelectedRemovedSize P b)).symm j⟩) (.inl (some b))) =
      originalMatrix (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)) j.succ (Fin.last _) := by
  have he := congrFun (congrFun (originalBlockFieldMatrix_eq_profile P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)) j.succ) (Fin.last _)
  change originalMap (hh (P.xi (interiorSliceIndex _ _ _ j.succ).succ -
    P.zeta (interiorSliceIndex _ _ _ (Fin.last _)).castSucc)) = _ at he
  rw [originalBlockInterval_last] at he
  change originalMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P
    (.inr ⟨b.val, (finCongr (originalSelectedRemovedSize P b)).symm j⟩)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))))) = _
  rw [originalRowSplitEquiv_removed, originalColSplitEquiv_selected]
  unfold originalRemovedRow
  rw [originalSelectedRowPosition]
  exact he

/-- The full-source diagonal embeds as the canonical component response. -/
theorem originalLocalResponse_eq_componentResponse {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (c : SelectedCoordinate D hD) :
    c.regularEmbedding (c.originalLocalResponse P (some b) (some b)) =
      componentResponse (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)) := by
  rw [c.originalLocalResponse_diagonal_embedding, originalSelectedCorner_field,
    componentResponse_eq_inverseContraction]
  congr 1
  let Q := interiorBlockProfile P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)
  let e := (finCongr (originalSelectedRemovedSize P b)).symm
  let r : Fin (originalRemovedSize (hD := hD) P b.val) → actualField :=
    fun j => originalMap
      ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr ⟨b.val, j⟩))
  let s : Fin (originalRemovedSize (hD := hD) P b.val) → actualField :=
    fun j => originalMap
      ((originalSplitMatrix (hD := hD) P) (.inr ⟨b.val, j⟩) (.inl (some b)))
  change inverseContraction r s ((originalRemovedDiagonal (hD := hD) P b.val).map originalMap) =
    inverseContraction (fun j => originalMatrix Q 0 j.castSucc)
      (fun j => originalMatrix Q j.succ (Fin.last _)) (deletedTopRightOriginalMatrix Q)
  rw [← inverseContraction_equiv e r s]
  have hr : r ∘ e = fun j => originalMatrix Q 0 j.castSucc := by
    funext j
    exact originalSelectedIncoming_field P b j
  have hs : s ∘ e = fun j => originalMatrix Q j.succ (Fin.last _) := by
    funext j
    exact originalSelectedOutgoing_field P b j
  have hm : ((originalRemovedDiagonal (hD := hD) P b.val).map originalMap).submatrix e e =
      deletedTopRightOriginalMatrix Q := originalRemovedDiagonal_selected_field P b
  rw [hr, hs, hm]

/-- The exact normal quotient now holds for a selected component inside the full original source. -/
theorem originalLocalResponse_eq_normal_quotient {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (c : SelectedCoordinate D hD) :
    c.regularEmbedding (c.originalLocalResponse P (some b) (some b)) =
      originalMap (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)).schur /
      componentCoefficient (interiorBlockProfile P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)) := by
  rw [originalLocalResponse_eq_componentResponse P b c, componentResponse_eq_normal_quotient]

/-- Actual selection identifies the canonical component function with the selected prime exactly. -/
theorem originalSelectedProfile_schur {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    (interiorBlockProfile P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)).schur = cellSchur D hD.1 := by
  have hi := originalBlockSelected_nonempty P b.val b.property
  have he := (dvd_originalBlock_iff (hD := hD) P b.val.val hi).mp b.property
  exact (interior_block_det_eq_profile P b.val.val hi).symm.trans
    ((originalBlock_det_eq_cellSchur P b.val.val hi).trans he.symm)

/-- Actual selection supplies the selected geometric top. -/
theorem originalSelectedProfile_top {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (c : SelectedCoordinate D hD) :
    (interiorBlockProfile P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)).topVar = c.top := by
  apply Subtype.ext
  have he := congrArg polynomialSpan (originalSelectedProfile_schur P b)
  rw [Profile.polynomialSpan_schur, polynomialSpan_cellSchur hD, ← c.span_eq] at he
  exact he

/-- The canonical component's signed cofactor is the actual selected coordinate's coefficient. -/
theorem originalSelectedProfile_coefficient {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (c : SelectedCoordinate D hD) :
    componentCoefficient (interiorBlockProfile P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)) = originalMap c.coefficient := by
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  have he : generatorDeriv Q.topVar (originalMap Q.schur) = componentCoefficient Q := by
    rw [generatorDeriv_originalMap, Q.pderiv_schur_eq_interiorSchur]
    rfl
  rw [← he, originalSelectedProfile_top P b c, originalSelectedProfile_schur P b, c.prime_eq]
  exact generatorDeriv_affineCoordinate _ _ _ c.top_notMem_coefficient c.top_notMem_remainder

/-- The assembled source's selected diagonal is exactly the actual prime divided by its cofactor. -/
theorem originalLocalResponse_eq_selected_quotient {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (c : SelectedCoordinate D hD) :
    c.regularEmbedding (c.originalLocalResponse P (some b) (some b)) =
      originalMap (cellSchur D hD.1) / originalMap c.coefficient := by
  rw [originalLocalResponse_eq_normal_quotient P b c, originalSelectedProfile_schur P b,
    originalSelectedProfile_coefficient P b c]

/-- The same exact quotient identity already holds multiplicatively in the selected local ring. -/
theorem originalLocalResponse_mul_coefficient {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (c : SelectedCoordinate D hD) :
    c.originalLocalResponse P (some b) (some b) * algebraMap Lambda c.RegularRing c.coefficient =
      algebraMap Lambda c.RegularRing (cellSchur D hD.1) := by
  apply c.regularEmbedding_injective
  rw [map_mul, c.regularEmbedding_polynomial, c.regularEmbedding_polynomial,
    originalLocalResponse_eq_selected_quotient P b c]
  exact div_mul_cancel₀ _ (by simpa only [ne_eq, originalMap_eq_zero] using c.coefficient_ne_zero)

/-- The actual selected same-block entry vanishes at residue after full original elimination. -/
theorem originalLocalResponse_diagonal_residue_zero {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (c : SelectedCoordinate D hD) :
    c.regularResidue (c.originalLocalResponse P (some b) (some b)) = 0 := by
  have he := congrArg c.regularResidue (originalLocalResponse_mul_coefficient P b c)
  rw [map_mul, c.regularResidue_polynomial, c.regularResidue_polynomial] at he
  have hp : c.residueMap (cellSchur D hD.1) = 0 :=
    (c.residueMap_eq_zero_iff _).mpr dvd_rfl
  rw [hp] at he
  exact (mul_eq_zero.mp he).resolve_right
    ((c.residueMap_ne_zero_iff _).mpr c.not_dvd_coefficient)

end SelectedCoordinate
end SkewCornerDescent.Matrix
