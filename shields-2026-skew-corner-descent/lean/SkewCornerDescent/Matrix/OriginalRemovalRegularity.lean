/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalRemovalLayout

/-!
# Regularity of the complete original removed matrix

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Complete source diagonal matrices are
identified with either full nonselected blocks or proper selected blocks. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire remaining source diagonal matrix of a single actual component. -/
noncomputable def originalRemovedDiagonal {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    Matrix (Fin (originalRemovedSize (hD := hD) P b))
      (Fin (originalRemovedSize (hD := hD) P b)) Lambda :=
  Matrix.of fun j k => hh (P.xi (originalRemovedRow (hD := hD) P b j).succ -
    P.zeta (originalRemovedCol (hD := hD) P b k).castSucc)

/-- The assembled sigma diagonal contains exactly the complete remaining source block. -/
theorem originalRemovedDiagonal_reindex {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    Matrix.reindex (originalRemovedFiberEquiv (hD := hD) P b).symm
      (originalRemovedFiberEquiv (hD := hD) P b).symm
      ((originalRemovedMatrix (hD := hD) P).toSquareBlock Sigma.fst b) =
      originalRemovedDiagonal (hD := hD) P b := by
  apply Matrix.ext
  intro j k
  rfl

/-- Source positions in a selected block yield its actual complete proper minor. -/
theorem originalRemovedDiagonal_selected {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : originalBlockSelected (hD := hD) P b) :
    Matrix.reindex (finCongr (by simp only [originalRemovedSize, ite_eq_left hs]))
      (finCongr (by simp only [originalRemovedSize, ite_eq_left hs]))
      (originalRemovedDiagonal (hD := hD) P b) = originalSelectedMinor P b.val := by
  apply Matrix.ext
  intro j k
  simp only [Matrix.reindex_apply, originalRemovedDiagonal, Matrix.of_apply,
    originalSelectedMinor, jtMatrix, originalRemovedRow, originalRemovedCol,
    originalRemovedRowPosition, originalRemovedColPosition, dite_eq_left hs]
  rfl

/-- Source positions in a nonselected block retain its whole original interval matrix. -/
theorem originalRemovedDiagonal_nonselected {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b) :
    Matrix.reindex (finCongr (by simp only [originalRemovedSize, ite_eq_right hs]))
      (finCongr (by simp only [originalRemovedSize, ite_eq_right hs]))
      (originalRemovedDiagonal (hD := hD) P b) =
      jtMatrix (fun j => P.xi (interiorSliceIndex (interiorBlockFirst P b.val).val
          (interiorBlockLength P b.val) (interiorBlock_interval_bound P b.val) j).succ)
        (fun j => P.zeta (interiorSliceIndex (interiorBlockFirst P b.val).val
          (interiorBlockLength P b.val) (interiorBlock_interval_bound P b.val) j).castSucc) := by
  apply Matrix.ext
  intro j k
  simp only [Matrix.reindex_apply, originalRemovedDiagonal, Matrix.of_apply, jtMatrix,
    originalRemovedRow, originalRemovedCol, originalRemovedRowPosition,
    originalRemovedColPosition, dite_eq_right hs]
  rfl

/-- Every selected component has a genuinely nonempty row; an empty pivot cannot be selected. -/
theorem originalBlockSelected_nonempty {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : originalBlockSelected (hD := hD) P b) :
    P.zeta b.val.castSucc < P.xi b.val.succ := by
  have hle := P.zeta_le_xi_succ b.val
  by_contra hn
  have he : P.xi b.val.succ = P.zeta b.val.castSucc := by omega
  exact not_dvd_originalEmptyBlock (hD := hD) P b.val he hs

/-- The complete selected diagonal determinant is the actual proper component minor. -/
theorem originalRemovedDiagonal_det_selected {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : originalBlockSelected (hD := hD) P b) :
    (originalRemovedDiagonal (hD := hD) P b).det = (originalSelectedMinor P b.val).det := by
  have he := Matrix.det_reindex_self
    (finCongr (show originalRemovedSize (hD := hD) P b = interiorBlockLength P b.val from
      by simp only [originalRemovedSize, ite_eq_left hs]))
    (originalRemovedDiagonal (hD := hD) P b)
  rw [originalRemovedDiagonal_selected (hD := hD) P b hs] at he
  exact he.symm

/-- The entire nonselected diagonal determinant is the original full block determinant. -/
theorem originalRemovedDiagonal_det_nonselected {n : ℕ} (P : Profile n)
    (b : OriginalBlocks P) (hs : ¬ originalBlockSelected (hD := hD) P b) :
    (originalRemovedDiagonal (hD := hD) P b).det =
      ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
        (interiorBlock P) (interiorBlock P b.val)).det := by
  have he := Matrix.det_reindex_self
    (finCongr (show originalRemovedSize (hD := hD) P b = interiorBlockLength P b.val + 1 from
      by simp only [originalRemovedSize, ite_eq_right hs]))
    (originalRemovedDiagonal (hD := hD) P b)
  rw [originalRemovedDiagonal_nonselected (hD := hD) P b hs] at he
  exact he.symm.trans (interior_block_det_eq_interval P b.val).symm

/-- Actual selection and component proofs supply regularity of every complete removed diagonal. -/
theorem not_dvd_originalRemovedDiagonal {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    ¬ cellSchur D hD.1 ∣ (originalRemovedDiagonal (hD := hD) P b).det := by
  by_cases hs : originalBlockSelected (hD := hD) P b
  · have hi := originalBlockSelected_nonempty (hD := hD) P b hs
    have he := (dvd_originalBlock_iff (hD := hD) P b.val hi).mp hs
    rw [originalRemovedDiagonal_det_selected (hD := hD) P b hs]
    exact not_dvd_originalSelectedMinor (hD := hD) P b.val hi he
  · rw [originalRemovedDiagonal_det_nonselected (hD := hD) P b hs]
    exact hs

/-- The entire assembled original removed matrix has regular determinant at the selected prime. -/
theorem not_dvd_originalRemovedMatrix {n : ℕ} (P : Profile n) :
    ¬ cellSchur D hD.1 ∣ (originalRemovedMatrix (hD := hD) P).det := by
  rw [(originalRemovedMatrix_blockTriangular_fst (hD := hD) P).det_fintype]
  apply (irreducible_cellSchur hD).prime.not_dvd_finsetProd
  intro b _
  have he := Matrix.det_reindex_self (originalRemovedFiberEquiv (hD := hD) P b).symm
    ((originalRemovedMatrix (hD := hD) P).toSquareBlock Sigma.fst b)
  rw [originalRemovedDiagonal_reindex (hD := hD) P b] at he
  rw [← he]
  exact not_dvd_originalRemovedDiagonal (hD := hD) P b

/-- The full original removed matrix inverse is produced, with every off-diagonal entry present. -/
@[instance_reducible]
noncomputable def originalRemovedLocalInverse {n : ℕ} (P : Profile n) :
    Invertible ((originalRemovedMatrix (hD := hD) P).map (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (not_dvd_originalRemovedMatrix (hD := hD) P)

/-- Taking the residue preserves the produced full inverse of the original removed matrix. -/
@[instance_reducible]
noncomputable def originalRemovedResidueInverse {n : ℕ} (P : Profile n) :
    Invertible ((originalRemovedMatrix (hD := hD) P).map c.residueMap) :=
  c.regularResidueMatrixInverse _ (not_dvd_originalRemovedMatrix (hD := hD) P)

end SkewCornerDescent.Matrix.SelectedCoordinate
