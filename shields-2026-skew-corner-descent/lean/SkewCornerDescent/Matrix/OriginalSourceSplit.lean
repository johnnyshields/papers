/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalSourcePartition

/-!
# Full original retained-source split

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Separate bijective row and column partitions
produce the actual complete removed block and its full local Schur response. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable


variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The retained global source row is the literal top row. -/
theorem originalRowSplitEquiv_corner {n : ℕ} (P : Profile n) :
    originalRowSplitEquiv (hD := hD) P (.inl none) = 0 := rfl

/-- The retained global source column is the literal last column. -/
theorem originalColSplitEquiv_corner {n : ℕ} (P : Profile n) :
    originalColSplitEquiv (hD := hD) P (.inl none) = Fin.last n := rfl

/-- The removed source rows are exactly the original rows used in the assembled matrix. -/
theorem originalRowSplitEquiv_removed {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalRowSplitEquiv (hD := hD) P (.inr j) =
      (originalRemovedRow (hD := hD) P j.1 j.2).succ := by
  change Fin.succAbove 0 (originalBlockIndex P
    ⟨j.1, originalRemovedRowPosition (hD := hD) P j.1 j.2⟩) = _
  rw [Fin.succAbove_zero]
  rfl

/-- The removed source columns keep their original complementary column positions. -/
theorem originalColSplitEquiv_removed {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalColSplitEquiv (hD := hD) P (.inr j) =
      (originalRemovedCol (hD := hD) P j.1 j.2).castSucc := by
  change Fin.succAbove (Fin.last n) (originalBlockIndex P
    ⟨j.1, originalRemovedColPosition (hD := hD) P j.1 j.2⟩) = _
  rw [Fin.succAbove_last]
  rfl

/-- A retained component row is its original first row, not an abstract replacement. -/
theorem originalRowSplitEquiv_selected {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalRowSplitEquiv (hD := hD) P (.inl (some b)) = b.val.val.succ := by
  change Fin.succAbove 0 (originalBlockIndex P ⟨b.val, 0⟩) = _
  rw [Fin.succAbove_zero]
  congr 1
  apply Fin.ext
  simp only [originalBlockIndex, interiorSliceIndex, Fin.val_zero, add_zero, b.val.property]

/-- A retained component column is its original last column, including one-row components. -/
theorem originalColSplitEquiv_selected {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalColSplitEquiv (hD := hD) P (.inl (some b)) =
      (interiorBlockLast P b.val.val).castSucc := by
  change Fin.succAbove (Fin.last n) (originalBlockIndex P ⟨b.val, Fin.last _⟩) = _
  rw [Fin.succAbove_last]
  congr 1
  apply Fin.ext
  have hb := Fin.le_def.mp (interiorBlockFirst_le_last P b.val.val)
  change (interiorBlockFirst P b.val.val).val + interiorBlockLength P b.val.val =
    (interiorBlockLast P b.val.val).val
  unfold interiorBlockLength
  omega

/-- The full original Jacobi--Trudi source in the produced retained/removed coordinates. -/
noncomputable def originalSplitMatrix {n : ℕ} (P : Profile n) :
    Matrix (Option (OriginalSelectedBlocks (hD := hD) P) ⊕
      OriginalRemainingIndices (hD := hD) P)
      (Option (OriginalSelectedBlocks (hD := hD) P) ⊕
        OriginalRemainingIndices (hD := hD) P) Lambda :=
  (jtMatrix P.xi P.zeta).submatrix (originalRowSplitEquiv (hD := hD) P)
    (originalColSplitEquiv (hD := hD) P)

/-- The full source's removed block is the proved regular actual removed matrix. -/
theorem originalSplitMatrix_removed {n : ℕ} (P : Profile n) :
    (originalSplitMatrix (hD := hD) P).toBlocks₂₂ =
      originalRemovedMatrix (hD := hD) P := by
  apply Matrix.ext
  intro j k
  change hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inr j)) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inr k))) = _
  rw [originalRowSplitEquiv_removed, originalColSplitEquiv_removed]
  rfl

/-- All four source blocks assemble back to the full bijectively indexed original matrix. -/
theorem originalSplitMatrix_fromBlocks {n : ℕ} (P : Profile n) :
    Matrix.fromBlocks (originalSplitMatrix (hD := hD) P).toBlocks₁₁
      (originalSplitMatrix (hD := hD) P).toBlocks₁₂
      (originalSplitMatrix (hD := hD) P).toBlocks₂₁
      (originalRemovedMatrix (hD := hD) P) = originalSplitMatrix (hD := hD) P := by
  rw [← originalSplitMatrix_removed P]
  exact Matrix.fromBlocks_toBlocks _

/-- The original local response uses the full inverse supplied by actual component selection. -/
noncomputable def originalLocalResponse {n : ℕ} (P : Profile n) :
    Matrix (Option (OriginalSelectedBlocks (hD := hD) P))
      (Option (OriginalSelectedBlocks (hD := hD) P)) c.RegularRing :=
  c.localRetainedResponse (originalSplitMatrix (hD := hD) P).toBlocks₁₁
    (originalSplitMatrix (hD := hD) P).toBlocks₁₂
    (originalSplitMatrix (hD := hD) P).toBlocks₂₁
    (originalRemovedMatrix (hD := hD) P) (not_dvd_originalRemovedMatrix P)

/-- Actual full-source determinant factorization holds before residue specialization. -/
theorem originalSplitMatrix_local_det {n : ℕ} (P : Profile n) :
    algebraMap Lambda c.RegularRing (originalSplitMatrix (hD := hD) P).det =
      algebraMap Lambda c.RegularRing (originalRemovedMatrix (hD := hD) P).det *
        (c.originalLocalResponse P).det := by
  have he := c.local_det_eq_removed_mul_response
    (originalSplitMatrix (hD := hD) P).toBlocks₁₁
    (originalSplitMatrix (hD := hD) P).toBlocks₁₂
    (originalSplitMatrix (hD := hD) P).toBlocks₂₁
    (originalRemovedMatrix (hD := hD) P) (not_dvd_originalRemovedMatrix P)
  rw [originalSplitMatrix_fromBlocks P] at he
  exact he

/-- The actual original source response specializes with its entire inverse intact. -/
theorem originalLocalResponse_residue {n : ℕ} (P : Profile n) :
    let _ := c.originalRemovedResidueInverse P
    (c.originalLocalResponse P).map c.regularResidue =
      retainedResponse ((originalSplitMatrix (hD := hD) P).toBlocks₁₁.map c.residueMap)
        ((originalSplitMatrix (hD := hD) P).toBlocks₁₂.map c.residueMap)
        ((originalSplitMatrix (hD := hD) P).toBlocks₂₁.map c.residueMap)
        ((originalRemovedMatrix (hD := hD) P).map c.residueMap) :=
  c.localRetainedResponse_residue _ _ _ _ _

/-- The exact orientation sign accounts for the distinct original row and column partitions. -/
theorem originalSplitMatrix_det {n : ℕ} (P : Profile n) :
    (originalSplitMatrix (hD := hD) P).det =
      (Equiv.Perm.sign ((originalColSplitEquiv (hD := hD) P).symm.trans
        (originalRowSplitEquiv (hD := hD) P)) : Lambda) * P.schur := by
  change ((jtMatrix P.xi P.zeta).reindex
    (originalRowSplitEquiv (hD := hD) P).symm
    (originalColSplitEquiv (hD := hD) P).symm).det = _
  rw [Matrix.det_reindex]
  rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
