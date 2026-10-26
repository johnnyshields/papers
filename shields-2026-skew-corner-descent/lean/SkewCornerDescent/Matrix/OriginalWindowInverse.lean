/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRemainingMatrices

/-!
# Full regular inverses for actual whole-window matrices

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The complete
remaining window matrix is inverted with every coupling intact. Regularity is derived
from the actual component selection and proper minors, not assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire original removed matrix on the complete whole-window inventory. -/
noncomputable def originalWholeWindowMatrix {n : ℕ} (P : Profile n) (lo hi : ℤ) :
    Matrix (OriginalWholeWindowRemaining (hD := hD) P lo hi)
      (OriginalWholeWindowRemaining (hD := hD) P lo hi) Lambda :=
  Matrix.of fun i j => originalRemovedMatrix P ⟨i.1.val, i.2⟩ ⟨j.1.val, j.2⟩

/-- Canonical whole-window blocks keep the actual source matrix block order. -/
theorem originalWholeWindowMatrix_blockTriangular {n : ℕ} (P : Profile n) (lo hi : ℤ) :
    (originalWholeWindowMatrix (hD := hD) P lo hi).BlockTriangular Sigma.fst := by
  intro i j hij
  exact originalRemovedMatrix_blockTriangular_fst (hD := hD) P
    (show j.1.val < i.1.val from hij)

/-- A diagonal window fiber contains every remaining position of its whole original block. -/
def originalWholeWindowFiberEquiv {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b : OriginalWholeWindowBlocks P lo hi) :
    Fin (originalRemovedSize (hD := hD) P b.val) ≃
      {i : OriginalWholeWindowRemaining (hD := hD) P lo hi // i.1 = b} where
  toFun k := ⟨⟨b, k⟩, rfl⟩
  invFun i := i.property ▸ i.val.2
  left_inv _ := rfl
  right_inv i := by
    rcases i with ⟨⟨d, k⟩, he⟩
    change d = b at he
    subst d
    rfl

/-- The full diagonal window fiber is the actual selected or unselected proper block. -/
theorem originalWholeWindowMatrix_diagonal {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b : OriginalWholeWindowBlocks P lo hi) :
    Matrix.reindex (originalWholeWindowFiberEquiv (hD := hD) P lo hi b).symm
      (originalWholeWindowFiberEquiv (hD := hD) P lo hi b).symm
      ((originalWholeWindowMatrix (hD := hD) P lo hi).toSquareBlock Sigma.fst b) =
      originalRemovedDiagonal (hD := hD) P b.val := by
  apply Matrix.ext
  intro i j
  rfl

/-- The selected prime does not divide the complete actual window removed determinant. -/
theorem not_dvd_originalWholeWindowMatrix {n : ℕ} (P : Profile n) (lo hi : ℤ) :
    ¬ cellSchur D hD.1 ∣ (originalWholeWindowMatrix (hD := hD) P lo hi).det := by
  rw [(originalWholeWindowMatrix_blockTriangular (hD := hD) P lo hi).det_fintype]
  apply (irreducible_cellSchur hD).prime.not_dvd_finsetProd
  intro b _
  have he := Matrix.det_reindex_self (originalWholeWindowFiberEquiv (hD := hD) P lo hi b).symm
    ((originalWholeWindowMatrix (hD := hD) P lo hi).toSquareBlock Sigma.fst b)
  rw [originalWholeWindowMatrix_diagonal (hD := hD) P lo hi b] at he
  rw [← he]
  exact not_dvd_originalRemovedDiagonal (hD := hD) P b.val

/-- The full normal-dependent original window inverse is produced in the regular ring. -/
@[instance_reducible]
noncomputable def originalWholeWindowLocalInverse {n : ℕ} (P : Profile n) (lo hi : ℤ) :
    Invertible ((originalWholeWindowMatrix (hD := hD) P lo hi).map
      (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (not_dvd_originalWholeWindowMatrix (hD := hD) P lo hi)

/-- The full field inverse retains all original generator dependence of the window matrix. -/
@[instance_reducible]
noncomputable def originalWholeWindowFieldInverse {n : ℕ} (P : Profile n) (lo hi : ℤ) :
    Invertible (intervalMatrix
      (fun i : OriginalWholeWindowRemaining (hD := hD) P lo hi =>
        originalResponseRows P ⟨i.1.val, i.2⟩)
      (fun i => originalResponseCols P ⟨i.1.val, i.2⟩)) :=
  c.regularEmbeddedMatrixInverse (originalWholeWindowMatrix (hD := hD) P lo hi)
    (not_dvd_originalWholeWindowMatrix (hD := hD) P lo hi)

end SkewCornerDescent.Matrix.SelectedCoordinate
