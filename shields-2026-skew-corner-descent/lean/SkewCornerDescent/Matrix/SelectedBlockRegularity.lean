/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalBlockRegularity

/-!
# Proper removed matrices of selected original blocks

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Each selected actual block retains its first
row and last column. Its complete remaining proper minor is regular and invertible in the
selected local ring, including a one-row component with an empty proper minor. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Actual source entries after retaining the selected block's first row and last column. -/
noncomputable def originalSelectedMinor {n : ℕ} (P : Profile n) (i : Fin n) :
    Matrix (Fin (interiorBlockLength P i)) (Fin (interiorBlockLength P i)) Lambda :=
  jtMatrix
    (fun j => P.xi (interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) j.succ).succ)
    (fun j => P.zeta (interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) j.castSucc).castSucc)

/-- The full original proper minor is exactly the normalized component's proper JT minor. -/
theorem originalSelectedMinor_eq_profile {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    originalSelectedMinor P i =
      jtMatrix (fun j : Fin (interiorBlockLength P i) => (interiorBlockProfile P i hi).xi j.succ)
        (fun j => (interiorBlockProfile P i hi).zeta j.castSucc) := by
  obtain ⟨hxi, hzeta⟩ := interiorSliceProfile_beta P _ _ _ (interiorBlock_slice_same P i)
    (interiorBlock_first_nonempty P i hi)
  change originalSelectedMinor P i =
    jtMatrix (fun j : Fin (interiorBlockLength P i) =>
      (interiorSliceProfile P _ _ _ (interiorBlock_slice_same P i)
        (interiorBlock_first_nonempty P i hi)).xi j.succ)
      (fun j => (interiorSliceProfile P _ _ _ (interiorBlock_slice_same P i)
        (interiorBlock_first_nonempty P i hi)).zeta j.castSucc)
  rw [hxi, hzeta]
  apply Matrix.ext
  intro j k
  change hh (P.xi (interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) j.succ).succ -
      P.zeta (interiorSliceIndex (interiorBlockFirst P i).val
        (interiorBlockLength P i) (interiorBlock_interval_bound P i) k.castSucc).castSucc) = _
  congr 1
  dsimp only [interiorSliceBetaPair]
  ring

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact component selection supplies regularity of the entire original proper minor. -/
theorem not_dvd_originalSelectedMinor {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ)
    (he : cellSchur D hD.1 =
      cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1) :
    ¬ cellSchur D hD.1 ∣ (originalSelectedMinor P i).det := by
  let Q := interiorBlockProfile P i hi
  obtain ⟨q⟩ := exists_selectedCoordinate Q.isConnectedSkew_cells
  have hq := q.not_dvd_selectedMinor Q (cellSchur_cells Q)
  rw [cellSchur_cells] at hq
  rw [he, interiorBlockCells_schur P i hi,
    interiorSliceProfile_matrix P _ _ _ (interiorBlock_slice_same P i)
      (interiorBlock_first_nonempty P i hi), originalSelectedMinor_eq_profile P i hi]
  exact hq

/-- The actual proper selected block inverse is produced in the original selected local ring. -/
@[instance_reducible]
noncomputable def originalSelectedMinorLocalInverse {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ)
    (he : cellSchur D hD.1 =
      cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1) :
    Invertible ((originalSelectedMinor P i).map (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (not_dvd_originalSelectedMinor (hD := hD) P i hi he)

/-- The same actual proper selected matrix has its complete inverse after taking the residue. -/
@[instance_reducible]
noncomputable def originalSelectedMinorResidueInverse {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ)
    (he : cellSchur D hD.1 =
      cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1) :
    Invertible ((originalSelectedMinor P i).map c.residueMap) :=
  c.regularResidueMatrixInverse _ (not_dvd_originalSelectedMinor (hD := hD) P i hi he)

end SelectedCoordinate
end SkewCornerDescent.Matrix
