/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.InteriorBlockDeterminants
import SkewCornerDescent.Matrix.ComponentRegularMatrices

/-!
# Local inverses of the produced original blocks

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Nonselected geometric components give
regular complete original block matrices, including tied spans. Empty rows give unit blocks.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The block determinant is the actual component function, not merely an associate. -/
theorem originalBlock_det_eq_cellSchur {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
      (interiorBlock P) (interiorBlock P i)).det =
      cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1 := by
  rw [interior_block_det_eq_profile P i hi, interiorBlockCells_schur P i hi,
    interiorSliceProfile_matrix P _ _ _ (interiorBlock_slice_same P i)
      (interiorBlock_first_nonempty P i hi)]
  rfl

/-- Every nonselected actual nonempty diagonal block has a regular determinant. -/
theorem not_dvd_originalBlock {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ)
    (hne : cellSchur D hD.1 ≠
      cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1) :
    ¬ cellSchur D hD.1 ∣
      ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
        (interiorBlock P) (interiorBlock P i)).det := by
  rw [originalBlock_det_eq_cellSchur P i hi]
  exact not_dvd_distinct_component hD (interiorBlockCells_connected P i hi) hne

/-- Selection by divisibility of an actual block is exact equality with its component function. -/
theorem dvd_originalBlock_iff {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    cellSchur D hD.1 ∣
      ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
        (interiorBlock P) (interiorBlock P i)).det ↔
      cellSchur D hD.1 =
        cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1 := by
  constructor
  · intro hd
    by_contra hn
    exact not_dvd_originalBlock (hD := hD) P i hi hn hd
  · intro he
    rw [originalBlock_det_eq_cellSchur P i hi, ← he]

/-- Produce the full original block inverse without an inverse or regularity hypothesis. -/
@[instance_reducible]
noncomputable def originalBlockLocalInverse {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ)
    (hne : cellSchur D hD.1 ≠
      cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1) :
    Invertible (((jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).toSquareBlock (interiorBlock P) (interiorBlock P i)).map
        (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (not_dvd_originalBlock (hD := hD) P i hi hne)

/-- Produce the full original nonselected block inverse after taking the selected residue. -/
@[instance_reducible]
noncomputable def originalBlockResidueInverse {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ)
    (hne : cellSchur D hD.1 ≠
      cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1) :
    Invertible (((jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).toSquareBlock (interiorBlock P) (interiorBlock P i)).map
        c.residueMap) :=
  c.regularResidueMatrixInverse _ (not_dvd_originalBlock (hD := hD) P i hi hne)

/-- Empty original row blocks are regular units, independently of the selected prime. -/
theorem not_dvd_originalEmptyBlock {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.xi i.succ = P.zeta i.castSucc) :
    ¬ cellSchur D hD.1 ∣
      ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
        (interiorBlock P) (interiorBlock P i)).det := by
  rw [interior_empty_block_det P i hi]
  exact (irreducible_cellSchur hD).not_dvd_one

/-- The literal empty-row pivot is inverted as its complete original block. -/
@[instance_reducible]
noncomputable def originalEmptyBlockLocalInverse {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.xi i.succ = P.zeta i.castSucc) :
    Invertible (((jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).toSquareBlock (interiorBlock P) (interiorBlock P i)).map
        (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (not_dvd_originalEmptyBlock (hD := hD) P i hi)

end SkewCornerDescent.Matrix.SelectedCoordinate
