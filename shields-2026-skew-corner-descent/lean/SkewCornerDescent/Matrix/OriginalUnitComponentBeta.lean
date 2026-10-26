/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSourcePartition

/-!
# Literal beta lists of actual nonselected component fibers

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The genuine full component profile and its content translation identify every original
remaining row and column. The entire fiber matrix, not just its diagonal, is retained.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Literal content translation from the normalized component's last column. -/
def originalComponentTau {n : ℕ} (P : Profile n) (b : OriginalBlocks P) : ℤ :=
  P.zeta (interiorBlockLast P b.val).castSucc

/-- Every row of a nonselected component remains in its complete original fiber. -/
def originalUnitIndex {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (i : Fin (interiorBlockLength P b.val + 1)) :
    Fin (originalRemovedSize (hD := hD) P b) :=
  Fin.cast (by simp only [originalRemovedSize, ite_eq_right hs]) i

/-- The actual nonselected row position is the full component position. -/
theorem originalUnitIndex_row {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (i : Fin (interiorBlockLength P b.val + 1)) :
    originalRemovedRowPosition (hD := hD) P b (originalUnitIndex P b hs i) = i := by
  apply Fin.ext
  rw [originalRemovedRowPosition_val, ite_eq_right hs]
  rfl

/-- The actual nonselected column position is the full component position. -/
theorem originalUnitIndex_col {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (i : Fin (interiorBlockLength P b.val + 1)) :
    originalRemovedColPosition (hD := hD) P b (originalUnitIndex P b hs i) = i := by
  apply Fin.ext
  rfl

/-- The normalized component's last slice index is its actual last original index. -/
theorem interiorBlock_slice_last {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    interiorSliceIndex (interiorBlockFirst P b.val).val (interiorBlockLength P b.val)
      (interiorBlock_interval_bound P b.val) (Fin.last _) = interiorBlockLast P b.val := by
  apply Fin.ext
  have h := Fin.le_def.mp (interiorBlockFirst_le_last P b.val)
  simp only [interiorSliceIndex, Fin.val_last, interiorBlockLength]
  omega

/-- Both complete original beta lists are produced from one actual connected component
profile and its literal translation. No beta-list matching premise is supplied. -/
theorem original_unit_component_beta {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ)
    (i : Fin (interiorBlockLength P b.val + 1)) :
    P.xi (originalRemovedRow (hD := hD) P b (originalUnitIndex P b hs i)).succ =
      (interiorBlockProfile P b.val hne).xi i + originalComponentTau P b ∧
    P.zeta (originalRemovedCol (hD := hD) P b (originalUnitIndex P b hs i)).castSucc =
      (interiorBlockProfile P b.val hne).zeta i + originalComponentTau P b := by
  obtain ⟨hx, hz⟩ := interiorSliceProfile_beta P (interiorBlockFirst P b.val).val
    (interiorBlockLength P b.val) (interiorBlock_interval_bound P b.val)
    (interiorBlock_slice_same P b.val) (interiorBlock_first_nonempty P b.val hne)
  unfold originalRemovedRow originalRemovedCol
  rw [originalUnitIndex_row, originalUnitIndex_col]
  change _ = (interiorSliceProfile _ _ _ _ _ _).xi i + _ ∧
    _ = (interiorSliceProfile _ _ _ _ _ _).zeta i + _
  rw [hx, hz]
  simp only [interiorSliceBetaPair, originalComponentTau, interiorBlock_slice_last,
    sub_add_cancel]
  exact ⟨True.intro, True.intro⟩

/-- The complete actual diagonal fiber is the normalized component JT matrix.
All original off-diagonal entries inside this component survive the identification. -/
theorem original_unit_component_matrix {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ) :
    (originalRemovedMatrix (hD := hD) P).submatrix
      (fun i => ⟨b, originalUnitIndex P b hs i⟩)
      (fun j => ⟨b, originalUnitIndex P b hs j⟩) =
    jtMatrix (interiorBlockProfile P b.val hne).xi
      (interiorBlockProfile P b.val hne).zeta := by
  ext i j : 1
  change hh (_ - _) = hh (_ - _)
  rw [(original_unit_component_beta P b hs hne i).1,
    (original_unit_component_beta P b hs hne j).2]
  congr 1
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
