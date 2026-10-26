/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureComponents

/-!
# Literal component selection in an actual source profile

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). A component with the selected Schur function
supplies its own canonical selected block; the block is not an independent input. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Different representatives of one complete block describe precisely the same cells. -/
theorem interiorBlockCells_eq_of_label_eq {n : ℕ} (P : Profile n) {i j : Fin n}
    (h : interiorBlock P i = interiorBlock P j) :
    interiorBlockCells P i = interiorBlockCells P j := by
  ext x
  obtain ⟨r, b⟩ := x
  simp only [mem_interiorBlockCells, h]

namespace SelectedCoordinate

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual component and equality of its function produce its canonical selected occurrence. -/
theorem exists_originalSelectedBlock_of_component {n : ℕ} (P : Profile n) (C : Diagram)
    (hC : C ∈ edgeComponents (diagramInterior P.cells))
    (he : cellSchur D hD.1 = cellSchur C (isSkew_component P.isConnectedSkew_cells.1.interior hC)) :
    ∃ b : OriginalSelectedBlocks (hD := hD) P, interiorBlockCells P b.val.val = C := by
  obtain ⟨i, hi, hcells⟩ := (interior_components_eq_blocks P C).mp hC
  let b : OriginalBlocks P := ⟨interiorBlockFirst P i, interiorBlockFirst_idem P i⟩
  have hlabel : interiorBlock P b.val = interiorBlock P i :=
    (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)
  have hbCells : interiorBlockCells P b.val = C :=
    (interiorBlockCells_eq_of_label_eq P hlabel).trans hcells.symm
  have hbi : P.zeta b.val.castSucc < P.xi b.val.succ := by
    simpa only [b, interiorSliceIndex, Fin.val_zero, add_zero] using
      interiorBlock_first_nonempty P i hi
  have hbSel : originalBlockSelected (hD := hD) P b := by
    apply (dvd_originalBlock_iff (hD := hD) P b.val hbi).mpr
    exact he.trans (cellSchur_congr hbCells.symm _ _)
  exact ⟨⟨b, hbSel⟩, hbCells⟩

/-- A translated source component produces an actual selected block in the source profile. -/
theorem exists_originalSelectedBlock_of_translated_component {n : ℕ} (P : Profile n)
    (v : ℤ × ℤ) (C : Diagram)
    (hC : C ∈ edgeComponents (diagramInterior (translate v P.cells)))
    (he : cellSchur D hD.1 = cellSchur C
      (isSkew_component (isSkew_translate v P.isConnectedSkew_cells.1).interior hC)) :
    ∃ b : OriginalSelectedBlocks (hD := hD) P,
      translate v (interiorBlockCells P b.val.val) = C := by
  have hCt := hC
  rw [interior_translate, edgeComponents_translate] at hCt
  obtain ⟨E, hE, hEC⟩ := Finset.mem_image.mp hCt
  have heE : cellSchur D hD.1 =
      cellSchur E (isSkew_component P.isConnectedSkew_cells.1.interior hE) := by
    exact he.trans ((cellSchur_congr hEC.symm _ _).trans
      (cellSchur_translate E (isSkew_component P.isConnectedSkew_cells.1.interior hE) v))
  obtain ⟨b, hb⟩ := exists_originalSelectedBlock_of_component (hD := hD) P E hE heE
  exact ⟨b, by rw [hb, hEC]⟩

end SelectedCoordinate
end SkewCornerDescent.Matrix
