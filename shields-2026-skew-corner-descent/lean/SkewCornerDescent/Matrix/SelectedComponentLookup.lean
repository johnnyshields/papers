/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TransposeFrameInventory
import SkewCornerDescent.Matrix.OriginalSelectedOrder
import SkewCornerDescent.Matrix.OriginalWindowSelectedRanks
import SkewCornerDescent.Matrix.OriginalComponentSelection

/-!
# Canonical selected blocks from actual geometric components

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The original complete component inventory supplies a canonical selected block
for each component with the actual selected Schur function. This is the lookup
needed to transport the first and last cap components. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A selected canonical block has exactly the actual selected component function. -/
theorem selected_block_cellSchur {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    cellSchur D hD.1 = cellSchur (interiorBlockCells P b.val.val)
      (interiorBlockCells_connected P b.val.val
        (originalBlockSelected_nonempty P b.val b.property)).1 :=
  (dvd_originalBlock_iff (hD := hD) P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)).mp b.property

/-- Actual selected components remain selected after a whole transpose and
normalization, with their complete literal cell correspondence produced. -/
theorem selected_block_transpose_exists {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    ∃ e : OriginalSelectedBlocks (hD := isConnectedSkew_transpose hD) T,
      transpose (interiorBlockCells P b.val.val) =
        translate a (interiorBlockCells T e.val.val) := by
  classical
  have hb := originalBlockSelected_nonempty P b.val b.property
  have hCb := interiorBlockCells_mem_components P b.val.val hb
  have hC : transpose (interiorBlockCells P b.val.val) ∈
      edgeComponents (diagramInterior (transpose P.cells)) := by
    rw [diagramInterior_transpose, edgeComponents_transpose]
    exact Finset.mem_image_of_mem _ hCb
  rw [ha, interior_translate, edgeComponents_translate] at hC
  obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hC
  have hc := isConnectedSkew_component T.isSkew_cells.interior hC
  have hfun := congrArg schurInvolution (selected_block_cellSchur (hD := hD) P b)
  rw [schurInvolution_cellSchur hD,
    schurInvolution_cellSchur (interiorBlockCells_connected P b.val.val hb)] at hfun
  have hfunT : cellSchur (transpose D) (isSkew_transpose hD.1) = cellSchur C hc.1 := by
    have h := cellSchur_congr he (isSkew_translate a hc.1)
      (isSkew_transpose (interiorBlockCells_connected P b.val.val hb).1)
    rw [cellSchur_translate C hc.1 a] at h
    exact hfun.trans h.symm
  obtain ⟨e, hEC⟩ := exists_originalSelectedBlock_of_component
    (hD := isConnectedSkew_transpose hD) T C hC hfunT
  refine ⟨e, ?_⟩
  rw [hEC]
  exact he.symm

/-- Every actual selected transposed component comes from one complete
original selected component. This supplies the reverse direction without
casting a block through a double-transposed diagram type. -/
theorem selected_block_transpose_exists_reverse {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells)
    (e : OriginalSelectedBlocks (hD := isConnectedSkew_transpose hD) T) :
    ∃ b : OriginalSelectedBlocks (hD := hD) P,
      transpose (interiorBlockCells P b.val.val) =
        translate a (interiorBlockCells T e.val.val) := by
  classical
  have he := originalBlockSelected_nonempty T e.val e.property
  have hCT := interiorBlockCells_mem_components T e.val.val he
  have hm : translate a (interiorBlockCells T e.val.val) ∈
      edgeComponents (diagramInterior (transpose P.cells)) := by
    rw [ha, interior_translate, edgeComponents_translate]
    exact Finset.mem_image_of_mem _ hCT
  have hCP : transpose (translate a (interiorBlockCells T e.val.val)) ∈
      edgeComponents (diagramInterior P.cells) := by
    have h := Finset.mem_image_of_mem transpose hm
    rwa [← edgeComponents_transpose, ← diagramInterior_transpose, transpose_transpose] at h
  have hc := isConnectedSkew_component P.isSkew_cells.interior hCP
  have hfun : cellSchur D hD.1 =
      cellSchur (transpose (translate a (interiorBlockCells T e.val.val))) hc.1 := by
    apply schurInvolution_involutive.injective
    rw [schurInvolution_cellSchur hD, schurInvolution_cellSchur hc]
    have hsk := (interiorBlockCells_connected T e.val.val he).1
    rw [cellSchur_congr (transpose_transpose (D := translate a (interiorBlockCells T e.val.val)))
        (isSkew_transpose hc.1) (isSkew_translate a hsk),
      cellSchur_translate _ hsk a]
    exact selected_block_cellSchur (hD := isConnectedSkew_transpose hD) T e
  obtain ⟨b, hb⟩ := exists_originalSelectedBlock_of_component (hD := hD) P _ hCP hfun
  refine ⟨b, ?_⟩
  have h := congrArg transpose hb
  rwa [transpose_transpose] at h

end SelectedCoordinate
end SkewCornerDescent.Matrix
