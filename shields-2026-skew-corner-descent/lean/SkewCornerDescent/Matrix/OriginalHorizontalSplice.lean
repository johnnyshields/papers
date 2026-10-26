/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ComponentElimination
import SkewGluing.EmptyHorizontal

/-!
# Literal geometric cap-splice distance

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). The splice uses the actual horizontal empty
mark, with the last selected component translated by its actual displacement. The cap sum
is derived from these cells and is not the definition of the splice distance. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

attribute [local instance] Classical.propDecidable

/-- The actual least content of the complete original component is its last column endpoint. -/
theorem interiorBlockCells_minContent {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    minContent (interiorBlockCells P i) = P.zeta (interiorBlockLast P i).castSucc := by
  unfold interiorBlockCells
  rw [interiorSliceCells_eq_translate P _ _ _ (interiorBlock_slice_same P i)
    (interiorBlock_first_nonempty P i hi)]
  change minContent (translate
    (((interiorBlockFirst P i : ℕ) : ℤ),
      P.zeta (interiorSliceIndex (interiorBlockFirst P i).val (interiorBlockLength P i)
        (interiorBlock_interval_bound P i) (Fin.last _)).castSucc + (interiorBlockFirst P i : ℕ))
    (interiorBlockProfile P i hi).cells) = _
  rw [minContent_translate (interiorBlockProfile P i hi).isConnectedSkew_cells.2.1]
  rw [Profile.minContent_cells, originalBlockInterval_last]
  simp only [content]
  ring

/-- The complete literal horizontal closure is the actual two-copy empty composition. -/
def originalHorizontalClosure {n : ℕ} (P : Profile n) : Diagram :=
  (emptyMarkH P.cells).compose (horizontalRow 2)

/-- The closure is an actual connected skew diagram, rather than formal concatenation data. -/
theorem originalHorizontalClosure_connected {n : ℕ} (P : Profile n) :
    IsConnectedSkew (originalHorizontalClosure P) :=
  (emptyMarkH_isLegal P.isConnectedSkew_cells).isConnectedSkew_compose_horizontalRow_all (by decide)

/-- Both complete interior copies are retained by the actual empty horizontal attachment. -/
theorem originalHorizontalClosure_interior {n : ℕ} (P : Profile n) :
    diagramInterior (originalHorizontalClosure P) =
      diagramInterior P.cells ∪ translate (vH P.cells) (diagramInterior P.cells) := by
  unfold originalHorizontalClosure
  rw [(emptyMarkH_isLegal P.isConnectedSkew_cells).interior_compose_horizontalRow_all (by decide)]
  simp only [show (2 : ℕ) = (0 + 1) + 1 from rfl, Finset.range_add_one,
    Finset.range_zero, Finset.biUnion_insert, Finset.biUnion_empty, Nat.cast_zero,
    Nat.cast_one, zero_smul, one_smul, emptyMarkH, SkewGluing.translate_zero,
    Finset.empty_union, Finset.union_comm]

/-- The actual complete unshifted component remains in the closure's interior. -/
theorem originalHorizontalClosure_first_subset {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorBlockCells P i ⊆ diagramInterior (originalHorizontalClosure P) := by
  rw [originalHorizontalClosure_interior]
  exact (interiorSliceCells_subset P _ _ _).trans Finset.subset_union_left

/-- The actual translated component remains in the closure's interior, with all its cells. -/
theorem originalHorizontalClosure_second_subset {n : ℕ} (P : Profile n) (i : Fin n) :
    translate (vH P.cells) (interiorBlockCells P i) ⊆
      diagramInterior (originalHorizontalClosure P) := by
  rw [originalHorizontalClosure_interior]
  intro x hx
  apply Finset.mem_union_right
  apply mem_translate.mpr
  exact interiorSliceCells_subset P _ _ _ (mem_translate.mp hx)

/-- The actual empty displacement has the parent profile's generator span. -/
theorem originalHorizontalDisplacement_content {n : ℕ} (P : Profile n) :
    content (vH P.cells) = P.xi 0 - P.zeta (Fin.last n) := by
  have h := (show (emptyMarkH P.cells).IsLegalEmpty from
    ⟨emptyMarkH_isLegal P.isConnectedSkew_cells, rfl⟩).span_eq
  change (span P.cells : ℤ) = content (vH P.cells) at h
  rw [P.span_cells_eq_topVar, P.topVar_coe] at h
  rw [P.zeta_last]
  omega

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Geometric splice distance from the two actual component diagrams at the horizontal join. -/
def originalCapSpliceDistance {n : ℕ} (P : Profile n)
    (first last : OriginalSelectedBlocks (hD := hD) P) : ℤ :=
  minContent (translate (vH P.cells) (interiorBlockCells P last.val.val)) -
    minContent (interiorBlockCells P first.val.val)

/-- The actual geometric splice has the literal parent-distance-minus-selected-band formula. -/
theorem originalCapSpliceDistance_eq {n : ℕ} (P : Profile n)
    (first last : OriginalSelectedBlocks (hD := hD) P) :
    originalCapSpliceDistance P first last =
      P.xi 0 - P.zeta (Fin.last n) +
        P.zeta (interiorBlockLast P last.val.val).castSucc -
        P.zeta (interiorBlockLast P first.val.val).castSucc := by
  unfold originalCapSpliceDistance
  rw [minContent_translate (interiorBlockCells_connected P last.val.val
      (originalBlockSelected_nonempty P last.val last.property)).2.1,
    interiorBlockCells_minContent P last.val.val
      (originalBlockSelected_nonempty P last.val last.property),
    interiorBlockCells_minContent P first.val.val
      (originalBlockSelected_nonempty P first.val first.property),
    originalHorizontalDisplacement_content]
  ring

/-- The true cap sum is the selected top plus the actual translated-component splice distance. -/
theorem originalCapSpliceDistance_cap_sum {n : ℕ} (P : Profile n)
    (first last : OriginalSelectedBlocks (hD := hD) P) :
    (c.top : ℤ) + originalCapSpliceDistance P first last =
      originalFirstCapDistance P first + originalLastCapDistance P last := by
  rw [originalCapSpliceDistance_eq]
  have ht := c.originalSelected_endpoint_distance P last
  unfold originalFirstCapDistance originalLastCapDistance
  omega

end SelectedCoordinate
end SkewCornerDescent.Matrix
