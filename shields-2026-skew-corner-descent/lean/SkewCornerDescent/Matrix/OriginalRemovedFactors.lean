/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalMultiplicity
import SkewGluing.CofactorAssembly

/-!
# Complete original removed determinant factors

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-words`). The identities are polynomial identities before
normal substitution. They retain all nonselected complete blocks and the actual proper
minor of every selected occurrence, including repeated equal components. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The complete removed determinant is the product of its actual remaining diagonal blocks.
No inverse entry is discarded from an upper response by this determinant identity. -/
theorem originalRemovedMatrix_det_product {n : ℕ} (P : Profile n) :
    (originalRemovedMatrix (hD := hD) P).det =
      ∏ b : OriginalBlocks P, (originalRemovedDiagonal (hD := hD) P b).det := by
  classical
  rw [(originalRemovedMatrix_blockTriangular_fst (hD := hD) P).det_fintype]
  apply Finset.prod_congr rfl
  intro b _
  have he := Matrix.det_reindex_self (originalRemovedFiberEquiv (hD := hD) P b).symm
    ((originalRemovedMatrix (hD := hD) P).toSquareBlock Sigma.fst b)
  rw [originalRemovedDiagonal_reindex (hD := hD) P b] at he
  exact he.symm

/-- Every selected occurrence removes the same actual unsigned top cofactor, independently
of the literal realization of the selected connected Schur prime. -/
theorem originalRemovedDiagonal_selected_cofactor {n : ℕ} (P : Profile n)
    (b : OriginalBlocks P) (hs : originalBlockSelected (hD := hD) P b) :
    (originalRemovedDiagonal (hD := hD) P b).det =
      cellSchur (diagramInterior D) hD.1.interior := by
  have hi := originalBlockSelected_nonempty (hD := hD) P b hs
  let Q := interiorBlockProfile P b.val hi
  have he : cellSchur Q.cells Q.isSkew_cells = cellSchur D hD.1 := by
    rw [cellSchur_cells]
    exact originalSelectedProfile_schur P ⟨b, hs⟩
  have hcofactor := interiorSchur_eq_of_cellSchur_eq Q.isConnectedSkew_cells hD he
  rw [originalRemovedDiagonal_det_selected (hD := hD) P b hs,
    originalSelectedMinor_eq_profile P b.val hi]
  change betaDet (fun j => Q.xi j.succ) (fun j => Q.zeta j.castSucc) = _
  rw [Q.minorDet_eq_interiorSchur, hcofactor]

/-- The full removed determinant separates the repeated selected proper minor from every
nonselected full original block. Empty blocks remain present with determinant one. -/
theorem originalRemovedMatrix_det_inventory {n : ℕ} (P : Profile n) :
    (originalRemovedMatrix (hD := hD) P).det =
      cellSchur (diagramInterior D) hD.1.interior ^ originalSelectedCount (hD := hD) P *
        ∏ b ∈ Finset.univ.filter (fun b : OriginalBlocks P =>
          ¬ originalBlockSelected (hD := hD) P b), originalBlockPolynomial P b := by
  classical
  rw [originalRemovedMatrix_det_product (hD := hD) P]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (OriginalBlocks P)) (originalBlockSelected (hD := hD) P)]
  congr 1
  · have hf : (Finset.univ.filter (originalBlockSelected (hD := hD) P)).card =
        originalSelectedCount (hD := hD) P := by
      simp only [originalSelectedCount, OriginalSelectedBlocks, Fintype.card_subtype]
    rw [← hf]
    calc
      _ = ∏ _b ∈ Finset.univ.filter (originalBlockSelected (hD := hD) P),
          cellSchur (diagramInterior D) hD.1.interior :=
        Finset.prod_congr rfl (fun b hb =>
          originalRemovedDiagonal_selected_cofactor P b (Finset.mem_filter.mp hb).2)
      _ = _ := Finset.prod_const _
  · apply Finset.prod_congr rfl
    intro b hb
    exact originalRemovedDiagonal_det_nonselected (hD := hD) P b (Finset.mem_filter.mp hb).2

end SkewCornerDescent.Matrix.SelectedCoordinate
