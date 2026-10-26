/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ClosureResidueReflection
import SkewCornerDescent.Matrix.OriginalHessenbergInventory

/-!
# Full actual cofactor and component inventories after transposition

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The complete corner determinant transports as the actual full interior Schur
product. Prime multiplicity, component spans, and every column component then
supply the corresponding transposed row-chart premises. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Full interior Schur products respect every transposed profile presentation. -/
theorem transpose_profile_corner_schur {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) :
    (jtMatrix (fun j : Fin m => T.xi j.succ) (fun j => T.zeta j.castSucc)).det =
      schurInvolution
        ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det) := by
  change betaDet (fun j : Fin m => T.xi j.succ) (fun j => T.zeta j.castSucc) =
    schurInvolution (betaDet (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc))
  rw [T.minorDet_eq_interiorSchur, P.minorDet_eq_interiorSchur,
    schurInvolution_skew_cellSchur]
  have he : transpose (diagramInterior P.cells) = translate a (diagramInterior T.cells) := by
    rw [← diagramInterior_transpose, ha, interior_translate]
  rw [cellSchur_congr he (isSkew_transpose P.isSkew_cells.interior)
      (isSkew_translate a T.isSkew_cells.interior),
    cellSchur_translate (diagramInterior T.cells) T.isSkew_cells.interior a]

/-- Complete corner powers transport with the unchanged copy count. -/
theorem transpose_profile_corner_power {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) (Λ : Lambda) (b : ℕ)
    (h : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b) :
    (jtMatrix (fun j : Fin m => T.xi j.succ)
      (fun j => T.zeta j.castSucc)).det = schurInvolution Λ ^ b := by
  rw [transpose_profile_corner_schur P T a ha, h, map_pow]

/-- The selected generator index is intrinsic to the whole selected diagram
and is unchanged by any produced transposed coordinate. -/
theorem transposed_selectedCoordinate_top {D : Diagram} {hD : IsConnectedSkew D}
    (c : Matrix.SelectedCoordinate D hD)
    (d : Matrix.SelectedCoordinate (transpose D) (isConnectedSkew_transpose hD)) :
    d.top = c.top := by
  have h := d.span_eq
  rw [span_transpose, ← c.span_eq] at h
  exact PNat.eq h

/-- Selected prime multiplicity in every original polynomial is preserved
on the actual whole transposed selected diagram. -/
theorem transposed_selected_primeOrder {D : Diagram} {hD : IsConnectedSkew D}
    (f : Lambda) :
    Matrix.primeOrder (cellSchur (transpose D) (isSkew_transpose hD.1)) (schurInvolution f) =
      Matrix.primeOrder (cellSchur D hD.1) f := by
  rw [← schurInvolution_cellSchur hD, primeOrder_schurInvolution]

/-- The complete maximal-component bound transports through the actual
normalizing translation of the whole source profile. -/
theorem transpose_profile_component_span {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells) (N : ℕ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N) :
    ∀ C ∈ edgeComponents (diagramInterior T.cells), span C ≤ N := by
  intro C hC
  have hm : translate a C ∈ edgeComponents (diagramInterior (transpose P.cells)) := by
    rw [ha, interior_translate, edgeComponents_translate]
    exact Finset.mem_image_of_mem _ hC
  have h := corner_span_bound_transpose P.cells N hmax _ hm
  rwa [span_translate] at h

/-- Every actual all-column corner component supplies a genuine row component
on the normalized transposed source; no selected-only restriction is used. -/
theorem transpose_profile_all_columns_rows {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells)
    (hcol : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.snd).card = 1) :
    ∀ C ∈ edgeComponents (diagramInterior T.cells), (C.image Prod.fst).card = 1 := by
  intro C hC
  have hm : translate a C ∈ edgeComponents (diagramInterior (transpose P.cells)) := by
    rw [ha, interior_translate, edgeComponents_translate]
    exact Finset.mem_image_of_mem _ hC
  have h := all_column_corner_transpose_rows P.cells hcol _ hm
  have he : (translate a C).image Prod.fst =
      (C.image Prod.fst).image (fun r => r + a.1) := by
    simp only [SkewGluing.translate, Finset.image_image, Function.comp_def, Prod.fst_add]
  rw [he, Finset.card_image_of_injective _ (fun r s h => add_right_cancel h)] at h
  exact h

end SkewCornerDescent
