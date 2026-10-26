/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowSelected
import SkewCornerDescent.Matrix.OriginalLiteralWindowBounds

/-!
# Complete selected inventory of a literal window profile

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). A complete
literal window profile supplies all of its selected occurrences, with no omitted boundary
component. Its cells produce the target band and private boundary facts. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A complete literal window profile produces its whole selected occurrence order. -/
theorem originalLiteralWindow_profile_selected_orderIso {n m : ℕ}
    (P : Profile n) (Q : Profile m) (lo hi : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    ∃ e : OriginalWindowSelected (hD := hD) P lo hi ≃o OriginalSelectedBlocks (hD := hD) Q,
      ∀ b, interiorBlockCells Q (e b).val.val =
        translate v (interiorBlockCells P b.val.val.val) := by
  classical
  let q := content v
  have hbounds := originalLiteralWindow_profile_bounds P Q lo hi v hwindow hlo hhi
  have hband (x : ℤ × ℤ) (hx : x ∈ Q.cells) :
      lo + q ≤ content x ∧ content x < hi + q := hbounds.1 x hx
  have hfilter : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) = Q.cells := by
    apply Finset.filter_eq_self.mpr
    exact hband
  have hcuts : (∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q) ∧
      (∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q) := hbounds.2
  obtain ⟨e, he⟩ := originalLiteralWindow_selected_orderIso (hD := hD) P Q lo hi q v rfl
    (by rw [hfilter]; exact hwindow) hlo hcuts.1 hhi hcuts.2
  have hall (b : OriginalSelectedBlocks (hD := hD) Q) :
      ∀ x ∈ interiorBlockCells Q b.val.val, lo + q ≤ content x ∧ content x < hi + q := by
    intro x hx
    have hI := component_subset (interiorBlockCells_mem_components Q b.val.val
      (originalBlockSelected_nonempty Q b.val b.property)) hx
    exact hband x (Finset.mem_filter.mp hI).1
  let f : OriginalWindowSelected (hD := hD) Q (lo + q) (hi + q) ≃o
      OriginalSelectedBlocks (hD := hD) Q :=
    { toFun := Subtype.val
      invFun := fun b => ⟨b, hall b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact ⟨e.trans f, he⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
