/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowSelectedTranslation

/-!
# Source gap period from complete original windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
The whole window's actual profile supplies its selected count. Private cuts and complete
literal equality then produce the source gap period with shift equal to the difference of
the two actual counts. Neither count correspondence nor gap equality is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The whole original window occurrence count is the cardinality of its actual selected
component inventory, with every occurrence counted separately. -/
theorem originalWindow_selected_inventory_card {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    (selectedComponentInventory (hD := hD)
      (P.cells.filter fun x => lo ≤ content x ∧ content x < hi)).card =
      Fintype.card (OriginalWindowSelected (hD := hD) P lo hi) := by
  classical
  rw [selectedComponentInventory_interval_of_gaps P.cells lo hi hlo hhi,
    selectedComponentInventory_eq_original_image, Finset.filter_image,
    Finset.card_image_of_injective _ (originalSelectedBlock_cells_injective P)]
  exact (Fintype.card_subtype _).symm

/-- A complete literal window profile produces its original selected count. -/
theorem originalWindow_selected_count {n m : ℕ} (P : Profile n) (W : Profile m)
    (lo hi : ℤ) (u : ℤ × ℤ)
    (hW : P.cells.filter (fun x => lo ≤ content x ∧ content x < hi) = translate u W.cells)
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    Fintype.card (OriginalWindowSelected (hD := hD) P lo hi) =
      originalSelectedCount (hD := hD) W := by
  rw [← originalWindow_selected_inventory_card P lo hi hlo hhi, hW,
    selectedComponentInventory_translate W.cells W.isConnectedSkew_cells.1 u,
    Finset.card_image_of_injective _ (fun _ _ he => translate_injective u he),
    selectedComponentInventory_card]

/-- The normalized original source has no interior occurrence on either exterior boundary. -/
theorem originalProfile_interior_boundary_gaps {n : ℕ} (P : Profile n) :
    (∀ x ∈ diagramInterior P.cells, content x ≠ 0) ∧
      (∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) := by
  have hbound (x : ℤ × ℤ) (hx : x ∈ diagramInterior P.cells) :
      0 < content x ∧ content x < P.xi 0 := by
    have h := interior_content_strict P.isConnectedSkew_cells hx
    rw [Profile.minContent_cells, Profile.maxContent_cells] at h
    omega
  constructor <;> intro x hx <;> have h := hbound x hx <;> omega

/-- The literal source and complete window produce their exact overlapping actual gap
period. Only the two genuine private cuts and literal window placement are hypotheses. -/
theorem originalWindow_gap_period_from_profile {n m : ℕ} (P : Profile n) (W : Profile m)
    (c : SelectedCoordinate D hD) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (i j : Fin (originalSelectedCount (hD := hD) P))
    (hji : j.val = i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W))
    (hj : j.val + 1 < originalSelectedCount (hD := hD) P) :
    c.originalCompletedGap P i = c.originalCompletedGap P j := by
  have hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [hW]
    exact isSkew_translate u W.isConnectedSkew_cells.1
  have h0 := (originalProfile_interior_boundary_gaps P).1
  have hL := (originalProfile_interior_boundary_gaps P).2
  have hq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hq hx
  have hLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hLq hx
  have hcount := originalWindow_selected_count (hD := hD) P W 0 (P.xi 0 - q) u hW h0 hLq'
  apply originalWindow_internal_gap_period P c q v hv hprefix hwindow h0 hq' hLq' hL i j
    (by rw [hcount]; exact hji) hj

end SkewCornerDescent.Matrix.SelectedCoordinate
