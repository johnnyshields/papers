/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationInventory
import SkewCornerDescent.Matrix.OriginalWindowLowerWord

/-!
# The actual full internal response word of the amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete literal
end windows produce both copies of the original response word. The actual selected
inventory determines their offset. Full normal-dependent inverse corrections are retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The amalgamation has the source prefix followed by its full internal word. Its count,
rank shift, and full inverse correspondence are produced from the literal parent cells. -/
theorem originalAmalgamation_internal_word {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W) :
    ∃ hcount : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hinventory : originalSelectedCount (hD := hD) A +
      originalSelectedCount (hD := hD) W = 2 * originalSelectedCount (hD := hD) P,
      ∀ i : Fin (originalSelectedCount (hD := hD) A - 1),
        c.originalInternalResponse A i =
          if hi : i.val < originalSelectedCount (hD := hD) P -
              originalSelectedCount (hD := hD) W then
            c.originalInternalResponse P ⟨i.val, by omega⟩
          else c.originalInternalResponse P
            ⟨i.val - (originalSelectedCount (hD := hD) P -
              originalSelectedCount (hD := hD) W), by have := i.isLt; omega⟩ := by
  classical
  have hinventory := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v u z hv hwindow hW hA
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  have hupper : P.cells = translate (u - v)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate]
    have he : v + (u - v) = u := by abel
    rw [he]
    exact hright.symm
  obtain ⟨hc, hlast⟩ := c.originalWindow_lower_restriction_internal_word A P q u
    hleft.symm (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1)
  obtain ⟨_, hfirst⟩ := c.originalWindow_restriction_internal_word A P q (u - v)
    hupper (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2)
  refine ⟨hc, hinventory, fun i => ?_⟩
  have hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P =
      originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W := by omega
  split_ifs with hi
  · have hb : i.val < originalSelectedCount (hD := hD) P - 1 := by omega
    exact (hfirst ⟨i.val, hb⟩).symm
  · let j : Fin (originalSelectedCount (hD := hD) P - 1) :=
      ⟨i.val - (originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W), by have hii := i.isLt; omega⟩
    have hr := hlast j
    have hij : (⟨j.val + (originalSelectedCount (hD := hD) A -
        originalSelectedCount (hD := hD) P), by have hj := j.isLt; omega⟩ :
          Fin (originalSelectedCount (hD := hD) A - 1)) = i := by
      apply Fin.ext
      change j.val + (originalSelectedCount (hD := hD) A -
        originalSelectedCount (hD := hD) P) = i.val
      dsimp only [j]
      rw [hshift]
      omega
    rw [hij] at hr
    exact hr.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
