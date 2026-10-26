/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowCoreWords
import SkewCornerDescent.Matrix.OriginalAmalgamationWord

/-!
# Complete actual selected-core word of an amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The two complete literal end windows produce the source prefix followed by
its entire selected-core word. No response-class quotient replaces a position.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual amalgamation carries the complete source prefix and the complete
source proper-core word, with both canonical endpoint occurrences retained. -/
theorem originalAmalgamation_core_word {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hcount : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hinventory : originalSelectedCount (hD := hD) A +
        originalSelectedCount (hD := hD) W = 2 * originalSelectedCount (hD := hD) P,
    ∀ i : Fin (originalSelectedCount (hD := hD) A),
      (c.originalSelectedCoreLeft A i =
        if hi : i.val < originalSelectedCount (hD := hD) P -
            originalSelectedCount (hD := hD) W then
          c.originalSelectedCoreLeft P ⟨i.val, by omega⟩
        else c.originalSelectedCoreLeft P
          ⟨i.val - (originalSelectedCount (hD := hD) P -
            originalSelectedCount (hD := hD) W), by have := i.isLt; omega⟩) ∧
      (c.originalSelectedCoreRight A i =
        if hi : i.val < originalSelectedCount (hD := hD) P -
            originalSelectedCount (hD := hD) W then
          c.originalSelectedCoreRight P ⟨i.val, by omega⟩
        else c.originalSelectedCoreRight P
          ⟨i.val - (originalSelectedCount (hD := hD) P -
            originalSelectedCount (hD := hD) W), by have := i.isLt; omega⟩) := by
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
  obtain ⟨hc, hlast⟩ := c.originalWindow_lower_core_words A P q u
    hleft.symm (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1)
  obtain ⟨_, hfirst⟩ := c.originalWindow_upper_core_words A P q (u - v)
    hupper (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2)
  refine ⟨hc, hinventory, fun i => ?_⟩
  have hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P =
      originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W := by omega
  by_cases hi : i.val < originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W
  · simp only [dite_eq_left hi]
    let j : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by omega⟩
    have h := hfirst j
    have he : (⟨j.val, by have := j.isLt; omega⟩ :
        Fin (originalSelectedCount (hD := hD) A)) = i := Fin.ext rfl
    rw [he] at h
    exact ⟨h.1.symm, h.2.symm⟩
  · simp only [dite_eq_right hi]
    let j : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨i.val - (originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W), by have := i.isLt; omega⟩
    have h := hlast j
    have he : (⟨j.val + (originalSelectedCount (hD := hD) A -
        originalSelectedCount (hD := hD) P), by have := j.isLt; omega⟩ :
        Fin (originalSelectedCount (hD := hD) A)) = i := by
      apply Fin.ext
      dsimp only [j]
      rw [hshift]
      omega
    rw [he] at h
    exact ⟨h.1.symm, h.2.symm⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
