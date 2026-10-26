/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowLowerWord
import SkewCornerDescent.Matrix.OriginalResponseClasses

/-!
# Complete window values belong to the original response class inventory

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The actual full inverse-response restriction supplies every window internal
value as a complete original source occurrence. Negative-only window counts
therefore still refer to actual source classes. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every internal source occurrence belongs to the complete original class inventory. -/
theorem originalInternalResidue_mem_classes {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    c.originalInternalResidue P i ∈ c.originalResponseClasses P := by
  classical
  change c.regularResidue (c.originalHessenbergResponse P
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
    ⟨i.val + 1, by have hi := i.isLt; omega⟩) ∈
      Finset.univ.image (fun j => c.regularResidue (c.originalHessenbergResponse P j j))
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- A complete literal first window supplies each of its actual internal
residues as a member of the full original source class set. -/
theorem originalWindow_internal_residue_mem_classes {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (v : ℤ × ℤ)
    (hW : W.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcut : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (i : Fin (originalSelectedCount (hD := hD) W - 1)) :
    c.originalInternalResidue W i ∈ c.originalResponseClasses P := by
  have hzero : ∀ x ∈ diagramInterior P.cells, content x ≠ 0 := by
    intro x hx hz
    have h := interior_content_strict P.isConnectedSkew_cells hx
    rw [P.minContent_cells] at h
    omega
  have hlast : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcut hx
  obtain ⟨hcount, hword⟩ := c.originalWindow_lower_restriction_internal_word P W q v hW hzero hlast
  have he := congrArg c.regularResidue (hword i)
  change c.originalInternalResidue W i = c.originalInternalResidue P
    ⟨i.val + (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W),
      by have hi := i.isLt; omega⟩ at he
  rw [he]
  exact c.originalInternalResidue_mem_classes P _

end SkewCornerDescent.Matrix.SelectedCoordinate
