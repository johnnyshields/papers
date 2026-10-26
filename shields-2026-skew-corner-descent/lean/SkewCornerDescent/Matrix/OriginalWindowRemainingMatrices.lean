/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRemainingEquiv

/-!
# Full removed source matrices of complete equal windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). All remaining
positions are reindexed at once. The equality includes couplings between different
selected proper minors, every unselected block, and the actual empty unit pivots.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every remaining original position in the complete whole-block window inventory. -/
abbrev OriginalWholeWindowRemaining {n : ℕ} (P : Profile n) (lo hi : ℤ) :=
  Σ b : OriginalWholeWindowBlocks P lo hi, Fin (originalRemovedSize (hD := hD) P b.val)

/-- Literal complete windows produce the entire remaining matrix equivalence. -/
theorem originalWindow_remaining_matrix_equiv {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    ∃ e : OriginalWholeWindowRemaining (hD := hD) P lo (hi - q) ≃
        OriginalWholeWindowRemaining (hD := hD) P (lo + q) hi,
      (∀ i, originalResponseRows P ⟨(e i).1.val, (e i).2⟩ =
          originalResponseRows P ⟨i.1.val, i.2⟩ + q ∧
        originalResponseCols P ⟨(e i).1.val, (e i).2⟩ =
          originalResponseCols P ⟨i.1.val, i.2⟩ + q) ∧
      ∀ i j, originalRemovedMatrix P ⟨(e i).1.val, (e i).2⟩
          ⟨(e j).1.val, (e j).2⟩ = originalRemovedMatrix P ⟨i.1.val, i.2⟩ ⟨j.1.val, j.2⟩ := by
  classical
  obtain ⟨b, hb⟩ := originalWindow_remaining_orderIso (hD := hD) P lo hi q v hv hwindow
    hlo hloq hhiq hhi
  let t := fun i => (hb i).2.choose
  let e := (Equiv.sigmaCongrRight t).trans
    (Equiv.sigmaCongrLeft (β := fun i : OriginalWholeWindowBlocks P (lo + q) hi =>
      Fin (originalRemovedSize (hD := hD) P i.val)) b.toEquiv)
  have hend : ∀ i : OriginalWholeWindowRemaining (hD := hD) P lo (hi - q),
      originalResponseRows P ⟨(e i).1.val, (e i).2⟩ =
          originalResponseRows P ⟨i.1.val, i.2⟩ + q ∧
        originalResponseCols P ⟨(e i).1.val, (e i).2⟩ =
          originalResponseCols P ⟨i.1.val, i.2⟩ + q := by
    intro i
    exact (hb i.1).2.choose_spec i.2
  refine ⟨e, hend, ?_⟩
  intro i j
  have hr := (hend i).1
  have hc := (hend j).2
  change hh (originalResponseRows P ⟨(e i).1.val, (e i).2⟩ -
      originalResponseCols P ⟨(e j).1.val, (e j).2⟩) =
    hh (originalResponseRows P ⟨i.1.val, i.2⟩ - originalResponseCols P ⟨j.1.val, j.2⟩)
  rw [hr, hc]
  congr 1
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
