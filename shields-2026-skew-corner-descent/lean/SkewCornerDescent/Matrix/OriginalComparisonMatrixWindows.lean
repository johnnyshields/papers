/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationInternalMatrices
import SkewCornerDescent.Matrix.OriginalClosureInternalMatrices
import SkewCornerDescent.Matrix.ConsecutiveMatrixWindows

/-!
# Finite full-matrix window cancellation in the actual comparison

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete copied matrix tails cancel before any residue periodicity is used.
The remaining starts are exactly the two actual prefixes, with all entries
and all normal jets retained, including the true closure join.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every full local matrix functional has exact finite prefix cancellation
in the literal three-profile comparison, in both ordinary closure directions.
No scalar-word substitute or copied-matrix hypothesis is used. -/
theorem originalComparison_matrix_window_cancellation {n m k qn : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (Q : Profile qn)
    (q : ℤ) (v u z w : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells ∨
      originalVerticalClosure P = translate w Q.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hPpos : 0 < originalSelectedCount (hD := hD) P) :
    ∃ hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      ∀ (L : ℕ) (hL : L ≤ originalSelectedCount (hD := hD) P)
        (β : Type*) [AddCommGroup β]
        (F : Matrix (Fin L) (Fin L) (PowerSeries (OtherField c.top)) → β) (a d : ℕ),
      let MA := (c.originalInternalResponseMatrix A).map c.normalSeries
      let MP := (c.originalInternalResponseMatrix P).map c.normalSeries
      let MQ := (c.originalInternalResponseMatrix Q).map c.normalSeries
      (a + d) • (∑ s, F (contiguousMatrixWindow MA L s)) -
        a • (∑ s, F (contiguousMatrixWindow MP L s)) -
        d • (∑ s, F (contiguousMatrixWindow MQ L s)) =
      (a + d) • (∑ s : Fin (originalSelectedCount (hD := hD) A -
        originalSelectedCount (hD := hD) P),
          F (contiguousMatrixWindow MA L ⟨s.val, by have := s.isLt; omega⟩)) -
        d • (∑ s : Fin (originalSelectedCount (hD := hD) P),
          F (contiguousMatrixWindow MQ L ⟨s.val, by have := s.isLt; omega⟩)) := by
  obtain ⟨hAP, _, hcopyA⟩ := c.originalAmalgamation_lower_internal_matrix
    P W A q v u z hq hv hwindow hW hA hcutq hcutLq
  obtain ⟨hCQ, hcopyQ⟩ := c.originalClosure_lower_internal_matrix P Q w hQ
  refine ⟨hAP, hCQ, fun L hL β _ F a d => ?_⟩
  dsimp only
  have hsA := contiguousMatrixWindow_sum_copy_tail
    (N := originalSelectedCount (hD := hD) A - 1)
    (B := originalSelectedCount (hD := hD) P - 1)
    (T := originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P)
    (L := L) (by omega) (by omega)
    ((c.originalInternalResponseMatrix A).map c.normalSeries)
    ((c.originalInternalResponseMatrix P).map c.normalSeries) hcopyA F
  have hsQ := contiguousMatrixWindow_sum_copy_tail
    (N := originalSelectedCount (hD := hD) Q - 1)
    (B := originalSelectedCount (hD := hD) P - 1)
    (T := originalSelectedCount (hD := hD) P)
    (L := L) (by omega) (by omega)
    ((c.originalInternalResponseMatrix Q).map c.normalSeries)
    ((c.originalInternalResponseMatrix P).map c.normalSeries) hcopyQ F
  rw [hsA, hsQ]
  simp only [nsmul_add, add_nsmul]
  abel

end SkewCornerDescent.Matrix.SelectedCoordinate
