/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowFilteredPeriod
import SkewCornerDescent.Matrix.OriginalAmalgamationMaximalGaps
import SkewCornerDescent.Matrix.OriginalAmalgamationCyclicInventory

/-!
# The actual amalgamation's full-period filtered cyclic inventory

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Complete
literal windows supply the period response cycle and its true gap cycle. Every
period gap window has the literal displacement span, so the actual bin filter
commutes with the complete extra-start inventory. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full-period union inventory is one source inventory plus the complete
period-cycle inventory, filtered by the actual prefix gap cycle. -/
theorem originalAmalgamation_filtered_interval_inventory {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) [NeZero j] (hj : 2 ≤ j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ) (hqM : q ≤ M)
    (hbound : ∀ x : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j x ≤ M)
    (K : ℕ+) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    c.originalFilteredIntervalInventory A j K = c.originalFilteredIntervalInventory P j K +
      filteredInverseWindowSum
        (finiteWordCycle (n := j) (c.originalInternalResidue P) (by omega))
        (finiteWordCycle (n := j) (c.originalCompletedGap P) (by omega)) j M := by
  subst j
  let j := originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W
  classical
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  have hinv := originalAmalgamation_selected_inventory (hD := hD) P W A q v u z
    hv hwindow hW hA
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have hBA : 0 < originalSelectedCount (hD := hD) A := by omega
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨by omega⟩
  let : NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :=
    ⟨by omega⟩
  have hboundA := c.originalAmalgamation_completed_gap_bound P W A q v u z hq hv hwindow
    hW hA hcutq' hcutLq' hC j (by omega) rfl M hqM hbound
  have hP := c.originalWindow_filtered_inventory_at_period_length P W q z v hv hW.symm
    hwindow hcutq' hcutLq' hB j hj rfl M hbound K hKeq
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u
    hq hv hwindow hA
  have hlower : A.cells.filter (fun x => 0 ≤ content x ∧ content x < A.xi 0 - q) =
      translate (-u) P.cells := by
    apply translate_injective u
    rw [hleft, translate_translate, add_neg_cancel, translate_zero]
  have hupper : A.cells.filter (fun x => q ≤ content x ∧ content x < A.xi 0) =
      translate v (A.cells.filter fun x => 0 ≤ content x ∧ content x < A.xi 0 - q) := by
    apply translate_injective u
    rw [hright, translate_translate, add_comm u v, ← translate_translate, hleft]
  have hcuts := originalAmalgamation_private_end_cuts P A q v u
    hq hv hwindow hA hcutq' hcutLq'
  have hA' := c.originalWindow_filtered_inventory_at_period_length A P q (-u) v hv hlower
    hupper (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.1)
    hBA j hj (by omega) M hboundA K hKeq
  have hlinear := c.originalAmalgamation_linear_inventory P W A q v u z hq hv
    hwindow hW hA hcutq hcutLq hC (by omega) j (by omega)
  dsimp only at hlinear
  have hlinear' : linearInverseWindowSum (c.originalInternalResidue A) j =
      linearInverseWindowSum (c.originalInternalResidue P) j + inverseWindowSum
        (finiteWordCycle (n := j) (c.originalInternalResidue P) (by omega)) j := by
    exact hlinear
  have hgap := c.originalWindow_period_gap_windows P W q z v hv hW.symm hwindow
    hcutq' hcutLq' hC j rfl
  have hfilter : filteredInverseWindowSum
      (finiteWordCycle (n := j) (c.originalInternalResidue P) (by omega))
      (finiteWordCycle (n := j) (c.originalCompletedGap P) (by omega)) j M =
      if q = M then inverseWindowSum
        (finiteWordCycle (n := j) (c.originalInternalResidue P) (by omega)) j else 0 := by
    unfold filteredInverseWindowSum
    simp_rw [hgap]
    split_ifs
    · rfl
    · exact Finset.sum_const_zero
  rw [hA', hP, hfilter]
  split_ifs
  · exact hlinear'
  · simp only [zero_add]

end SkewCornerDescent.Matrix.SelectedCoordinate
