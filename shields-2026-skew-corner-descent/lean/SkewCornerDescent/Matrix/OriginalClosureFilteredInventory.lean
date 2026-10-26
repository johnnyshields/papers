/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFilteredLinearInventory
import SkewCornerDescent.Matrix.OriginalClosureBoundedFrontier
import SkewCornerDescent.Matrix.OriginalClosureResponseWord

/-!
# Complete filtered cyclic inventory of the actual horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The literal
closure response word and gap projection share their original positional starts.
One complete source inventory and every closure-cycle start are retained, with
both true boundary caps excluded only by their strict completion bounds.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual doubled internal word preserves the geometric filter at every
start before its complete cyclic inventory is split off. -/
theorem originalHorizontalClosure_filtered_linear_inventory {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) Q)]
    (j : ℕ) (hj : j ≤ originalSelectedCount (hD := hD) P) (M : ℤ) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    let g := fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)
    let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
    filteredLinearInverseWindowSum (c.originalInternalResidue Q)
      (fun z => c.originalCompletedGap Q ((ZMod.finEquiv _).symm z)) j M =
      filteredLinearInverseWindowSum (c.originalInternalResidue P) g j M +
        filteredInverseWindowSum (completeResponseCycle (c.originalInternalResidue P) S) g j M := by
  classical
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
  let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
  let g := fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)
  have hlen : originalSelectedCount (hD := hD) Q - 1 =
      2 * originalSelectedCount (hD := hD) P - 1 := by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
  have hw (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
      c.originalInternalResidue Q i = completeResponseCycle (c.originalInternalResidue P) S
        ((finCongr hlen i).val : ZMod (originalSelectedCount (hD := hD) P)) := by
    change c.regularResidue (c.originalInternalResponse Q i) = _
    rw [c.originalHorizontalClosure_internal_response_word P Q v hQ hB i,
      completeResponseCycle_double]
    simp only [finCongr_apply, Fin.val_cast]
    split_ifs <;> rfl
  have hstarts : originalSelectedCount (hD := hD) Q - 1 + 1 - j =
      2 * originalSelectedCount (hD := hD) P - 1 + 1 - j := congrArg (fun l => l + 1 - j) hlen
  let fnew := fun s : Fin (2 * originalSelectedCount (hD := hD) P - 1 + 1 - j) =>
    if windowSum g 1 j (s.val : ZMod (originalSelectedCount (hD := hD) P)) = M then
      ∏ a : Fin j, (completeResponseCycle (c.originalInternalResidue P) S
        ((s.val + a.val : ℕ) : ZMod (originalSelectedCount (hD := hD) P)))⁻¹ else 0
  have he : filteredLinearInverseWindowSum (c.originalInternalResidue Q)
      (fun z => c.originalCompletedGap Q ((ZMod.finEquiv _).symm z)) j M =
      filteredLinearInverseWindowSum
        (fun i : Fin (2 * originalSelectedCount (hD := hD) P - 1) =>
          completeResponseCycle (c.originalInternalResidue P) S
            (i.val : ZMod (originalSelectedCount (hD := hD) P))) g j M := by
    unfold filteredLinearInverseWindowSum
    change _ = ∑ s, fnew s
    rw [← (finCongr hstarts).sum_comp fnew]
    apply Finset.sum_congr rfl
    intro s _
    have hgap := c.originalHorizontalClosure_completed_gap_window_at P Q v hQ j
      (s.val : ZMod (originalSelectedCount (hD := hD) Q))
    simp only [map_natCast] at hgap
    rw [hgap]
    dsimp only [fnew]
    simp only [finCongr_apply, Fin.val_cast]
    split_ifs
    · apply Finset.prod_congr rfl
      intro a _
      have hp := hw ⟨s.val + a.val, by have := s.isLt; have := a.isLt; omega⟩
      simpa only [finCongr_apply, Fin.val_cast] using congrArg Inv.inv hp
    · rfl
  dsimp only
  rw [he]
  exact filteredLinearInverseWindowSum_complete_double (c.originalInternalResidue P) S g j hj M

/-- Complete original interval elimination gives the actual filtered closure
cycle, under the bound supplied by the source maximum. -/
theorem originalHorizontalClosure_filtered_interval_inventory {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) (hj : 2 ≤ j) (hjB : j ≤ originalSelectedCount (hD := hD) P) (M : ℤ)
    (hbound : ∀ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j z ≤ M)
    (K : ℕ+) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    c.originalFilteredIntervalInventory Q j K = c.originalFilteredIntervalInventory P j K +
      filteredInverseWindowSum
        (completeResponseCycle (c.originalInternalResidue P)
          (c.regularResidue (c.originalHessenbergResponse Q middle middle)))
        (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) j M := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by omega⟩
  have hboundQ : ∀ z : ZMod (originalSelectedCount (hD := hD) Q),
      windowSum (fun s => c.originalCompletedGap Q ((ZMod.finEquiv _).symm s)) 1 j z ≤ M := by
    intro z
    rw [c.originalHorizontalClosure_completed_gap_window_at P Q v hQ]
    exact hbound _
  have hj : j - 1 + 1 = j := by omega
  have hP := c.originalFilteredIntervalInventory_eq_linear P hB (j - 1) (by omega)
    (by omega) M (by simpa only [hj] using hbound) K hKeq
  have hQ' := c.originalFilteredIntervalInventory_eq_linear Q hBQ (j - 1) (by omega)
    (by omega) M (by simpa only [hj] using hboundQ) K hKeq
  simp only [hj] at hP hQ'
  rw [hP, hQ']
  exact c.originalHorizontalClosure_filtered_linear_inventory P Q v hQ hB j hjB M

end SkewCornerDescent.Matrix.SelectedCoordinate
