/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFilteredLinearInventory
import SkewCornerDescent.Matrix.OriginalWindowPeriodDistance
import SkewCornerDescent.FinitePeriodicWords
import SkewCornerDescent.Matrix.OriginalClosureGapPeriod

/-!
# Filtering the actual full internal period by its literal displacement

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Every
noncrossing full-period gap window has the actual translation sum. Thus its
geometric filter is constant on the complete finite linear inventory, even when
the completed source gap cycle is not periodic. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A full noncrossing internal-period gap window has precisely the literal
translation sum, produced by matching its two actual selected endpoint ranks. -/
theorem originalWindow_internal_gap_window_sum {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) (hj : 0 < j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (start : ℕ) (hstart : start < originalSelectedCount (hD := hD) P - j) :
    windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      1 j (start : ZMod (originalSelectedCount (hD := hD) P)) = q := by
  let i : Fin (originalSelectedCount (hD := hD) P) := ⟨start, by omega⟩
  let k : Fin (originalSelectedCount (hD := hD) P) := ⟨start + j - 1, by omega⟩
  let last : Fin (originalSelectedCount (hD := hD) P) := ⟨start + j, by omega⟩
  have hdist := c.originalWindow_selected_period_distance P W q u v hv hW hwindow
    hcutq hcutLq i last (by dsimp only [i, last]; omega)
  have he := c.originalCompletedGap_cyclic_internal_window P i k
    (by change start ≤ start + j - 1; omega)
    (by change start + j - 1 + 1 < originalSelectedCount (hD := hD) P; omega)
  have hk : k.succ = last.castSucc := by
    apply Fin.ext
    change start + j - 1 + 1 = start + j
    omega
  have hlen : k.val - i.val + 1 = j := by dsimp only [i, k]; omega
  rw [hk, hlen, hdist] at he
  exact (add_left_cancel he).symm

/-- The actual full-period filtered interval inventory is its literal linear
inventory when the displacement bin is retained, and zero otherwise. -/
theorem originalWindow_filtered_inventory_at_period_length {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) (hj : 2 ≤ j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ)
    (hbound : ∀ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j z ≤ M)
    (K : ℕ+) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    c.originalFilteredIntervalInventory P j K =
      if q = M then linearInverseWindowSum (c.originalInternalResidue P) j else 0 := by
  classical
  have hjB : j ≤ originalSelectedCount (hD := hD) P := by rw [hjlen]; exact Nat.sub_le _ _
  have hj' : j - 1 + 1 = j := by omega
  have hraw := c.originalFilteredIntervalInventory_eq_linear P hB (j - 1) (by omega)
    (by omega) M (by simpa only [hj'] using hbound) K hKeq
  simp only [hj'] at hraw
  rw [hraw]
  unfold filteredLinearInverseWindowSum
  by_cases hqm : q = M
  · rw [ite_eq_left hqm]
    unfold linearInverseWindowSum
    apply Finset.sum_congr rfl
    intro s _
    have hg := c.originalWindow_internal_gap_window_sum P W q u v hv hW hwindow
      hcutq hcutLq j (by omega) hjlen s.val (by have := s.isLt; omega)
    rw [hg, hqm, ite_eq_left rfl]
  · rw [ite_eq_right hqm]
    apply Finset.sum_eq_zero
    intro s _
    have hg := c.originalWindow_internal_gap_window_sum P W q u v hv hW hwindow
      hcutq hcutLq j (by omega) hjlen s.val (by have := s.isLt; omega)
    rw [hg, ite_eq_right hqm]

/-- Every full window in the actual internal-period gap cycle has the literal
translation sum. This identifies its bin filter without assuming a source cycle
period or assigning independent gap variables. -/
theorem originalWindow_period_gap_windows {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) [NeZero j]
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :
    ∀ s : ZMod j, windowSum
      (finiteWordCycle (n := j) (c.originalCompletedGap P) (by omega)) 1 j s = q := by
  have hj : 0 < j := Nat.pos_of_ne_zero (NeZero.ne j)
  have hjB : j ≤ originalSelectedCount (hD := hD) P := by rw [hjlen]; exact Nat.sub_le _ _
  let g := finiteWordCycle (n := j) (c.originalCompletedGap P) hjB
  have hprefix : windowSum g 1 j 0 = windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 j 0 := by
    unfold windowSum
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    simp only [zero_add, nsmul_eq_mul, mul_one, g, finiteWordCycle]
    congr 1
    apply Fin.ext
    change (a : ZMod j).val =
      ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm
        (a : ZMod (originalSelectedCount (hD := hD) P))).val
    rw [finEquiv_symm_val, ZMod.val_natCast_of_lt ha',
      ZMod.val_natCast_of_lt (ha'.trans_le hjB)]
  have hzero := c.originalWindow_internal_gap_window_sum P W q u v hv hW hwindow
    hcutq hcutLq j hj hjlen 0 (by omega)
  intro s
  calc
    windowSum g 1 j s = ∑ z, g z := zmod_windowSum_cycle g s
    _ = windowSum g 1 j 0 := (zmod_windowSum_cycle g 0).symm
    _ = q := hprefix.trans (by simpa only [Nat.cast_zero] using hzero)

end SkewCornerDescent.Matrix.SelectedCoordinate
