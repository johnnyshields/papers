/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationGapPeriod
import SkewCornerDescent.Matrix.OriginalAmalgamationInventory
import SkewCornerDescent.Matrix.OriginalCompletedCorePhase

/-!
# Complete actual amalgamation gap period and exact period total

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original corner powers supply all selected-count divisibilities. Complete
literal windows supply the gap cycle, including both true caps.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual source powers and windows produce the amalgamation's nonzero selected
count, its full gap period, and the unchanged complete period sum. -/
theorem originalCompleted_amalgamation_gap_period_data {n m an : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an)
    (q : ℤ) (u v w : ℤ × ℤ) (hq0 : 0 ≤ q) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate w A.cells)
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    ∃ hpos : 0 < originalSelectedCount (hD := hD) A,
      letI : NeZero (originalSelectedCount (hD := hD) A) := ⟨ne_of_gt hpos⟩
      Function.Periodic
        (fun x => c.originalCompletedGap A ((ZMod.finEquiv _).symm x))
        (r : ZMod (originalSelectedCount (hD := hD) A)) ∧
      windowSum (fun x => c.originalCompletedGap A ((ZMod.finEquiv _).symm x)) 1 r 0 =
        windowSum (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hdivP : r ∣ originalSelectedCount (hD := hD) P := ⟨b, hcountP⟩
  have hdivW : r ∣ originalSelectedCount (hD := hD) W := ⟨a, hcountW⟩
  have hCW : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  have hWP : originalSelectedCount (hD := hD) W < originalSelectedCount (hD := hD) P := by
    rw [hcountW, hcountP]
    exact Nat.mul_lt_mul_of_pos_left hab hrpos
  have hinv := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v w u hv hwindow hW.symm hA
  have hpos : 0 < originalSelectedCount (hD := hD) A := by
    have hBP := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega
  refine ⟨hpos, ?_⟩
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨ne_of_gt hpos⟩
  have hlenr : r ≤ originalSelectedCount (hD := hD) P := Nat.le_of_dvd (NeZero.pos _) hdivP
  have hAe : originalSelectedCount (hD := hD) A =
      2 * originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W := by omega
  have hdivA : r ∣ originalSelectedCount (hD := hD) A := by
    rw [hAe]
    have hd2 : r ∣ 2 * originalSelectedCount (hD := hD) P := ⟨2 * b, by rw [hcountP]; ring⟩
    exact Nat.dvd_sub hd2 hdivW
  let cycle := finiteWordCycle (n := r) (c.originalCompletedGap P) hlenr
  have hAP (j : Fin (originalSelectedCount (hD := hD) A)) :
      c.originalCompletedGap A j = cycle (j.val : ZMod r) :=
    c.originalAmalgamation_completed_gap_cycle P W A q v w u hq0 hv hwindow hW.symm hA
      (fun x hx => privateDiagonal_avoids_interior hq hx)
      (fun x hx => privateDiagonal_avoids_interior hLq hx) hCW r hlenr hdivP hdivW hgap j
  have hPP (j : Fin (originalSelectedCount (hD := hD) P)) :
      c.originalCompletedGap P j = cycle (j.val : ZMod r) :=
    c.originalCompletedGap_period_cycle P r hlenr hgap j
  have hprojA (z : ZMod (originalSelectedCount (hD := hD) A)) :
      c.originalCompletedGap A ((ZMod.finEquiv _).symm z) =
        cycle (ZMod.castHom hdivA (ZMod r) z) := by
    simpa only [finEquiv_symm_val, ZMod.castHom_apply, ZMod.cast_eq_val] using
      hAP ((ZMod.finEquiv _).symm z)
  have hprojP (z : ZMod (originalSelectedCount (hD := hD) P)) :
      c.originalCompletedGap P ((ZMod.finEquiv _).symm z) =
        cycle (ZMod.castHom hdivP (ZMod r) z) := by
    simpa only [finEquiv_symm_val, ZMod.castHom_apply, ZMod.cast_eq_val] using
      hPP ((ZMod.finEquiv _).symm z)
  constructor
  · intro z
    dsimp only
    rw [hprojA, hprojA, map_add, map_natCast, ZMod.natCast_self, add_zero]
  · unfold windowSum
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [hprojA, hprojP]
    simp only [map_add, map_zero, map_nsmul, map_one]

end SkewCornerDescent.Matrix.SelectedCoordinate
