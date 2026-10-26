/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalAmalgamationGaps
import SkewCornerDescent.Matrix.OriginalClosureGapPeriod
import SkewCornerDescent.FinitePeriodicWords

/-!
# Source periods inherited by the actual amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
The actual completed gap word projects to the source period cycle. Selected-count
multiples make the rank shift vanish in that cycle. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A source cyclic period determines every literal finite source gap position. -/
theorem originalCompletedGap_period_cycle {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r : ℕ) [NeZero r]
    (hr : r ≤ originalSelectedCount (hD := hD) P)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalCompletedGap P i = finiteWordCycle (c.originalCompletedGap P) hr
      (i.val : ZMod r) := by
  have he (j : Fin (originalSelectedCount (hD := hD) P)) :
      (ZMod.finEquiv _).symm (j.val : ZMod (originalSelectedCount (hD := hD) P)) = j := by
    apply Fin.ext
    rw [finEquiv_symm_val, ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt]
  apply finiteWordCycle_eq
  intro a b hab
  have h := hp (a.val : ZMod (originalSelectedCount (hD := hD) P))
  have hb : (a.val : ZMod (originalSelectedCount (hD := hD) P)) + r =
      (b.val : ZMod (originalSelectedCount (hD := hD) P)) := by
    rw [hab, Nat.cast_add]
  simp only [hb, he a, he b] at h
  exact h.symm

/-- The actual amalgamation projects to the complete source period, with true caps included. -/
theorem originalAmalgamation_completed_gap_cycle {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)] (r : ℕ) [NeZero r]
    (hr : r ≤ originalSelectedCount (hD := hD) P)
    (hrB : r ∣ originalSelectedCount (hD := hD) P)
    (hrC : r ∣ originalSelectedCount (hD := hD) W)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i : Fin (originalSelectedCount (hD := hD) A)) :
    c.originalCompletedGap A i = finiteWordCycle (c.originalCompletedGap P) hr
      (i.val : ZMod r) := by
  obtain ⟨_, _, hw⟩ := c.originalAmalgamation_completed_gap_word P W A q v u z
    hq hv hwindow hW hA hcutq hcutLq hC
  rw [hw i]
  split_ifs with hi
  · exact c.originalCompletedGap_period_cycle P r hr hp _
  · have he := c.originalCompletedGap_period_cycle P r hr hp
      ⟨i.val - (originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W), by have := i.isLt; omega⟩
    have hn : r ∣ originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W := Nat.dvd_sub hrB hrC
    have hz : ((originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W : ℕ) : ZMod r) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hn
    have hm : ((i.val - (originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) W) : ℕ) : ZMod r) = (i.val : ZMod r) := by
      rw [Nat.cast_sub (by omega), hz, sub_zero]
    exact he.trans (congrArg (finiteWordCycle (c.originalCompletedGap P) hr) hm)

end SkewCornerDescent.Matrix.SelectedCoordinate
