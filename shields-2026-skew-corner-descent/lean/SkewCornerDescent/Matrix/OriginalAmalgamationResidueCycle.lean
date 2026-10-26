/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalResidueCycles

/-!
# Actual amalgamation residue phase through every original position

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal copies produce the full normal overlap period. The source inventory
and independently periodic completed response then give every smaller
residue-phase letter, including all repeated wraps. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The smaller residue phase extends through the actual amalgamation because
its whole normal overlap period is a multiple of that phase. The count equation
is the source inventory equation; no full-normal smaller period is asserted. -/
theorem originalAmalgamation_normal_residue_cycle {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hproper : originalSelectedCount (hD := hD) W < originalSelectedCount (hD := hD) P)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hstep : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = d * r)
    (active : OtherField c.top)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    ∀ i : Fin (originalSelectedCount (hD := hD) A - 1),
      PowerSeries.constantCoeff (((c.originalInternalResponseMatrix A).map c.normalSeries) i i) =
        completeResponseCycle (c.originalInternalResidue P) active
          (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
  let B := originalSelectedCount (hD := hD) P
  let T := d * r
  have hTpos : 0 < T := Nat.mul_pos hd hr
  let : NeZero T := ⟨ne_of_gt hTpos⟩
  obtain ⟨hAP, hinv, hword⟩ := c.originalAmalgamation_internal_word_periods
    P W A q v u z hq hv hwindow hW hA hcutq hcutLq
  obtain ⟨_, hupper⟩ := c.originalAmalgamation_upper_internal_matrix
    P A q v u hq hv hwindow hA hcutq hcutLq
  have hshift : originalSelectedCount (hD := hD) A -
      originalSelectedCount (hD := hD) P = T := by dsimp only [T]; omega
  have hTP : T ≤ originalSelectedCount (hD := hD) P - 1 := by dsimp only [T]; omega
  have hTA : T ≤ originalSelectedCount (hD := hD) A - 1 := by omega
  let word := fun i : Fin (originalSelectedCount (hD := hD) A - 1) =>
    PowerSeries.constantCoeff (((c.originalInternalResponseMatrix A).map c.normalSeries) i i)
  let g := fun k : ℕ => completeResponseCycle (c.originalInternalResidue P) active (k : ZMod B)
  have hperiod : Function.Periodic g T := by
    intro k
    have he := (hresponse.nsmul d) (k : ZMod B)
    simpa only [g, T, Nat.cast_add, Nat.cast_mul, nsmul_eq_mul] using he
  have hp : ∀ i j : Fin (originalSelectedCount (hD := hD) A - 1),
      j.val = i.val + T → word i = word j := by
    intro i j hij
    exact congrArg PowerSeries.constantCoeff (hword.1 i j (by omega))
  have hfirst (i : Fin T) : word ⟨i.val, i.isLt.trans_le hTA⟩ = g i.val := by
    have hi : i.val < originalSelectedCount (hD := hD) P - 1 := i.isLt.trans_le hTP
    have he := congrArg PowerSeries.constantCoeff (hupper ⟨i.val, hi⟩ ⟨i.val, hi⟩)
    rw [c.originalInternal_normal_constant P] at he
    exact he.trans (completeResponseCycle_prefix
      (c.originalInternalResidue P) active ⟨i.val, hi⟩).symm
  exact finite_periodic_word_eq_of_prefix word hTA hp g hperiod hfirst

end SkewCornerDescent.Matrix.SelectedCoordinate
