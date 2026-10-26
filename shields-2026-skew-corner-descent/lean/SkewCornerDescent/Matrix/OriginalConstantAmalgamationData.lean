/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationWord
import SkewCornerDescent.Matrix.OriginalAmalgamationGaps
import SkewCornerDescent.Matrix.OriginalAmalgamationCoreWord
import SkewCornerDescent.Matrix.OriginalClosureProfileCycle

/-!
# Full constant source data in the actual overlap union

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Whole literal source copies supply the complete amalgamation response,
gap and proper-core words. Constant source data therefore identify every
actual internal union residue and height, and both full core profiles,
including positions beyond the first overlap period. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Transfer all actual constant source data to the whole amalgamation,
not just its first cycle or a list of independent response values. -/
theorem originalAmalgamation_constant_internal_data {n m k : ℕ}
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
    (S : OtherField c.top) (K : ℤ)
    (hS : ∀ i, c.originalInternalResidue P i = S)
    (hgap : ∀ i, c.originalCompletedGap P i = K - (c.top : ℤ))
    (hcore : ∀ i : Fin (originalSelectedCount (hD := hD) P),
      c.originalSelectedCoreLeft P i = c.originalSelectedCoreLeft P 0 ∧
        c.originalSelectedCoreRight P i = c.originalSelectedCoreRight P 0) :
    originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A ∧
      originalSelectedCount (hD := hD) A + originalSelectedCount (hD := hD) W =
        2 * originalSelectedCount (hD := hD) P ∧
      (∀ i : Fin (originalSelectedCount (hD := hD) A - 1),
        c.originalInternalResidue A i = S ∧
          originalHessenbergDistance (hD := hD) A
            (originalInternalStateIndex A i) (originalInternalStateIndex A i) = K) ∧
      ∀ i : Fin (originalSelectedCount (hD := hD) A),
        c.originalSelectedCoreLeft A i = c.originalSelectedCoreLeft P 0 ∧
          c.originalSelectedCoreRight A i = c.originalSelectedCoreRight P 0 := by
  have hcutq' := fun x hx => privateDiagonal_avoids_interior hcutq (x := x) hx
  have hcutLq' := fun x hx => privateDiagonal_avoids_interior hcutLq (x := x) hx
  obtain ⟨hc, hinv, hword⟩ := c.originalAmalgamation_internal_word P W A q v u z
    hq hv hwindow hW hA hcutq' hcutLq' hC
  obtain ⟨_, _, hgapword⟩ := c.originalAmalgamation_completed_gap_word P W A q v u z
    hq hv hwindow hW hA hcutq' hcutLq' hC
  obtain ⟨_, _, hcoreword⟩ := c.originalAmalgamation_core_word P W A q v u z
    hq hv hwindow hW hA hcutq' hcutLq'
  have hgapA (i : Fin (originalSelectedCount (hD := hD) A)) :
      c.originalCompletedGap A i = K - (c.top : ℤ) := by
    rw [hgapword]
    split_ifs <;> exact hgap _
  refine ⟨hc, hinv, ?_, ?_⟩
  · intro i
    constructor
    · change c.regularResidue (c.originalInternalResponse A i) = S
      rw [hword]
      split_ifs <;> exact hS _
    · rw [c.originalInternal_height_eq_completed_gap, hgapA]
      ring
  · intro i
    obtain ⟨hl, hr⟩ := hcoreword i
    constructor
    · rw [hl]
      split_ifs <;> exact (hcore _).1
    · rw [hr]
      split_ifs <;> exact (hcore _).2

end SkewCornerDescent.Matrix.SelectedCoordinate
