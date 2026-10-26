/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalClosurePhaseRankIndex
import SkewCornerDescent.Matrix.OriginalSelectedRowDisplacement

/-!
# Produced physical row displacement on the no-discrepancy branch

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Whole original interval recovery produces actual phasewise physical row
gaps. Their genuine finite period then gives one common source-row
displacement over all eligible selected starting positions in the ordinary
closure, including the first source copy’s closing endpoint. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Real completed phase gaps produce a common physical selected-row displacement. -/
theorem originalClosure_row_displacement_of_phase_gaps {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (b r : ℕ) [NeZero b] [NeZero r]
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P)
    (hphase : ∀ (i : Fin r) (k l : ZMod b),
      originalInternalSourceRowGap Q (originalClosurePhaseStateIndex P Q b r hB hCQ i k) =
        originalInternalSourceRowGap Q (originalClosurePhaseStateIndex P Q b r hB hCQ i l)) :
    ∃ rowShift : ℤ, ∀ i : ℕ, (hi : i + r ≤ originalSelectedCount (hD := hD) P) →
      originalSelectedSourceRow Q ⟨i + r, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ - originalSelectedSourceRow Q ⟨i, by
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩ = rowShift := by
  have hpos := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hless : originalSelectedCount (hD := hD) P < originalSelectedCount (hD := hD) Q := by
    omega
  have hb : 1 ≤ b := NeZero.pos b
  have hrle : r ≤ originalSelectedCount (hD := hD) P := by
    rw [hB]
    simpa only [one_mul] using Nat.mul_le_mul_right r hb
  refine ⟨originalSelectedSourceRow Q ⟨r, by omega⟩ -
    originalSelectedSourceRow Q ⟨0, by omega⟩, ?_⟩
  intro i hi
  apply originalSelected_source_row_displacement Q r (originalSelectedCount (hD := hD) P)
    hless hrle _ i hi
  intro j hj
  exact originalClosure_phase_period_of_constant P Q b r hB hCQ
    (originalInternalSourceRowGap Q) hphase j hj

/-- The actual no-discrepancy branch constructs one common physical row displacement. -/
theorem originalClosure_no_discrepancy_row_displacement {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r d : ℕ) [NeZero b] [NeZero r]
    (hc : Nat.Coprime d b)
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    (∀ (i : Fin r) (k : ZMod b),
      (cycle (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1 =
        (cycle (ZMod.ringEquivCongr hB.symm
          (phaseCycleEquiv b r (i,k + (d : ZMod b))))).1) →
    ∃ rowShift : ℤ, ∀ i : ℕ, (hi : i + r ≤ originalSelectedCount (hD := hD) P) →
      originalSelectedSourceRow Q ⟨i + r, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ - originalSelectedSourceRow Q ⟨i, by
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩ = rowShift := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_phase_literal_row_gaps P Q z hQ active b r d hc
    hB hresponse hgap hmax
  refine ⟨hCQ, ?_⟩
  intro hactive
  dsimp only
  intro hperiod
  exact originalClosure_row_displacement_of_phase_gaps P Q b r hB hCQ (hdata hactive hperiod)

end SkewCornerDescent.Matrix.SelectedCoordinate
