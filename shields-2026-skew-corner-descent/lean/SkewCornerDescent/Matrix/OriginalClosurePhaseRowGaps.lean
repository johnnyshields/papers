/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralIntervalRanks
import SkewCornerDescent.Matrix.OriginalClosurePhaseLiteral

/-!
# Physical source-row gaps on actual literal occurrence phases

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
No discrepancy in the completed profiles gives whole actual interval copies.
Their recovered ending core sizes and complete interval cardinalities then
force equal physical source-row gaps in every occurrence phase. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual no-discrepancy branch produces physical, not just beta, row-gap periodicity. -/
theorem originalClosure_phase_literal_row_gaps {pn qn : ℕ}
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
    ∀ (i : Fin r) (k l : ZMod b),
      originalInternalSourceRowGap Q (originalClosurePhaseStateIndex P Q b r hB hCQ i k) =
        originalInternalSourceRowGap Q (originalClosurePhaseStateIndex P Q b r hB hCQ i l) := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_phase_family_data P Q z hQ active b r hB
    hresponse hgap
  obtain ⟨hCQ', hcopy⟩ := c.originalClosure_phase_literal_intervals P Q z hQ active
    b r d hc hB hresponse hgap hmax
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hd := hdata hactive
  dsimp only at hd ⊢
  intro hperiod i k l
  exact originalInternal_literal_source_row_gap Q _ _
    (((hd i).1 k).trans ((hd i).1 l).symm) (hcopy hactive hperiod i k l)

end SkewCornerDescent.Matrix.SelectedCoordinate
