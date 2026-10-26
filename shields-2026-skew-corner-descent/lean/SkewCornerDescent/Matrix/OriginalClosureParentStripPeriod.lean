/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalClosureIncomingPeriod

/-!
# Complete parent-cell strip periods throughout the genuine ordinary closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full actual incoming word inherits the selected phase period. Actual
height and residue cycles then supply literal interval copies at every
eligible state in both source copies and across their true splice.
Restoring every original row and column transports the complete parent
cell strips rather than only selected endpoints or response values.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- No discrepancy supplies full literal parent-strip copies at every
genuine shifted closure state. -/
theorem originalClosure_no_discrepancy_parent_strip_period {pn qn : ℕ}
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
          (phaseCycleEquiv b r (i,k+(d : ZMod b))))).1) →
    ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
      (originalHessenbergDistance (hD := hD) Q
          (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) =
        originalHessenbergDistance (hD := hD) Q
          (originalInternalStateIndex Q j) (originalInternalStateIndex Q j)) ∧
      originalInternalLiteralCopy Q i j ∧
      translate (originalInternalCellShift Q i j) (originalInternalParentStrip Q i) =
        originalInternalParentStrip Q j := by
  obtain ⟨hCQ, hstate⟩ := c.originalClosure_profile_height_residue_cycle P Q z hQ active
  obtain ⟨_, hincoming⟩ := c.originalClosure_no_discrepancy_incoming_period P Q z hQ
    b r d hc hB
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hH | hV
    · exact c.originalHorizontalClosure_profile_component_span P Q z hH hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hV hmax
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hs := hstate hactive
  dsimp only at hs ⊢
  intro hp i j hij
  have hx : (j.val : ZMod (originalSelectedCount (hD := hD) P)) =
      (i.val : ZMod (originalSelectedCount (hD := hD) P)) +
        (r : ZMod (originalSelectedCount (hD := hD) P)) := by rw [hij, Nat.cast_add]
  have hheight : originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) =
      originalHessenbergDistance (hD := hD) Q
        (originalInternalStateIndex Q j) (originalInternalStateIndex Q j) := by
    rw [(hs i).2.1, (hs j).2.1, hx]
    exact congrArg (fun t : ℤ => (c.top : ℤ) + t) (hgap _).symm
  have hres : c.originalInternalResidue Q i = c.originalInternalResidue Q j := by
    rw [(hs i).2.2, (hs j).2.2, hx]
    exact (hresponse _).symm
  have hcopy := c.originalInternal_literal_copy_of_incoming_eq Q i j hheight hres hmaxQ
    (hincoming hp i j hij)
  exact ⟨hheight, hcopy, originalInternal_literal_parent_strips Q i j hheight hcopy⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
