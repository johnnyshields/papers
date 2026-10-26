/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOrdinaryPeriodContent
import SkewCornerDescent.Matrix.OriginalClosureFixedParentStrips

/-!
# Full parent-strip translation at the exact original root span

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual no-discrepancy branch produces one common physical translation
throughout both genuine closure copies. Original whole-copy beta spans
fix its content to the negative root span. All selected endpoint
displacements, including the last selected endpoint, are retained.
Whole content-window and private-cut transport remain separate. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual no-discrepancy geometry produces complete parent-strip copies
by one physical translation of exactly the root-span content. -/
theorem originalClosure_no_discrepancy_root_span_strips {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r d : ℕ) [NeZero b] [NeZero r]
    (hc : Nat.Coprime d b) (hb : 2 ≤ b)
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ) :
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
    ∃ v : ℤ × ℤ, 0 < v.1 ∧ 0 < δ ∧ content v = -δ ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
        originalInternalCellShift Q i j = v) ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
        translate v (originalInternalParentStrip Q i) = originalInternalParentStrip Q j) ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) Q), j.val = i.val+r →
        (originalSelectedSourceRow Q j - originalSelectedSourceRow Q i = v.1) ∧
          (originalSelectedSourceBeta Q j - originalSelectedSourceBeta Q i = content v)) := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_no_discrepancy_fixed_parent_strips P Q z hQ active
    b r d hc hB hresponse hgap hmax
  refine ⟨hCQ, ?_⟩
  intro hactive
  dsimp only
  intro hp
  obtain ⟨v, hrow, hneg, hfixed, hstrips, hselected⟩ := hdata hactive hp
  have hv := originalOrdinaryClosure_period_content P Q z hQ b r hb hB δ hspan v hfixed
  exact ⟨v, hrow, by omega, hv, hfixed, hstrips, hselected⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
