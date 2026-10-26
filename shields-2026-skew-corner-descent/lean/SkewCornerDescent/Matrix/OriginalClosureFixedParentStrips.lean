/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralPeriodTranslation

/-!
# One fixed physical translation for all actual parent-strip periods

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete original interval copies throughout the genuine doubled closure
produce periodic physical row and beta increments. Their finite sums give
one fixed nonzero cell translation for every actual parent-strip copy,
including both sides of the true source splice. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- No discrepancy constructs one physical translation for every complete
parent-strip period in the actual doubled closure. -/
theorem originalClosure_no_discrepancy_fixed_parent_strips {pn qn : ℕ}
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
    ∃ v : ℤ × ℤ, 0 < v.1 ∧ content v < 0 ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
        originalInternalCellShift Q i j = v) ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
        translate v (originalInternalParentStrip Q i) = originalInternalParentStrip Q j) ∧
      (∀ i j : Fin (originalSelectedCount (hD := hD) Q), j.val = i.val+r →
        (originalSelectedSourceRow Q j - originalSelectedSourceRow Q i = v.1) ∧
          (originalSelectedSourceBeta Q j - originalSelectedSourceBeta Q i = content v)) := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_no_discrepancy_parent_strip_period P Q z hQ active
    b r d hc hB hresponse hgap hmax
  refine ⟨hCQ, ?_⟩
  intro hactive
  dsimp only
  intro hp
  have hd := hdata hactive hp
  have hb : 1 ≤ b := NeZero.pos b
  have hmul : r ≤ b*r := by simpa only [one_mul] using Nat.mul_le_mul_right r hb
  have hcount := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hrQ : r < originalSelectedCount (hD := hD) Q := by omega
  obtain ⟨v, hrow, hcontent, hfixed, hselected⟩ := originalLiteralPeriod_fixed_cell_shift Q r hrQ
    (fun i j hij => ⟨(hd i j hij).1, (hd i j hij).2.1⟩)
  refine ⟨v, hrow, hcontent, hfixed, ?_, hselected⟩
  intro i j hij
  rw [← hfixed i j hij]
  exact (hd i j hij).2.2

end SkewCornerDescent.Matrix.SelectedCoordinate
