/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalSelectedCells

/-!
# One actual selected-cell translation on the no-discrepancy branch

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Recovered complete intervals give a common physical row displacement, while
the actual phase heights give a common beta displacement. Their combination
translates genuine selected starting-row cells by one fixed vector with
positive row and negative content displacement. Whole-parent band transport
remains a separate geometric step. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual no-discrepancy geometry constructs one nonzero physical selected-cell translation. -/
theorem originalClosure_no_discrepancy_selected_translation {pn qn : ℕ}
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
    ∃ v : ℤ × ℤ, 0 < v.1 ∧ content v < 0 ∧
      ∀ i : ℕ, (hi : i + r ≤ originalSelectedCount (hD := hD) P) →
      originalSelectedRowRightCell Q ⟨i + r, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = originalSelectedRowRightCell Q ⟨i, by
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩ + v := by
  obtain ⟨hCQ, hrow⟩ := c.originalClosure_no_discrepancy_row_displacement P Q z hQ active
    b r d hc hB hresponse hgap hmax
  obtain ⟨hCQ', hbeta⟩ := c.originalClosure_periodic_beta_displacement P Q z hQ active
    b r hB hresponse hgap
  refine ⟨hCQ, ?_⟩
  intro hactive
  dsimp only
  intro hperiod
  obtain ⟨R, hR⟩ := hrow hactive hperiod
  obtain ⟨H, hH⟩ := hbeta hactive
  have hpos := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hb : 1 ≤ b := NeZero.pos b
  have hrle : r ≤ originalSelectedCount (hD := hD) P := by
    rw [hB]
    simpa only [one_mul] using Nat.mul_le_mul_right r hb
  have hR0 := hR 0 (by omega)
  have hH0 := hH 0 (by omega)
  have hRpos : 0 < R := by
    rw [← hR0]
    apply sub_pos.mpr
    apply originalSelectedSourceRow_strictMono Q
    change (0 : ℕ) < 0 + r
    simpa only [zero_add] using NeZero.pos r
  have hHneg : H < 0 := by
    rw [← hH0]
    apply sub_neg.mpr
    apply originalSelectedSourceBeta_strictAnti Q
    change (0 : ℕ) < 0 + r
    simpa only [zero_add] using NeZero.pos r
  refine ⟨(R,H+R), hRpos, ?_, ?_⟩
  · change H+R-R < 0
    omega
  · intro i hi
    exact originalSelectedRowRightCell_translate Q _ _ R H (hR i hi) (hH i hi)

end SkewCornerDescent.Matrix.SelectedCoordinate
