/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalClosureRootSpanStrips
import SkewCornerDescent.Matrix.OriginalOrdinaryFullPeriodWindows
import SkewCornerDescent.FullWindowInheritedBoundary

/-!
# Complete actual proper literal root on the no-discrepancy branch

Formalizes the root branch of `shields-2026-skew-corner-descent.tex`,
`prop:normal-interface`. Actual interval recovery supplies whole parent
cell strips at one produced root-span translation. Genuine doubled
ordinary copies and the true-cap margin give complete source windows.
Their literal period supplies the ordinary boundary and joining edge;
the actual selected component supplies a nonempty root interior.
The conclusion is the whole original parent-cell composition. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual no-discrepancy branch constructs a proper connected nonline
inner and a literal empty b-copy row or column composition of the whole source. -/
theorem originalClosure_no_discrepancy_literal_root {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r d : ℕ) [NeZero b] [NeZero r]
    (hc : Nat.Coprime d b) (hb : 3 ≤ b)
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
    ∃ E : Diagram, IsConnectedSkew E ∧ span E = δ.toNat ∧
      (emptyMarkH E).IsLegal ∧ 2 ≤ E.card ∧
      (∃ x ∈ E, ∃ y ∈ E, x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
      2 ≤ (horizontalRow b).card ∧ 2 ≤ (verticalColumn b).card ∧
      (P.cells = (emptyMarkH E).compose (horizontalRow b) ∨
        P.cells = (emptyMarkH E).compose (verticalColumn b)) := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_no_discrepancy_root_span_strips P Q z hQ active
    b r d hc (by omega) hB hresponse hgap hmax δ hspan
  refine ⟨hCQ, ?_⟩
  intro hactive
  dsimp only
  intro hp
  obtain ⟨v, hrow, hδ, hv, hfixed, hstrips, hselected⟩ := hdata hactive hp
  have hP := NeZero.pos (originalSelectedCount (hD := hD) P)
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by omega⟩
  have hfull := c.originalOrdinaryClosure_full_windows_of_strip_period P Q z hQ
    b r hb hB δ hδ hspan hgap v hv hstrips (fun i j hij => (hselected i j hij).2)
  have hvup : content (-v) = δ := by
    dsimp only [content, Prod.fst_neg, Prod.snd_neg]
    change v.2-v.1 = -δ at hv
    omega
  have hmin : minContent P.cells = 0 := P.minContent_cells
  have hmaxP : maxContent P.cells = (b : ℤ)*δ-1 := by rw [P.maxContent_cells, hspan]
  have hwindow : upperFullWindow P.cells b δ = translate (-v) (lowerFullWindow P.cells b δ) := by
    unfold upperFullWindow lowerFullWindow
    rw [← hspan, show ((b : ℤ)-1)*δ = P.xi 0-δ by rw [hspan]; ring]
    exact hfull
  have hboundary := fullWindow_period_ordinary_boundary P.isConnectedSkew_cells b
    (by omega) δ hδ (-v) hvup hmin hmaxP hwindow
  have hinterior : (diagramInterior P.cells).Nonempty := by
    let sel := originalSelectedEnumeration (hD := hD) P ⟨0,hP⟩
    have hsel := originalBlockSelected_nonempty P sel.val sel.property
    have hn := (interiorBlockCells_connected P sel.val.val hsel).2.1
    have hs : interiorBlockCells P sel.val.val ⊆ diagramInterior P.cells :=
      interiorSliceCells_subset P _ _ _
    exact hn.mono hs
  exact fullWindow_boundary_proper_root P.isConnectedSkew_cells b (by omega) δ hδ
    (-v) hvup hmin hmaxP hwindow hboundary.1 hboundary.2 hinterior

end SkewCornerDescent.Matrix.SelectedCoordinate
