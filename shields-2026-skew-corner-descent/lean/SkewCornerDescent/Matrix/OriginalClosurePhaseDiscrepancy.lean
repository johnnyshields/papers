/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalPhaseMargins
import SkewCornerDescent.Matrix.OriginalClosurePhaseData
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse
import SkewCornerDescent.Matrix.OriginalVerticalEndLogLocality

/-!
# First discrepancies and maximal margin of the actual completed closure

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
The unchanged actual closure supplies all occurrence phases in both ordinary
directions.  Source gap and response periods give their exact common heights
and residues; original early recovery produces uniform first discrepancies,
a positive maximal resolving margin and a nonzero attaining difference.
The alternative is equality of all shifted complete incoming profiles.
No phase-discrepancy or margin data is taken as a hypothesis.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual ordinary closure supplies every phase discrepancy choice and
its common positive maximal resolving margin, unless all shifted complete
incoming profiles already coincide.  Both ordinary closure directions retain
all genuine source positions and produce the component span bound. -/
theorem originalClosure_phase_first_discrepancies {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r d : ℕ) [NeZero b] [NeZero r]
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
    let incoming := fun (i : Fin r) (k : ZMod b) =>
      (cycle (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
    let K := fun i : Fin r => ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    (∀ i k, incoming i k = incoming i (k + (d : ZMod b))) ∨
    ∃ choices : Fin r → Option ℕ, ∃ J : ℕ+,
      (∀ i, match choices i with
        | none => ∀ k, incoming i k = incoming i (k + (d : ZMod b))
        | some w => 0 < w ∧ 2 * w < K i ∧
            (∀ k l, l < w → (incoming i k).coeff l =
              (incoming i (k + (d : ZMod b))).coeff l) ∧
            (K i : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ)) ∧
      ∃ i w, choices i = some w ∧ (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) ∧
        ∃ k, (incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w ≠ 0 := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_phase_family_data P Q z hQ active b r hB
    hresponse hgap
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hd := hdata hactive
  dsimp only at hd ⊢
  let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q)
    (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega)
  let incoming := fun (i : Fin r) (k : ZMod b) =>
    (cycle (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
  let K := fun i : Fin r => ((c.top : ℤ) + c.originalCompletedGap P
    ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
  let idx := fun (i : Fin r) (k : ZMod b) => originalClosurePhaseStateIndex P Q b r hB hCQ i k
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hH | hV
    · exact c.originalHorizontalClosure_profile_component_span P Q z hH hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hV hmax
  have hheight (i : Fin r) (k : ZMod b) : originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q (idx i k)) (originalInternalStateIndex Q (idx i k)) =
        (K i : ℤ) := (hd i).1 k
  have hres (i : Fin r) (k : ZMod b) : c.originalInternalResidue Q (idx i k) =
      c.originalInternalResidue Q (idx i 0) := (hd i).2.1 k
  have hprofiles (i : Fin r) (k : ZMod b) :
      (c.originalInternalEndpointProfiles Q (idx i k)).1 = incoming i k :=
    congrArg Prod.fst ((hd i).2.2 k)
  dsimp only [incoming, cycle] at hprofiles
  have h := c.originalInternal_phase_resolving_margin Q idx d K hheight hres hmaxQ
  rcases h with hperiod | ⟨choices, J, hchoices, hattain⟩
  · left
    intro i k
    rw [← hprofiles, ← hprofiles]
    exact hperiod i k
  · right
    refine ⟨choices, J, ?_, ?_⟩
    · intro i
      have hs := hchoices i
      cases hi : choices i with
      | none =>
        rw [hi] at hs
        intro k
        rw [← hprofiles, ← hprofiles]
        exact hs k
      | some w =>
        rw [hi] at hs
        refine ⟨hs.1, hs.2.1, ?_, hs.2.2.2⟩
        intro k l hl
        rw [← hprofiles, ← hprofiles]
        exact hs.2.2.1 k l hl
    · obtain ⟨i, w, hi, hJ, k, hη⟩ := hattain
      refine ⟨i, w, hi, hJ, k, ?_⟩
      rw [← hprofiles, ← hprofiles]
      exact hη

end SkewCornerDescent.Matrix.SelectedCoordinate
