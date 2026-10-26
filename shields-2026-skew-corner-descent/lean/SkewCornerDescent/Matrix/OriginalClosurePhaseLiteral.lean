/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalLiteralCopy
import SkewCornerDescent.Matrix.OriginalClosurePhaseData
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse
import SkewCornerDescent.Matrix.OriginalVerticalEndLogLocality

/-!
# Literal original interval copies within a completed occurrence phase

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
In the no-profile-discrepancy branch, the actual coprime shift becomes a
one-step period by Bezout.  Equal actual heights, residues and full incoming
profiles then reconstruct every paired original interval in one occurrence
phase.  This identifies complete beta lists, not merely their response values;
constructing the whole line-outer cell root remains a separate assembly.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- In the no-discrepancy branch, coprime shift counts and actual early
recovery identify every complete original interval in the same occurrence
phase.  The common translation is the original endpoint-coordinate shift,
not an assumed geometric copy or a scalar-response surrogate. -/
theorem originalClosure_phase_literal_intervals {pn qn : ℕ}
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
    ∀ (i : Fin r) (k l : ZMod b), originalInternalLiteralCopy Q
      (originalClosurePhaseStateIndex P Q b r hB hCQ i k)
      (originalClosurePhaseStateIndex P Q b r hB hCQ i l) := by
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
  let idx := fun (i : Fin r) (k : ZMod b) => originalClosurePhaseStateIndex P Q b r hB hCQ i k
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hH | hV
    · exact c.originalHorizontalClosure_profile_component_span P Q z hH hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hV hmax
  have hprofiles (i : Fin r) (k : ZMod b) :
      (c.originalInternalEndpointProfiles Q (idx i k)).1 = incoming i k :=
    congrArg Prod.fst ((hd i).2.2 k)
  intro hperiod i k l
  have hp : Function.Periodic
      (fun k : ZMod b => (c.originalInternalEndpointProfiles Q (idx i k)).1) (d : ZMod b) := by
    intro k
    apply (hprofiles i (k + (d : ZMod b))).trans
    apply Eq.trans ((hperiod i k).symm)
    exact (hprofiles i k).symm
  have hg := zmod_periodic_gcd _ hp
  rw [hc.gcd_eq_one, Nat.cast_one] at hg
  have hconstant (k : ZMod b) : (c.originalInternalEndpointProfiles Q (idx i k)).1 =
      (c.originalInternalEndpointProfiles Q (idx i 0)).1 := by
    have hk := hg.nsmul k.val 0
    simpa only [zero_add, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] using hk
  exact c.originalInternal_literal_copy_of_incoming_eq Q (idx i k) (idx i l)
    (((hd i).1 k).trans ((hd i).1 l).symm)
    (((hd i).2.1 k).trans ((hd i).2.1 l).symm) hmaxQ
    ((hconstant k).trans (hconstant l).symm)

end SkewCornerDescent.Matrix.SelectedCoordinate
