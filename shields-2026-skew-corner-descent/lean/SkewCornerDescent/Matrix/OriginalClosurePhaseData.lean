/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureProfileCycle
import SkewCornerDescent.CyclicPhaseIndex

/-!
# Actual common-height and common-response phase families

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal closure geometry supplies every representative profile. The true
response and gap phases produce common rational residues and integer heights
without imposing any smaller period on the full normal germs. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The genuine representative of a mixed-radix phase position in the full
actual closure word. Count equalities only transport the original index. -/
noncomputable def originalClosurePhaseStateIndex {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (b r : ℕ) [NeZero b] [NeZero r]
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P)
    (i : Fin r) (k : ZMod b) : Fin (originalSelectedCount (hD := hD) Q - 1) :=
  let x := ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k))
  ⟨x.val, by
    have hx := ZMod.val_lt x
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega⟩

/-- Actual closure geometry and the independently periodic response/gap
words supply common rational residues and heights on every occurrence phase.
The paired profiles themselves retain their complete genuine cycle values. -/
theorem originalClosure_phase_family_data {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r : ℕ) [NeZero b] [NeZero r]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    ∀ i : Fin r,
    let idx := fun k => originalClosurePhaseStateIndex P Q b r hB hCQ i k
    let K := ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    (∀ k, originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q (idx k)) (originalInternalStateIndex Q (idx k)) = (K : ℤ)) ∧
    (∀ k, c.originalInternalResidue Q (idx k) = c.originalInternalResidue Q (idx 0)) ∧
    (∀ k, c.originalInternalEndpointProfiles Q (idx k) =
      cycle (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))) := by
  obtain ⟨hCQ, hstate⟩ := c.originalClosure_profile_height_residue_cycle P Q z hQ active
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hs := hstate hactive
  dsimp only at hs ⊢
  intro i
  let e := ZMod.ringEquivCongr hB.symm
  let idx := fun k => originalClosurePhaseStateIndex P Q b r hB hCQ i k
  let H0 := (c.top : ℤ) + c.originalCompletedGap P
    ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))
  have hH0 : 0 ≤ H0 := by
    have hg := c.originalCompletedGap_gt_top P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))
    have hN : 0 < (c.top : ℤ) := by exact_mod_cast c.top.pos
    dsimp only [H0]
    omega
  have hK0 : (H0.toNat : ℤ) = H0 := Int.toNat_of_nonneg hH0
  have hi (k : ZMod b) : ((idx k).val : ZMod (originalSelectedCount (hD := hD) P)) =
      e (phaseCycleEquiv b r (i,k)) := by
    dsimp only [idx, originalClosurePhaseStateIndex, e]
    exact ZMod.natCast_zmod_val _
  have hconst {α : Type} (f : ZMod (originalSelectedCount (hD := hD) P) → α)
      (hp : Function.Periodic f (r : ZMod (originalSelectedCount (hD := hD) P)))
      (k : ZMod b) : f (e (phaseCycleEquiv b r (i,k))) =
        f (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
    exact phaseCycleEquiv_periodic_map b r e.toRingHom f hp i k
  have hheight (k : ZMod b) : originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q (idx k)) (originalInternalStateIndex Q (idx k)) = H0 := by
    have he := (hs (idx k)).2.1
    rw [hi] at he
    apply he.trans
    exact hconst
      (fun x => (c.top : ℤ) + c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (fun x => congrArg (fun t : ℤ => (c.top : ℤ) + t) (hgap x)) k
  have hres (k : ZMod b) : c.originalInternalResidue Q (idx k) =
      completeResponseCycle (c.originalInternalResidue P) active
        (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
    have he := (hs (idx k)).2.2
    rw [hi] at he
    exact he.trans (hconst _ hresponse k)
  refine ⟨fun k => (hheight k).trans hK0.symm, fun k => (hres k).trans (hres 0).symm, ?_⟩
  intro k
  have he := (hs (idx k)).1
  rw [hi] at he
  exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
