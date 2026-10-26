/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosurePhaseData
import SkewCornerDescent.Matrix.OriginalInternalProfileEnergy

/-!
# Complete energy jets on actual response phases

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal closure geometry produces every common phase height and response.
The actual internal-family energy producer then gives all lower cross jets
and the directed half-square coefficient. No self-product jet or energy
identity is an extra input. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual response phase has its exact directed energy and all lower
cross jets. Literal closure geometry supplies the family height and residue
contracts; the true source floor supplies the fresh-generator margin. -/
theorem originalClosure_phase_energy_jets {pn qn : ℕ}
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
    let f := fun k : ZMod b => (cycle
      (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
    let g := fun k : ZMod b => (cycle
      (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).2
    let K := ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    ∀ w : ℕ, 0 < w → 2 * w < K →
    (∀ k l, l < w → (f k).coeff l = (f (k + (d : ZMod b))).coeff l) →
    (∀ l, l < 2 * w →
      ∑ k, (f k * g (k + (d : ZMod b)) - f k * g k).coeff l = 0) ∧
      (∑ k, (f k * g (k + (d : ZMod b)) - f k * g k).coeff (2 * w)) =
        (1/2 : OtherField c.top) * ∑ k,
          ((f k).coeff w - (f (k + (d : ZMod b))).coeff w)^2 := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_phase_family_data P Q z hQ active b r hB hresponse hgap
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hd := hdata hactive
  dsimp only at hd ⊢
  intro i w hw hhalf hmatch
  let idx := fun k => originalClosurePhaseStateIndex P Q b r hB hCQ i k
  let σ : Equiv.Perm (ZMod b) := Equiv.addRight (d : ZMod b)
  let K := ((c.top : ℤ) + c.originalCompletedGap P
    ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
  obtain ⟨hheight, hS, hprofiles⟩ := hd i
  have hm : ∀ k l, l < w →
      (c.originalInternalEndpointProfiles Q (idx k)).1.coeff l =
      (c.originalInternalEndpointProfiles Q (idx (σ k))).1.coeff l := by
    intro k l hl
    rw [hprofiles, hprofiles]
    exact hmatch k l hl
  have he := c.originalInternal_profile_energy_jets Q idx σ 0 K w hw hhalf hheight hS hm
  dsimp only at he
  have hσ (k : ZMod b) : σ k = k + (d : ZMod b) := rfl
  simp only [idx, hσ] at he
  simpa only [hprofiles] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
