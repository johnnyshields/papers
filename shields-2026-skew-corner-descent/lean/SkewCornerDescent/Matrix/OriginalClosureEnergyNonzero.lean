/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFilteredPhaseEnergy
import SkewCornerDescent.Matrix.OriginalClosurePhaseData
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse
import SkewCornerDescent.Matrix.OriginalVerticalEndLogLocality

/-!
# Nonzero phase energy of the actual ordinary closure

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
Every scalar phase weight is identified with a genuine original closure
response class in both ordinary directions.  The attained discrepancy gives
a nonzero filtered energy through one produced positive regular chamber.
No positivity or independence of derived response functions is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The filtered energy in the actual completed ordinary closure is nonzero
at an attained nonzero discrepancy.  Genuine original closure response classes
supply one common positive regular specialization; no positivity or algebraic
independence of derived response functions is a hypothesis. -/
theorem originalClosure_filtered_phase_energy_ne_zero {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r d : ℕ) [NeZero b] [NeZero r]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    let C := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    let incoming := fun (i : Fin r) (k : ZMod b) =>
      (C (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
    let K := fun i : Fin r => ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    ∀ choices : Fin r → Option ℕ, ∀ J : ℕ+,
    (∃ i w, choices i = some w ∧ (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) ∧
      ∃ k, (incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w ≠ 0) →
    (∑ i : Fin r, match choices i with
      | none => 0
      | some w => if (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
          ((1/2 : OtherField c.top) * ∑ k : ZMod b,
            ((incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w)^2) *
              (completeResponseCycle (c.originalInternalResidue P) active
                (i.val : ZMod (originalSelectedCount (hD := hD) P)))⁻¹
        else 0) ≠ 0 := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_profile_height_residue_cycle P Q z hQ active
  refine ⟨hCQ, ?_⟩
  intro hactive
  dsimp only
  let C := finiteWordCycle (c.originalInternalEndpointProfiles Q)
    (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega)
  let incoming := fun (i : Fin r) (k : ZMod b) =>
    (C (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
  let K := fun i : Fin r => ((c.top : ℤ) + c.originalCompletedGap P
    ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
  let idx := fun (i : Fin r) (k : ZMod b) => originalClosurePhaseStateIndex P Q b r hB hCQ i k
  let weight := fun i : Fin r => c.originalResponseClassOf Q
    (originalInternalStateIndex Q (idx i 0))
  have hmaxQ : ∀ D ∈ edgeComponents (diagramInterior Q.cells), span D ≤ (c.top : ℕ) := by
    rcases hQ with hH | hV
    · exact c.originalHorizontalClosure_profile_component_span P Q z hH hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hV hmax
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [hCQ]
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega
  have hindex (i : Fin r) : ((idx i 0).val : ZMod (originalSelectedCount (hD := hD) P)) =
      (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
    dsimp only [idx, originalClosurePhaseStateIndex]
    rw [ZMod.natCast_zmod_val, phaseCycleEquiv_apply]
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero, map_natCast]
  have hweight (i : Fin r) : (weight i).val =
      completeResponseCycle (c.originalInternalResidue P) active
        (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
    change c.originalInternalResidue Q (idx i 0) = _
    have hh := (hdata hactive (idx i 0)).2.2
    rw [hindex] at hh
    exact hh
  intro choices J hattain
  have h := c.originalResponseClasses_filtered_phase_energy_ne_zero Q hBQ hmaxQ
    incoming weight d K choices J hattain
  convert h using 1
  congr 1
  funext i
  cases hi : choices i with
  | none => rfl
  | some w => simp only [hweight, incoming, C, K]

end SkewCornerDescent.Matrix.SelectedCoordinate
