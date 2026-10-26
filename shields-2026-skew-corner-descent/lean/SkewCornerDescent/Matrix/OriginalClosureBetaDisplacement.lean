/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalSelectedBetaGaps

/-!
# Produced beta displacement in the actual ordinary closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual periodic response and gap data produce common phase heights,
hence a common beta displacement over each full occurrence period.
Every endpoint belongs to the genuine doubled ordinary closure. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual phase heights give a common selected beta displacement. -/
theorem originalClosure_beta_displacement_of_phase_heights {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (b r : ℕ) [NeZero b] [NeZero r]
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P)
    (hphase : ∀ (i : Fin r) (k l : ZMod b),
      originalHessenbergDistance (hD := hD) Q
          (originalInternalStateIndex Q (originalClosurePhaseStateIndex P Q b r hB hCQ i k))
          (originalInternalStateIndex Q (originalClosurePhaseStateIndex P Q b r hB hCQ i k)) =
        originalHessenbergDistance (hD := hD) Q
          (originalInternalStateIndex Q (originalClosurePhaseStateIndex P Q b r hB hCQ i l))
          (originalInternalStateIndex Q (originalClosurePhaseStateIndex P Q b r hB hCQ i l))) :
    ∃ betaShift : ℤ, ∀ i : ℕ, (hi : i + r ≤ originalSelectedCount (hD := hD) P) →
      originalSelectedSourceBeta Q ⟨i + r, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ - originalSelectedSourceBeta Q ⟨i, by
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩ = betaShift := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  have hpos := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hless : originalSelectedCount (hD := hD) P < originalSelectedCount (hD := hD) Q := by
    omega
  have hb : 1 ≤ b := NeZero.pos b
  have hrle : r ≤ originalSelectedCount (hD := hD) P := by
    rw [hB]
    simpa only [one_mul] using Nat.mul_le_mul_right r hb
  refine ⟨originalSelectedSourceBeta Q ⟨r, by omega⟩ -
    originalSelectedSourceBeta Q ⟨0, by omega⟩, ?_⟩
  intro i hi
  apply originalSelected_source_beta_displacement Q r (originalSelectedCount (hD := hD) P)
    hless hrle _ i hi
  intro j hj
  apply originalClosure_phase_period_of_constant P Q b r hB hCQ
    (originalInternalSourceBetaGap Q) _ j hj
  intro phase k l
  rw [coord.originalInternal_source_beta_gap_height, coord.originalInternal_source_beta_gap_height,
    hphase phase k l]

/-- The actual ordinary periodic geometry constructs its selected beta displacement. -/
theorem originalClosure_periodic_beta_displacement {pn qn : ℕ}
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
    ∃ betaShift : ℤ, ∀ i : ℕ, (hi : i + r ≤ originalSelectedCount (hD := hD) P) →
      originalSelectedSourceBeta Q ⟨i + r, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ - originalSelectedSourceBeta Q ⟨i, by
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩ = betaShift := by
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_phase_family_data P Q z hQ active b r hB
    hresponse hgap
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hd := hdata hactive
  dsimp only at hd
  apply originalClosure_beta_displacement_of_phase_heights P Q b r hB hCQ
  intro phase k l
  exact ((hd phase).1 k).trans ((hd phase).1 l).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
