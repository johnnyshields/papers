/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProfileWordPeriods
import SkewCornerDescent.Matrix.OriginalInternalHeights
import SkewCornerDescent.Matrix.OriginalNormalResidueCycles
import SkewCornerDescent.Matrix.OriginalVerticalGapPeriod

/-!
# Actual completed closure profile, height, and residue cycles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal ordinary closure copies supply the whole paired-profile cycle and
its genuine completed height cycle. The identified central response then
supplies the actual residue cycle, without asserting literal row/column
reconstruction. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete paired endpoint-profile word of either actual ordinary
closure is its genuine source-length cycle at every original position. -/
theorem originalClosure_profile_cycle {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)] :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    let hB : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 := by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q) hB
    ∀ i : Fin (originalSelectedCount (hD := hD) Q - 1),
      c.originalInternalEndpointProfiles Q i =
        cycle (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
  obtain ⟨hCQ, hword⟩ := c.originalClosure_profile_word_period P Q z hQ
  refine ⟨hCQ, ?_⟩
  have hB : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 := by
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega
  have hp : ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1),
      j.val = i.val + originalSelectedCount (hD := hD) P →
        c.originalInternalEndpointProfiles Q i = c.originalInternalEndpointProfiles Q j := by
    simpa only [originalInternalEndpointProfiles] using hword
  exact fun i => finiteWordCycle_eq (c.originalInternalEndpointProfiles Q) hB hp i

/-- The actual retained height cycle includes the genuine completed central
gap of either ordinary closure, rather than a guessed wrapped endpoint. -/
theorem originalClosure_internal_height_cycle {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
    originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) =
      (c.top : ℤ) + c.originalCompletedGap P
        ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P))) := by
  rw [c.originalInternal_height_eq_completed_gap Q i]
  apply congrArg (fun x : ℤ => (c.top : ℤ) + x)
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have he : c.originalCompletedGap Q ⟨i.val, by have := i.isLt; omega⟩ =
      c.originalCompletedGap P
        ⟨i.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_mod P Q z hQ hB _
    · exact c.originalVerticalClosure_completed_gap_mod P Q z hQ hB _
  rw [he]
  apply congrArg (c.originalCompletedGap P)
  apply Fin.ext
  simp only [finEquiv_symm_val, ZMod.val_natCast]

/-- Literal closure geometry supplies the actual profile cycle and height
cycle together; identifying its actual central response supplies the residue
cycle. This is not literal reconstruction of the original row/column lists. -/
theorem originalClosure_profile_height_residue_cycle {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)] (active : OtherField c.top) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    ∀ i : Fin (originalSelectedCount (hD := hD) Q - 1),
      c.originalInternalEndpointProfiles Q i =
        cycle (i.val : ZMod (originalSelectedCount (hD := hD) P)) ∧
      originalHessenbergDistance (hD := hD) Q
        (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) =
        (c.top : ℤ) + c.originalCompletedGap P
          ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P))) ∧
      c.originalInternalResidue Q i = completeResponseCycle (c.originalInternalResidue P) active
        (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
  obtain ⟨hCQ, hprofiles⟩ := c.originalClosure_profile_cycle P Q z hQ
  obtain ⟨_, hresidues⟩ := c.originalClosure_normal_residue_cycle P Q z hQ active
  refine ⟨hCQ, ?_⟩
  intro hactive
  dsimp only
  intro i
  refine ⟨hprofiles i, c.originalClosure_internal_height_cycle P Q z hQ i, ?_⟩
  have he := hresidues hactive i
  rw [c.originalInternal_normal_constant Q] at he
  exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
