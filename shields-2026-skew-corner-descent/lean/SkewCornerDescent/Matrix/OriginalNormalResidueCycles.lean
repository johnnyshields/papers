/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalWordPeriods
import SkewCornerDescent.FinitePeriodicWordComparison
import SkewCornerDescent.FiniteClosureWindows

/-!
# Actual full normal residues on the completed source cycle

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal matrix copies and the actual central closure residue identify every
original internal residue with its completed cyclic position. This identifies
residues only, never an unsupported smaller full-normal period. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete normal internal diagonal has its actual rational residue. -/
theorem originalInternal_normal_constant {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    PowerSeries.constantCoeff (((c.originalInternalResponseMatrix P).map c.normalSeries) i i) =
      c.originalInternalResidue P i := by
  change PowerSeries.constantCoeff (c.normalSeries (c.originalInternalResponseMatrix P i i)) = _
  rw [c.normalSeries_constant_apply]
  rfl

/-- The actual ordinary closure's full residue word is the completed source
cycle once its actual central residue is identified with the active response.
This is a response-word theorem, not a claim that full normal jets have that period. -/
theorem originalClosure_normal_residue_cycle {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)] (active : OtherField c.top) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q
      ⟨originalSelectedCount (hD := hD) P - 1, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = active) →
    ∀ i : Fin (originalSelectedCount (hD := hD) Q - 1),
      PowerSeries.constantCoeff (((c.originalInternalResponseMatrix Q).map c.normalSeries) i i) =
        completeResponseCycle (c.originalInternalResidue P) active
          (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
  obtain ⟨hCQ, hword⟩ := c.originalClosure_internal_word_periods P Q z hQ
  obtain ⟨_, hupper⟩ := c.originalClosure_upper_internal_matrix P Q z hQ
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hBpos := NeZero.pos (originalSelectedCount (hD := hD) P)
  let B := originalSelectedCount (hD := hD) P
  let word := fun i : Fin (originalSelectedCount (hD := hD) Q - 1) =>
    PowerSeries.constantCoeff (((c.originalInternalResponseMatrix Q).map c.normalSeries) i i)
  let g := fun k : ℕ => completeResponseCycle (c.originalInternalResidue P) active (k : ZMod B)
  have hperiod : Function.Periodic g B := by
    intro k
    simp [g, Nat.cast_add]
  have hp : ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1),
      j.val = i.val + B → word i = word j := by
    intro i j hij
    exact congrArg PowerSeries.constantCoeff (hword.1 i j hij)
  have hfirst (i : Fin B) :
      word ⟨i.val, by have := i.isLt; dsimp only [B] at *; omega⟩ = g i.val := by
    by_cases hi : i.val < B - 1
    · have he := congrArg PowerSeries.constantCoeff (hupper ⟨i.val, hi⟩ ⟨i.val, hi⟩)
      rw [c.originalInternal_normal_constant P] at he
      exact he.trans (completeResponseCycle_prefix
        (c.originalInternalResidue P) active ⟨i.val, hi⟩).symm
    · have hi' : i.val = B - 1 := by have := i.isLt; omega
      have he : word ⟨i.val, by have := i.isLt; dsimp only [B] at *; omega⟩ = active := by
        dsimp only [word]
        rw [originalInternal_normal_constant]
        exact (congrArg (c.originalInternalResidue Q) (Fin.ext hi')).trans hactive
      rw [he]
      have hmod : i.val % originalSelectedCount (hD := hD) P = i.val :=
        Nat.mod_eq_of_lt i.isLt
      simp only [g, completeResponseCycle, ZMod.val_natCast, hmod]
      have hnot : ¬ i.val < originalSelectedCount (hD := hD) P - 1 := hi
      rw [dite_eq_right hnot]
  exact finite_periodic_word_eq_of_prefix word (by dsimp only [B]; omega) hp g hperiod hfirst

end SkewCornerDescent.Matrix.SelectedCoordinate
