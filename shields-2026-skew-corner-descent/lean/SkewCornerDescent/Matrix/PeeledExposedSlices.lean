/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalDualExposure
import SkewCornerDescent.FiniteInactiveReplacement

/-!
# Actual exposed slices after finite inactive replacement

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
The chamber is formed from the remaining actual response family. Replaced coordinates take
its sign as a nonzero constant, so every off-anchor numerator has the common sign even in
the negative chamber. No word position or cyclic start is removed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

/-- A chamber of the remaining actual family supplies an exposed slice of the full family,
with all replaced coordinates regular and of the same chamber sign. -/
theorem remainingActualChamber_exposed_slice {α : Type*} [Finite α] [DecidableEq α]
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → OtherPolynomial N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive) :
    ∃ a : {a : {a : α // a ∉ S} // top a.val = K},
      let root := rationalAnchorRoot
        (fun a : {a : {a : α // a ∉ S} // top a.val = K} =>
          realResiduePolynomial N (p a.val.val))
        (fun a => realResiduePolynomial N (q a.val.val)) a x
      let num := fun Y => if Y ∈ S then Polynomial.C (if positive then 1 else -1)
        else coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q Y)
      let den := fun Y => if Y ∈ S then (1 : Polynomial ℝ)
        else coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q Y)
      Polynomial.eval root (num a.val.val) = 0 ∧
        Polynomial.rootMultiplicity root (num a.val.val) = 1 ∧
        (∀ Y, 0 < Polynomial.eval root (den Y)) ∧
        (∀ Y, Y ≠ a.val.val → 0 < (if positive then 1 else -1) *
          Polynomial.eval root (num Y)) := by
  classical
  obtain ⟨a, hroot, hsimple, hden, hsign⟩ := simultaneousActualChamber_exposed_slice
    N K hNK (fun a : {a : α // a ∉ S} => top a.val)
    (fun a => p a.val) (fun a => q a.val)
    (fun a j hj => hp a.val j hj) (fun a j hj => hq a.val j hj)
    hanchor positive x hx
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · simpa only [a.val.property, ite_false, exposedResponseNumerator,
      exposedResponseLinearNumerator] using hroot
  · simpa only [a.val.property, ite_false, exposedResponseNumerator,
      exposedResponseLinearNumerator] using hsimple
  · intro Y
    by_cases hY : Y ∈ S
    · simp only [hY, ite_true, Polynomial.eval_one]
      exact zero_lt_one
    · simpa only [hY, ite_false, exposedResponseDenominator] using hden ⟨Y, hY⟩
  · intro Y hYa
    by_cases hY : Y ∈ S
    · cases positive <;> norm_num [hY]
    · have hne : (⟨Y, hY⟩ : {Y : α // Y ∉ S}) ≠ a.val := by
        intro hz
        exact hYa (congrArg Subtype.val hz)
      simpa only [hY, ite_false, exposedResponseNumerator,
        exposedResponseLinearNumerator] using hsign ⟨Y, hY⟩ hne

end SkewCornerDescent.Matrix.SelectedCoordinate
