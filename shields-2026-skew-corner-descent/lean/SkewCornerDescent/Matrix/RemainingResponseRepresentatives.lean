/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.PeeledExposedSlices
import SkewCornerDescent.Matrix.OriginalResponseNonzero

/-!
# Regular original representatives after inactive replacement

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
A chamber for the remaining actual family supplies polynomial representatives of the full
replaced source family. Replaced coordinates use the chamber sign. Regularity is produced
for the same noninjective coordinate specialization used by both complete detectors.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate CyclicWindows

/-- The remaining-family chamber supplies source representatives and target regularity for
all response classes, including the finitely replaced ones. -/
theorem remainingActualChamber_response_representatives {α : Type*}
    [Finite α] [DecidableEq α]
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive) :
    let source := algebraMap (OtherPolynomial N) (OtherField N)
    let φ := originalCoordinateSlice N K x
    let original := fun a => residueGenerator N ⟨top a, htop a⟩ +
      source (p a) / source (q a)
    ∃ num den : α → OtherPolynomial N,
      (∀ a, source (num a) / source (den a) =
        replaceResponses S original (fun _ => if positive then 1 else -1) a) ∧
      (∀ a, φ (num a) = if a ∈ S then RatFunc.C (if positive then 1 else -1)
        else algebraMap (Polynomial ℝ) (RatFunc ℝ)
          (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q a))) ∧
      (∀ a, φ (den a) = if a ∈ S then 1
        else algebraMap (Polynomial ℝ) (RatFunc ℝ)
          (coordinatePolynomial (K : ℕ) x (exposedResponseDenominator N q a))) ∧
      (∀ a, φ (num a) ≠ 0) ∧ (∀ a, φ (den a) ≠ 0) := by
  classical
  dsimp only
  let source := algebraMap (OtherPolynomial N) (OtherField N)
  let φ := originalCoordinateSlice N K x
  let num := fun a => if a ∈ S then (if positive then 1 else -1 : OtherPolynomial N)
    else originalExposedNumerator N top p q htop a
  let den := fun a => if a ∈ S then (1 : OtherPolynomial N) else q a ^ 2
  obtain ⟨hn, hd⟩ := originalCoordinateSlice_regular N K hNK
    (fun a : {a : α // a ∉ S} => top a.val) (fun a => p a.val) (fun a => q a.val)
    (fun a => htop a.val) (fun a j hj => hp a.val j hj)
    (fun a j hj => hq a.val j hj) hanchor positive x hx
  have hnφ (a : α) : φ (num a) ≠ 0 := by
    by_cases ha : a ∈ S
    · cases positive <;> simp only [num, ha, ite_true, Bool.false_eq_true, ite_false,
        map_one, map_neg, neg_ne_zero] <;> norm_num
    · simpa only [num, ha, ite_false, originalExposedNumerator] using hn ⟨a, ha⟩
  have hdφ (a : α) : φ (den a) ≠ 0 := by
    by_cases ha : a ∈ S
    · simp only [den, ha, ite_true, map_one]
      norm_num
    · simpa only [den, ha, ite_false] using hd ⟨a, ha⟩
  refine ⟨num, den, ?_, ?_, ?_, hnφ, hdφ⟩
  · intro a
    by_cases ha : a ∈ S
    · cases positive <;> simp only [num, den, replaceResponses, ha, ite_true,
        Bool.false_eq_true, ite_false, map_one, map_neg, div_one]
    · have hq0 : q a ≠ 0 := by
        intro hz
        exact hdφ a (by simp only [den, ha, ite_false, hz,
          zero_pow (by decide : 2 ≠ 0), map_zero])
      simpa only [num, den, replaceResponses, ha, ite_false] using
        originalExposedNumerator_fraction N top p q htop a hq0
  · intro a
    by_cases ha : a ∈ S
    · cases positive <;> simp only [num, ha, ite_true, Bool.false_eq_true, ite_false,
        map_one, map_neg]
    · simp only [num, ha, ite_false, originalCoordinateSlice, RingHom.comp_apply,
        real_originalExposedNumerator]
  · intro a
    by_cases ha : a ∈ S
    · simp only [den, ha, ite_true, map_one]
    · simp only [den, ha, ite_false, originalCoordinateSlice, RingHom.comp_apply,
        map_pow, exposedResponseDenominator]

end SkewCornerDescent.Matrix
