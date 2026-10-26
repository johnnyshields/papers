/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealResponseSlices
import SkewCornerDescent.ExposureLabels

/-!
# Real root order and finite replaced slices

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:peeling`).
The positive square denominator identifies numerator signs with strict root order.
Finite replacements retain every position and take the remaining chamber's sign.
Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

/-- A normalized numerator sign is the strict order of two actual real anchor roots. -/
theorem real_anchor_slice_sign_implies_root_sign {α : Type*}
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (a b : {i : α // top i = K}) (positive : Bool) (x : ℕ → ℝ)
    (hqb : eval x (q b.val) ≠ 0)
    (hsign :
      let root := rationalAnchorRoot (fun a : {i : α // top i = K} => p a.val)
        (fun a => q a.val) a x
      0 < (if positive then 1 else -1) * Polynomial.eval root
        (coordinatePolynomial (K : ℕ) x (realResponseNumerator top p q b.val))) :
    responseSign positive
      (rationalAnchorRoot (fun a : {i : α // top i = K} => p a.val)
        (fun a => q a.val) a x -
      rationalAnchorRoot (fun a : {i : α // top i = K} => p a.val)
        (fun a => q a.val) b x) := by
  let ap := fun a : {i : α // top i = K} => p a.val
  let aq := fun a : {i : α // top i = K} => q a.val
  let root := rationalAnchorRoot ap aq a x
  let y := anchorAssignment (K : ℕ) (rationalAnchorRoot ap aq) a x
  have hap (i : {i : α // top i = K}) (j : ℕ) (hj : j ∈ (ap i).vars) :
      j < (K : ℕ) := by
    simpa only [ap, i.property] using hp i.val j hj
  have haq (i : {i : α // top i = K}) (j : ℕ) (hj : j ∈ (aq i).vars) :
      j < (K : ℕ) := lt_of_lt_of_le (hq i.val j hj) hNK
  have hqy : eval y (aq b) = eval x (aq b) := by
    apply eval_polynomial_eq_of_agree_below _ (K : ℕ) (haq b)
    intro j hj
    simp only [y, anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)]
  have hreg : eval y (aq b) ≠ 0 := by rw [hqy]; exact hqb
  have hden : 0 < eval y (q b.val ^ 2) := by
    rw [map_pow]
    exact sq_pos_of_ne_zero hreg
  have hs : 0 < (if positive then (1 : ℝ) else -1) *
      (eval y (realResponseNumerator top p q b.val) / eval y (q b.val ^ 2)) := by
    rw [← mul_div_assoc]
    apply div_pos _ hden
    simpa only [coordinatePolynomial_eval, y, anchorAssignment, root, ap, aq] using hsign
  rw [realResponseNumerator_fraction top p q y b.val hreg, b.property] at hs
  have he := anchor_response_eq_normalized_difference (K : ℕ) ap aq hap haq a b x
    1 0 (by norm_num)
  simp only [one_mul, normalizedAnchorLabel, sub_zero, div_one] at he
  rw [he] at hs
  cases positive <;> simpa only [responseSign, Bool.false_eq_true, ite_false,
    ite_true, neg_one_mul, one_mul, neg_pos] using hs

/-- The remaining real chamber supplies a regular full-family slice after signed replacement. -/
theorem remainingRealChamber_exposed_slice {α : Type*} [Finite α] [DecidableEq α]
    (S : Finset α) (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+)
    (p q : α → MvPolynomial ℕ ℝ)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ))
    (hanchor : ∃ a : {a : α // a ∉ S}, top a.val = K)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousRealChamber K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive) :
    ∃ a : {a : {a : α // a ∉ S} // top a.val = K},
      let root := rationalAnchorRoot
        (fun a : {a : {a : α // a ∉ S} // top a.val = K} => p a.val.val)
        (fun a => q a.val.val) a x
      let num := fun Y => if Y ∈ S then Polynomial.C (if positive then 1 else -1)
        else coordinatePolynomial (K : ℕ) x (realResponseNumerator top p q Y)
      let den := fun Y => if Y ∈ S then (1 : Polynomial ℝ)
        else coordinatePolynomial (K : ℕ) x (q Y ^ 2)
      Polynomial.eval root (num a.val.val) = 0 ∧
        Polynomial.rootMultiplicity root (num a.val.val) = 1 ∧
        (∀ Y, 0 < Polynomial.eval root (den Y)) ∧
        (∀ Y, Y ≠ a.val.val → 0 < (if positive then 1 else -1) *
          Polynomial.eval root (num Y)) := by
  classical
  obtain ⟨a, hroot, hsimple, hden, hsign⟩ := simultaneousRealChamber_exposed_slice
    N K hNK (fun a : {a : α // a ∉ S} => top a.val)
    (fun a => p a.val) (fun a => q a.val)
    (fun a j hj => hp a.val j hj) (fun a j hj => hq a.val j hj)
    hanchor positive x hx
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · simpa only [a.val.property, ite_false, realResponseNumerator] using hroot
  · simpa only [a.val.property, ite_false, realResponseNumerator] using hsimple
  · intro Y
    by_cases hY : Y ∈ S
    · simp only [hY, ite_true, Polynomial.eval_one]
      exact zero_lt_one
    · simpa only [hY, ite_false] using hden ⟨Y, hY⟩
  · intro Y hYa
    by_cases hY : Y ∈ S
    · cases positive <;> norm_num [hY]
    · have hne : (⟨Y, hY⟩ : {Y : α // Y ∉ S}) ≠ a.val := by
        intro hz
        exact hYa (congrArg Subtype.val hz)
      simpa only [hY, ite_false, realResponseNumerator] using hsign ⟨Y, hY⟩ hne

end SkewCornerDescent
