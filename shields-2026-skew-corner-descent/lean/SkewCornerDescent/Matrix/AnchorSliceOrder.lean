/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposedRootOrders
import SkewCornerDescent.ExposureLabels

/-!
# Root order recovered from actual normalized slices

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
The positive square denominator identifies an off-anchor numerator sign with the strict
order of the original rational roots. No independent response coordinates are introduced.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- A normalized numerator sign at an anchor root is the sign of the difference of the
actual rational roots, provided the original anchor denominator is regular. -/
theorem anchor_slice_sign_implies_root_sign {α : Type*}
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (hp : ∀ i j, j ∈ (realResiduePolynomial N (p i)).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (realResiduePolynomial N (q i)).vars → j < (N : ℕ))
    (a b : {i : α // top i = K}) (positive : Bool) (x : ℕ → ℝ)
    (hqb : MvPolynomial.eval x (realResiduePolynomial N (q b.val)) ≠ 0)
    (hsign :
      let root := rationalAnchorRoot
        (fun a : {i : α // top i = K} => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val)) a x
      0 < (if positive then 1 else -1) * Polynomial.eval root
        (coordinatePolynomial (K : ℕ) x (exposedResponseNumerator N top p q b.val))) :
    responseSign positive
      (rationalAnchorRoot
        (fun a : {i : α // top i = K} => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val)) a x -
      rationalAnchorRoot
        (fun a : {i : α // top i = K} => realResiduePolynomial N (p a.val))
        (fun a => realResiduePolynomial N (q a.val)) b x) := by
  let ap := fun a : {i : α // top i = K} => realResiduePolynomial N (p a.val)
  let aq := fun a : {i : α // top i = K} => realResiduePolynomial N (q a.val)
  let root := rationalAnchorRoot ap aq a x
  let y := anchorAssignment (K : ℕ) (rationalAnchorRoot ap aq) a x
  have hap (i : {i : α // top i = K}) (j : ℕ) (hj : j ∈ (ap i).vars) :
      j < (K : ℕ) := by
    simpa only [ap, i.property] using hp i.val j hj
  have haq (i : {i : α // top i = K}) (j : ℕ) (hj : j ∈ (aq i).vars) :
      j < (K : ℕ) := lt_of_lt_of_le (hq i.val j hj) hNK
  have hqy : MvPolynomial.eval y (aq b) = MvPolynomial.eval x (aq b) := by
    apply eval_polynomial_eq_of_agree_below _ (K : ℕ) (haq b)
    intro j hj
    simp only [y, anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)]
  have hreg : MvPolynomial.eval y (aq b) ≠ 0 := by rw [hqy]; exact hqb
  have hden : 0 < MvPolynomial.eval y (exposedResponseDenominator N q b.val) := by
    rw [exposedResponseDenominator, map_pow]
    exact sq_pos_of_ne_zero hreg
  have hs : 0 < (if positive then (1 : ℝ) else -1) *
      (MvPolynomial.eval y (exposedResponseNumerator N top p q b.val) /
        MvPolynomial.eval y (exposedResponseDenominator N q b.val)) := by
    rw [← mul_div_assoc]
    apply div_pos _ hden
    simpa only [coordinatePolynomial_eval, y, anchorAssignment, root, ap, aq] using hsign
  rw [exposedResponse_fraction N top p q y b.val hreg, b.property] at hs
  have he := anchor_response_eq_normalized_difference (K : ℕ) ap aq hap haq a b x
    1 0 (by norm_num)
  simp only [one_mul, normalizedAnchorLabel, sub_zero, div_one] at he
  rw [he] at hs
  cases positive <;> simpa only [responseSign, Bool.false_eq_true, ite_false,
    ite_true, neg_one_mul, one_mul, neg_pos] using hs

end SkewCornerDescent.Matrix.SelectedCoordinate
