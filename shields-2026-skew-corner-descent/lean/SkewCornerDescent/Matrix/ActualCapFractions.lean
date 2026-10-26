/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposureCaps
import SkewCornerDescent.Matrix.OriginalExposedPolynomials

/-!
# Original true-cap fractions and chamber positivity

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `thm:dual-period`).
Both cap fractions are built from the original response representatives. Their regular
square denominators and positive product are produced from the actual chamber, including
coincident cap classes. No independent cap-sign or cap-regularity binder is needed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial SelectedCoordinate

/-- The two original cap numerators, with positive square-denominator normalization. -/
noncomputable def originalCapNumerator {α : Type*} (N : ℕ+) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (left right : α) :
    OtherPolynomial N :=
  originalExposedNumerator N top p q htop left *
    originalExposedNumerator N top p q htop right

/-- Equal cap classes retain both occurrences in their common denominator. -/
noncomputable def originalCapDenominator {α : Type*} (N : ℕ+)
    (q : α → OtherPolynomial N) (left right : α) : OtherPolynomial N :=
  q left ^ 2 * q right ^ 2

/-- The fraction is the actual original product, not just a sign-equivalent quantity. -/
theorem originalCapFraction_eq {α : Type*} (N : ℕ+) (top : α → ℕ+)
    (p q : α → OtherPolynomial N) (htop : ∀ a, top a ≠ N) (left right : α)
    (hl : q left ≠ 0) (hr : q right ≠ 0) :
    let ι := algebraMap (OtherPolynomial N) (OtherField N)
    ι (originalCapNumerator N top p q htop left right) /
        ι (originalCapDenominator N q left right) =
      (residueGenerator N ⟨top left, htop left⟩ + ι (p left) / ι (q left)) *
        (residueGenerator N ⟨top right, htop right⟩ + ι (p right) / ι (q right)) := by
  dsimp only
  simp only [originalCapNumerator, originalCapDenominator, map_mul]
  rw [← div_mul_div_comm]
  rw [originalExposedNumerator_fraction N top p q htop left hl,
    originalExposedNumerator_fraction N top p q htop right hr]

namespace SelectedCoordinate

/-- An actual chamber makes the original cap denominator regular and its fraction positive
at the unchanged lower-coordinate assignment. Both caps have protected tops below `K`. -/
theorem simultaneousActualChamber_cap_fraction_pos {α : Type*}
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (htop : ∀ a, top a ≠ N)
    (hp : ∀ a j, j ∈ (realResiduePolynomial N (p a)).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (realResiduePolynomial N (q a)).vars → j < (N : ℕ))
    (left right : α) (hl : top left < K) (hr : top right < K)
    (a : {i : α // top i = K}) (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive) :
    MvPolynomial.eval x
        (realResiduePolynomial N (originalCapDenominator N q left right)) ≠ 0 ∧
      0 < MvPolynomial.eval x
          (realResiduePolynomial N (originalCapNumerator N top p q htop left right)) /
        MvPolynomial.eval x
          (realResiduePolynomial N (originalCapDenominator N q left right)) := by
  let y := anchorAssignment (K : ℕ)
    (rationalAnchorRoot (fun a => realResiduePolynomial N (p a.val))
      (fun a => realResiduePolynomial N (q a.val))) a x
  have he (P : MvPolynomial ℕ ℝ) (hP : ∀ j ∈ P.vars, j < (K : ℕ)) :
      MvPolynomial.eval y P = MvPolynomial.eval x P := by
    apply eval_polynomial_eq_of_agree_below P K hP
    intro j hj
    simp only [y, anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hj)]
  have hqeq (i : α) :
      MvPolynomial.eval y (realResiduePolynomial N (q i)) =
        MvPolynomial.eval x (realResiduePolynomial N (q i)) :=
    he _ (fun j hj => lt_of_lt_of_le (hq i j hj) hNK)
  have hresponse (i : α) (hi : top i < K) :
      rationalTriangularResponse (top i : ℕ)
          (realResiduePolynomial N (p i)) (realResiduePolynomial N (q i)) y =
        rationalTriangularResponse (top i : ℕ)
          (realResiduePolynomial N (p i)) (realResiduePolynomial N (q i)) x := by
    have hpeq := he (realResiduePolynomial N (p i))
      (fun j hj => lt_trans (hp i j hj) hi)
    dsimp only [rationalTriangularResponse]
    rw [hpeq, hqeq]
    change Function.update x (K : ℕ) _ (top i : ℕ) + _ = _
    rw [Function.update_of_ne (show (top i : ℕ) ≠ (K : ℕ) from ne_of_lt hi)]
  have hleft := hx.2.2 a ⟨left, ne_of_lt hl⟩
  have hright := hx.2.2 a ⟨right, ne_of_lt hr⟩
  change MvPolynomial.eval y (realResiduePolynomial N (q left)) ≠ 0 ∧ _ at hleft
  change MvPolynomial.eval y (realResiduePolynomial N (q right)) ≠ 0 ∧ _ at hright
  have hql : MvPolynomial.eval x (realResiduePolynomial N (q left)) ≠ 0 := by
    simpa only [hqeq] using hleft.1
  have hqr : MvPolynomial.eval x (realResiduePolynomial N (q right)) ≠ 0 := by
    simpa only [hqeq] using hright.1
  have hls : responseSign positive (rationalTriangularResponse (top left : ℕ)
      (realResiduePolynomial N (p left)) (realResiduePolynomial N (q left)) y) := hleft.2
  have hrs : responseSign positive (rationalTriangularResponse (top right : ℕ)
      (realResiduePolynomial N (p right)) (realResiduePolynomial N (q right)) y) := hright.2
  rw [hresponse left hl] at hls
  rw [hresponse right hr] at hrs
  have hproduct : 0 < rationalTriangularResponse (top left : ℕ)
        (realResiduePolynomial N (p left)) (realResiduePolynomial N (q left)) x *
      rationalTriangularResponse (top right : ℕ)
        (realResiduePolynomial N (p right)) (realResiduePolynomial N (q right)) x :=
    signed_cap_product_pos positive hls hrs
  constructor
  · simpa only [originalCapDenominator, map_mul, map_pow] using
      mul_ne_zero (pow_ne_zero 2 hql) (pow_ne_zero 2 hqr)
  · simp only [originalCapNumerator, originalCapDenominator, map_mul, map_pow,
      real_originalExposedNumerator]
    rw [← div_mul_div_comm]
    have hfracL := exposedResponse_fraction N top p q x left hql
    have hfracR := exposedResponse_fraction N top p q x right hqr
    simp only [exposedResponseDenominator, map_pow] at hfracL hfracR
    rw [hfracL, hfracR]
    exact hproduct

end SelectedCoordinate
end SkewCornerDescent.Matrix
