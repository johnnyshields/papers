/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.WeightedOperator
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.Determinant

/-!
# The weighted derivation on a Jacobi–Trudi determinant

«The algebra map and the weighted operator» (`eq:weighted-beta-moves`) of
`shields-2026-skew-marked-factor.tex`.
For ordered beta lists `a`, `b` of equal length, `V_r det(h_{a_i - b_j})` is the sum over rows of
`(a_i - r)` times the determinant with `a_i` replaced by `a_i - r`, minus the sum over columns of
`b_j` times the determinant with `b_j` replaced by `b_j + r`.  Every replacement keeps its
position.  The identity is stated for all integer entries, with `h_0 = 1` and `h_j = 0` for
`j < 0`.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.MN MvPolynomial

/-- `V_r h_k = (k - r) h_{k-r}` for every integer `k`, including the boundary cases. -/
theorem wDeriv_hh (r : ℕ) (k : ℤ) :
    wDeriv r (hh k) = ((k - r : ℤ) : Lambda) * hh (k - r) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [hh_of_neg hk, hh_of_neg (by omega : k - r < 0)]; simp
  · subst hk
    rw [hh_zero, Derivation.map_one_eq_zero]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · rw [hh_of_neg (by omega : (0 : ℤ) - r < 0)]; simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
    have hn : 0 < n := by omega
    rw [hh_natCast, wDeriv_hPos r hn]
    by_cases hrn : r < n
    · rw [ite_eq_left hrn, show (n : ℤ) - r = ((n - r : ℕ) : ℤ) by omega, hh_natCast]
      simp [Nat.cast_sub hrn.le]
    · rw [ite_eq_right hrn]
      rcases Nat.lt_or_ge n r with h | h
      · rw [hh_of_neg (by omega : (n : ℤ) - r < 0)]; simp
      · have : (n : ℤ) - r = 0 := by omega
        rw [this]; simp

/-- The derivative of a determinant of a matrix, column by column. -/
theorem wDeriv_det {M : ℕ} (A : Matrix (Fin M) (Fin M) Lambda) (r : ℕ) :
    wDeriv r A.det = ∑ j : Fin M, (A.updateCol j fun i => wDeriv r (A i j)).det :=
  derivation_det (wDeriv r) A

/-- A column-weighted replacement sum equals the row-weighted replacement sum. -/
theorem sum_updateCol_weight_eq {M : ℕ} (A N : Matrix (Fin M) (Fin M) Lambda)
    (w : Fin M → Lambda) :
    ∑ j : Fin M, (A.updateCol j fun i => w i * N i j).det =
      ∑ i : Fin M, w i * (A.updateRow i (N i)).det := by
  have h1 : ∀ (j : Fin M) (c : Fin M → Lambda),
      (A.updateCol j c).det = (A.adjugate.mulVec c) j := fun j c => by
    rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  have h2 : ∀ (i : Fin M) (c : Fin M → Lambda),
      (A.updateRow i c).det = (A.adjugate.transpose.mulVec c) i := fun i c => by
    have e : (A.updateRow i c).det = (A.transpose.updateCol i c).det := by
      rw [Matrix.updateCol_transpose, Matrix.det_transpose]
    rw [e, show A.adjugate.transpose = A.transpose.adjugate from Matrix.adjugate_transpose A,
      ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  simp only [h1, h2, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The weighted beta moves** (`eq:weighted-beta-moves`): `V_r` of a Jacobi–Trudi determinant is
the row-weighted sum of the determinants with one `a_i` lowered by `r`, minus the column-weighted
sum of those with one `b_j` raised by `r`.  Each replacement stays in its original position. -/
theorem wDeriv_jtDet {M : ℕ} (r : ℕ) (a b : Fin M → ℤ) :
    wDeriv r (jtDet a b) =
      ∑ i : Fin M, ((a i - r : ℤ) : Lambda) * jtDet (Function.update a i (a i - r)) b -
      ∑ j : Fin M, ((b j : ℤ) : Lambda) * jtDet a (Function.update b j (b j + r)) := by
  unfold jtDet
  set A : Matrix (Fin M) (Fin M) Lambda := Matrix.of fun i j => hh (a i - b j) with hA
  set N : Matrix (Fin M) (Fin M) Lambda := Matrix.of fun i j => hh (a i - r - b j) with hN
  rw [wDeriv_det]
  have hcol : ∀ j : Fin M, (A.updateCol j fun i => wDeriv r (A i j)).det =
      (A.updateCol j fun i => ((a i - r : ℤ) : Lambda) * N i j).det -
      ((b j : ℤ) : Lambda) * (A.updateCol j fun i => N i j).det := by
    intro j
    have : (fun i => wDeriv r (A i j)) = (fun i => ((a i - r : ℤ) : Lambda) * N i j) +
        (-((b j : ℤ) : Lambda)) • (fun i => N i j) := by
      ext i
      simp only [hA, hN, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, wDeriv_hh, smul_eq_mul]
      rw [show a i - b j - r = a i - r - b j by ring]
      push_cast
      ring
    rw [this, Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
    ring
  have hrow : ∀ i : Fin M, A.updateRow i (N i) = Matrix.of fun i' j =>
      hh ((Function.update a i (a i - r)) i' - b j) := by
    intro i; ext i' j
    by_cases h : i' = i
    · subst h; simp [hA, hN, Matrix.updateRow_self]
    · simp [hA, Matrix.updateRow_ne h, Function.update_of_ne h]
  have hcolb : ∀ j : Fin M, A.updateCol j (fun i => N i j) = Matrix.of fun i j' =>
      hh (a i - (Function.update b j (b j + r)) j') := by
    intro j; ext i j'
    by_cases h : j' = j
    · subst h; simp [hA, hN, Matrix.updateCol_self]; congr 1; ring
    · simp [hA, Matrix.updateCol_ne h, Function.update_of_ne h]
  simp only [hcol, Finset.sum_sub_distrib]
  rw [sum_updateCol_weight_eq]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcolb]

end SkewMarkedFactor
