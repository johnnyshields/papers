/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Inj

/-!
# The adjugate form of the cap numerator

The numerator `N_A = C - (z^{Y_j}) adj(A) b` of the manuscript equals the bordered determinant
`num`.  Expanding the bordered determinant along its last row exhibits the coefficient of
`z^{Y_j}` as `±` the board with column `j` replaced by `b` (moved to the end), and the cofactor
expansion of that board along its last column is the `j`-th entry of `adj(A) b`.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

namespace WeakCap

variable {r : ℕ} (c : WeakCap r)

/-- The vector `adj(A) b`. -/
noncomputable def adjVec : Fin r → CompleteRing :=
  (betaBoard c.X c.Y).adjugate.mulVec fun i => complete (c.X i)

/-- The cap numerator `N_A = C - (z^{Y_j}) adj(A) b` in the joint polynomial ring. -/
noncomputable def numerator : J :=
  ι c.detA - ∑ j, zJ ^ (c.Y j).toNat * ι (c.adjVec j)

theorem minor_castSucc {n : ℕ} (c : WeakCap (n + 1)) (j : Fin (n + 1)) :
    (-1 : CompleteRing) ^ (n + 1 + (j : ℕ)) * c.minor j.castSucc = - c.adjVec j := by
  unfold minor adjVec
  rw [Matrix.det_succ_column _ (Fin.last n), Finset.mul_sum, Matrix.mulVec, dotProduct,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : betaBoard c.X (c.cols ∘ j.castSucc.succAbove) i (Fin.last n) = complete (c.X i) := by
    simp [betaBoard]
  have hA : (betaBoard c.X (c.cols ∘ j.castSucc.succAbove)).submatrix i.succAbove
      (Fin.last n).succAbove = (betaBoard c.X c.Y).submatrix i.succAbove j.succAbove := by
    refine Matrix.ext fun a k => ?_
    simp [betaBoard]
  rw [hb, hA, Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hs : (-1 : CompleteRing) ^ (n + 1 + (j : ℕ)) * (-1) ^ ((i : ℕ) + ((Fin.last n : Fin (n + 1)) : ℕ))
      = - (-1) ^ ((i : ℕ) + (j : ℕ)) := by
    rw [← pow_add, Fin.val_last]
    have : n + 1 + (j : ℕ) + ((i : ℕ) + n) = 2 * n + ((i : ℕ) + (j : ℕ)) + 1 := by ring
    rw [this, pow_succ, pow_add, pow_mul]
    simp
  linear_combination (complete (c.X i) *
    ((betaBoard c.X c.Y).submatrix i.succAbove j.succAbove).det) * hs

theorem numerator_eq_num : c.numerator = c.num := by
  rcases r with _ | n
  · rw [numerator, num_zero, detA_zero]
    simp
  · have hs : ∀ j : Fin (n + 1), zJ ^ (c.cols j.castSucc).toNat *
        ι ((-1 : CompleteRing) ^ (n + 1 + ((j.castSucc : Fin (n + 2)) : ℕ)) *
          c.minor j.castSucc) = - (zJ ^ (c.Y j).toNat * ι (c.adjVec j)) := by
      intro j
      rw [cols_castSucc, Fin.val_castSucc, c.minor_castSucc j, map_neg]
      ring
    have hl : zJ ^ (c.cols (Fin.last (n + 1))).toNat *
        ι ((-1 : CompleteRing) ^ (n + 1 + ((Fin.last (n + 1) : Fin (n + 2)) : ℕ)) *
          c.minor (Fin.last (n + 1))) = ι c.detA := by
      rw [cols_last, minor_last, Fin.val_last, ← two_mul, pow_mul]
      simp
    rw [num_eq_sum, Fin.sum_univ_castSucc, numerator, Finset.sum_congr rfl fun j _ => hs j,
      hl, Finset.sum_neg_distrib]
    ring

end WeakCap

end SkewCoframeRigidity.CapRecognition
