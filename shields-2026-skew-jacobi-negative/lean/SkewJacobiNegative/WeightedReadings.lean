/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED:
--   skew-cofactor-independence/lean/SkewCofactorIndependence/WeightedReadings.lean
import SkewJacobiNegative.CornerAlgebra
import Vendor.AlgebraicCombinatorics.DeterminantsBasic

/-!
# Weighted degrees of actual Schur determinants and cofactors

Formalizes `eq:cofactor-degree` and the degree separation in `sec:cofactors`
of `shields-2026-skew-cofactor-independence.tex`.  Every degree is produced
from the actual beta entries and determinant expansion.  Sorry-free.
-/

namespace SkewJacobiNegative

open scoped BigOperators

/-- The reverse index degree of a complete entry, also valid for zero and negative indices. -/
theorem complete_reverse_homogeneous (k : ℤ) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight (complete k) (-(k : ℝ)) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [complete_of_neg hk]
    exact MvPolynomial.isWeightedHomogeneous_zero ℚ _ _
  · subst k
    simp only [complete_zero, Int.cast_zero, neg_zero]
    exact MvPolynomial.isWeightedHomogeneous_one ℚ _
  · rw [complete_of_pos hk]
    have he : (k.toNat : ℝ) = (k : ℝ) := by
      exact_mod_cast (show (k.toNat : ℤ) = k by omega)
    have h := MvPolynomial.isWeightedHomogeneous_X ℚ reverseIndexWeight
      (⟨k.toNat, by omega⟩ : ℕ+)
    change MvPolynomial.IsWeightedHomogeneous reverseIndexWeight
      (MvPolynomial.X ⟨k.toNat, by omega⟩) (-(k.toNat : ℝ)) at h
    rw [he] at h
    exact h

namespace BetaDiagram

variable {n : ℕ}

/-- The number of cells, expressed by the difference of the full beta sums. -/
def area (D : BetaDiagram n) : ℤ := ∑ i, D.row i - ∑ i, D.col i

/-- The weighted degree is the same at every permutation in the determinant expansion. -/
theorem permutation_reverse_degree (D : BetaDiagram n) (σ : Equiv.Perm (Fin n)) :
    (∑ i, -((D.row i - D.col (σ i) : ℤ) : ℝ)) = -(D.area : ℝ) := by
  have he : ∑ i, D.col (σ i) = ∑ i, D.col i := Equiv.sum_comp σ D.col
  have hr : (∑ i, D.row i - ∑ i, D.col (σ i)) = D.area := by
    rw [he]
    rfl
  simp only [Int.cast_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  congr 1
  exact_mod_cast hr

/-- Every actual Schur polynomial has weighted degree equal to its geometric area. -/
theorem schur_reverse_homogeneous (D : BetaDiagram n) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight D.schur (-(D.area : ℝ)) := by
  classical
  unfold schur
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro σ hσ
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => complete (D.row i - D.col (σ i)))
    (fun i => -((D.row i - D.col (σ i) : ℤ) : ℝ))
    (fun i _ => complete_reverse_homogeneous _)
  rw [D.permutation_reverse_degree] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [matrix, Matrix.of_apply, hs, one_smul] using hp
  · simpa [matrix, Matrix.of_apply, hs] using hp.neg

/-- Any complementary board of a dense diagram has valid strict beta lists. -/
def deleteSite (D : BetaDiagram (n + 1)) (hD : D.Dense)
    (i j : Fin (n + 1)) : BetaDiagram n where
  row k := D.row (i.succAbove k)
  col k := D.col (j.succAbove k)
  row_strictAnti := by
    intro a b hab
    exact D.row_strictAnti ((Fin.strictMono_succAbove i) hab)
  col_strictAnti := by
    intro a b hab
    exact D.col_strictAnti ((Fin.strictMono_succAbove j) hab)
  row_nonempty k := hD (i.succAbove k) (j.succAbove k)

/-- The signed cofactor is the actual signed complementary Schur determinant. -/
theorem cofactor_eq_deleteSite (D : BetaDiagram (n + 1)) (hD : D.Dense)
    (i j : Fin (n + 1)) :
    D.cofactor i j = (-1) ^ (i.val + j.val) * (D.deleteSite hD i j).schur := rfl

/-- Deleting a site removes exactly its row beta and column beta from the area. -/
theorem deleteSite_area (D : BetaDiagram (n + 1)) (hD : D.Dense)
    (i j : Fin (n + 1)) :
    (D.deleteSite hD i j).area = D.area - (D.row i - D.col j) := by
  have hr := Fin.sum_univ_succAbove D.row i
  have hc := Fin.sum_univ_succAbove D.col j
  unfold area deleteSite
  dsimp only
  linarith

/-- Every signed cofactor of a dense diagram is nonzero, including the empty complementary minor. -/
theorem cofactor_ne_zero (D : BetaDiagram (n + 1)) (hD : D.Dense)
    (i j : Fin (n + 1)) : D.cofactor i j ≠ 0 := by
  rw [cofactor_eq_deleteSite D hD]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (D.deleteSite hD i j).schur_ne_zero

/-- The exact signed-cofactor degree formula of the manuscript. -/
theorem cofactor_reverse_homogeneous (D : BetaDiagram (n + 1)) (hD : D.Dense)
    (i j : Fin (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight (D.cofactor i j)
      (-((D.area - (D.row i - D.col j) : ℤ) : ℝ)) := by
  rw [cofactor_eq_deleteSite D hD]
  have h := (D.deleteSite hD i j).schur_reverse_homogeneous
  rw [deleteSite_area] at h
  have he : (-1 : CompleteRing) ^ (i.val + j.val) =
      MvPolynomial.C ((-1 : ℚ) ^ (i.val + j.val)) := by simp
  rw [he]
  exact h.C_mul _

end BetaDiagram
end SkewJacobiNegative
