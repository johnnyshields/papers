/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.RestorationComponents
import SkewCofactorIndependence.WeightedReadings

/-!
# Degrees of the actual first variations

The ordinary and generator-index degrees asserted after `eq:first-components`
in `shields-2026-skew-cofactor-independence.tex`.  Zero-freeness is required only
for the ordinary marking of cofactors; weighted degrees remain valid even when
Jacobi–Trudi entries are genuine units.
-/

namespace SkewCofactorIndependence
open scoped BigOperators Polynomial
open StrictTriangularPaths

/-- Generator-index weight in the manuscript's positive convention. -/
def indexWeight (j : ℕ+) : ℝ := j.val

/-- The reverse convention is exactly the negative of the positive one. -/
theorem weight_reverseIndex (d : ℕ+ →₀ ℕ) :
    Finsupp.weight reverseIndexWeight d = -Finsupp.weight indexWeight d := by
  simp only [Finsupp.weight_apply, Finsupp.sum, reverseIndexWeight, indexWeight,
    smul_neg, Finset.sum_neg_distrib]

/-- Homogeneity is transported at the weight-convention seam. -/
theorem reverse_homogeneous_iff (p : CompleteRing) (a : ℝ) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight p (-a) ↔
      MvPolynomial.IsWeightedHomogeneous indexWeight p a := by
  constructor <;> intro h d hd
  · have he := h hd
    rw [weight_reverseIndex] at he
    exact neg_injective he
  · rw [weight_reverseIndex, h hd]

/-- Arbitrary difference matrices have the same weighted degree at every permutation. -/
theorem difference_det_reverse_homogeneous {n : ℕ} (a b : Fin n → ℤ) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight
      (Matrix.of (fun i j => complete (a i - b j))).det
      (-((∑ i, a i - ∑ j, b j : ℤ) : ℝ)) := by
  classical
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro σ _
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => complete (a i - b (σ i)))
    (fun i => -((a i - b (σ i) : ℤ) : ℝ))
    (fun i _ => complete_reverse_homogeneous _)
  have he : ∑ i, -((a i - b (σ i) : ℤ) : ℝ) =
      -((∑ i, a i - ∑ j, b j : ℤ) : ℝ) := by
    simp only [Int.cast_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    congr 1
    exact_mod_cast congrArg (fun x : ℤ => (∑ i, a i) - x) (Equiv.sum_comp σ b)
  rw [he] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [Matrix.of_apply, hs, one_smul] using hp
  · simpa [Matrix.of_apply, hs] using hp.neg

/-- Strict return factors have their exact generator-index degree, including vanishing factors. -/
theorem positiveGap_reverse_homogeneous (a b : ℤ) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight
      (positiveGap complete a b) (-((a - b : ℤ) : ℝ)) := by
  unfold positiveGap
  split_ifs
  · exact complete_reverse_homogeneous _
  · exact MvPolynomial.isWeightedHomogeneous_zero ℚ _ _

/-- Marking every nonzero entry gives one marking factor per row. -/
theorem markOrdinary_difference_det {n : ℕ} (a b : Fin n → ℤ)
    (hz : ∀ i j, a i ≠ b j) :
    markOrdinary (Matrix.of (fun i j => complete (a i - b j))).det =
      Polynomial.X ^ n * Polynomial.C
        (Matrix.of (fun i j => complete (a i - b j))).det := by
  rw [markOrdinary.map_det]
  have hm : (Matrix.of (fun i j => complete (a i - b j))).map markOrdinary =
      (Polynomial.X : Polynomial CompleteRing) •
        (Matrix.of (fun i j => complete (a i - b j))).map Polynomial.C := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, markOrdinary_complete, sub_eq_zero, hz i j, ite_false]
  change ((Matrix.of (fun i j => complete (a i - b j))).map markOrdinary).det =
    Polynomial.X ^ n * Polynomial.C
      (Matrix.of (fun i j => complete (a i - b j))).det
  rw [hm, Matrix.det_smul, Fintype.card_fin]
  congr 1
  exact (Polynomial.C.map_det _).symm

/-- Strict return factors always have ordinary marking degree one. -/
theorem markOrdinary_positiveGap (a b : ℤ) :
    markOrdinary (positiveGap complete a b) =
      Polynomial.X * Polynomial.C (positiveGap complete a b) := by
  unfold positiveGap
  split_ifs with h
  · rw [markOrdinary_complete, ite_eq_right (by omega)]
  · simp

namespace BetaDiagram
variable {n : ℕ}

/-- Every signed complementary determinant has its actual generator-index degree. -/
theorem cofactor_reverse_homogeneous_general (D : BetaDiagram (n + 1))
    (i j : Fin (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous reverseIndexWeight (D.cofactor i j)
      (-((D.area - (D.row i - D.col j) : ℤ) : ℝ)) := by
  have h := difference_det_reverse_homogeneous
    (fun k => D.row (i.succAbove k)) (fun k => D.col (j.succAbove k))
  have he : (∑ k, D.row (i.succAbove k)) - (∑ k, D.col (j.succAbove k)) =
      D.area - (D.row i - D.col j) := by
    have hr := Fin.sum_univ_succAbove D.row i
    have hc := Fin.sum_univ_succAbove D.col j
    unfold area
    linarith
  rw [he] at h
  have hm : D.matrix.submatrix i.succAbove j.succAbove =
      Matrix.of (fun k l => complete (D.row (i.succAbove k) - D.col (j.succAbove l))) := rfl
  unfold cofactor
  rw [hm, show (-1 : CompleteRing) ^ (i.val + j.val) =
    MvPolynomial.C ((-1 : ℚ) ^ (i.val + j.val)) by simp]
  exact h.C_mul _

/-- The paper's positive convention for the actual signed complementary degree. -/
theorem cofactor_index_homogeneous (D : BetaDiagram (n + 1))
    (i j : Fin (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous indexWeight (D.cofactor i j)
      ((D.area - (D.row i - D.col j) : ℤ) : ℝ) :=
  (reverse_homogeneous_iff _ _).mp (D.cofactor_reverse_homogeneous_general i j)

/-- The entire first variation has weighted degree equal to the core's area. -/
theorem unitVariation_index_homogeneous (D : BetaDiagram (n + 1)) (z : ℤ) :
    MvPolynomial.IsWeightedHomogeneous indexWeight (D.unitVariation z) (D.area : ℝ) := by
  apply (reverse_homogeneous_iff _ _).mp
  unfold unitVariation
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i _
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j _
  have h := ((D.cofactor_reverse_homogeneous_general i j).mul
    (positiveGap_reverse_homogeneous (D.row i) z)).mul
    (positiveGap_reverse_homogeneous z (D.col j))
  convert h using 1; push_cast; ring

/-- Zero-free cofactors have ordinary marking degree equal to their matrix order. -/
theorem markOrdinary_cofactor (D : BetaDiagram (n + 1)) (hz : D.ZeroFree)
    (i j : Fin (n + 1)) : markOrdinary (D.cofactor i j) =
      Polynomial.X ^ n * Polynomial.C (D.cofactor i j) := by
  have h := markOrdinary_difference_det (fun k => D.row (i.succAbove k))
    (fun k => D.col (j.succAbove k)) (fun k l => hz _ _)
  have hm : D.matrix.submatrix i.succAbove j.succAbove =
      Matrix.of (fun k l => complete (D.row (i.succAbove k) - D.col (j.succAbove l))) := rfl
  simp only [cofactor, map_mul, map_pow, map_neg, map_one, hm, h]
  ring

/-- The exact ordinary marking identity for every first variation, even when it vanishes. -/
theorem markOrdinary_unitVariation (D : BetaDiagram (n + 1)) (hz : D.ZeroFree)
    (z : ℤ) : markOrdinary (D.unitVariation z) =
      Polynomial.X ^ (n + 2) * Polynomial.C (D.unitVariation z) := by
  simp only [unitVariation, map_sum, map_mul, D.markOrdinary_cofactor hz,
    markOrdinary_positiveGap]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, pow_two]
  ring

/-- The coefficient and Mathlib homogeneous-component readings give the same ordinary degree. -/
theorem unitVariation_ordinary_component (D : BetaDiagram (n + 1)) (hz : D.ZeroFree)
    (z : ℤ) (d : ℕ) : MvPolynomial.homogeneousComponent d (D.unitVariation z) =
      if n + 2 = d then D.unitVariation z else 0 := by
  rw [← ordinaryComponent_eq_homogeneousComponent, ordinaryComponent,
    D.markOrdinary_unitVariation hz, mul_comm, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm]

end BetaDiagram
end SkewCofactorIndependence
