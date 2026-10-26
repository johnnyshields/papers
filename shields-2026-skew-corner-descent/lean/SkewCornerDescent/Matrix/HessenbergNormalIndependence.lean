/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.HessenbergPermutationCost
import SkewCornerDescent.Matrix.NormalCoefficientLeibniz

/-!
# Full Hessenberg determinant exclusion before a fresh interval cost

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Every permutation term is retained. Long upper intervals vanish by their
forced selected-subdiagonal cost; shorter intervals retain all normal jets.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- A complete Hessenberg permutation term is generator-independent through order `m`
when all eligible upper intervals are. Long intervals are excluded by their actual cost,
not by replacing a full response with its constant term. -/
theorem hessenberg_permutation_coeff_deriv_zero {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ)
    (hnear : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) ≤ m →
      ∀ k, k ≤ m → D (PowerSeries.coeff k (A i j)) = 0)
    (σ : Equiv.Perm (Fin n)) :
    D (PowerSeries.coeff m (∏ i : Fin n, A i (σ i))) = 0 := by
  classical
  by_cases hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1
  · let lower := Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))
    let upper := Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ))
    have hproduct := hessenberg_permutation_product A σ hσ
      (PowerSeries.X * PowerSeries.C a) hsub
    change (∏ i : Fin n, A i (σ i)) =
      (PowerSeries.X * PowerSeries.C a) ^ lower.card * ∏ i ∈ upper, A i (σ i) at hproduct
    rw [hproduct]
    by_cases hcost : lower.card ≤ m
    · apply coeff_deriv_mul_zero D _ _ m
      · intro k hk
        apply coeff_deriv_pow_zero D _ _ _
        intro l hl
        rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
        split_ifs <;> simp [ha]
      · intro k hk
        apply coeff_deriv_prod_zero D upper _ k
        intro i hi l hl
        have hi' : (i : ℕ) ≤ (σ i : ℕ) := by
          have := (Finset.mem_filter.mp hi).2
          omega
        apply hnear i (σ i) hi' _ l (hl.trans hk)
        exact (hessenberg_permutation_interval_cost σ hσ i hi').trans hcost
    · rw [mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']
      simp [hcost]
  · push Not at hσ
    obtain ⟨i, hi⟩ := hσ
    have hz : (∏ k : Fin n, A k (σ k)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hA i (σ i) (by omega)
    rw [hz, map_zero, map_zero]

/-- The entire determinant inherits the minimum-cost exclusion. The premise concerns only
upper intervals eligible at this order; no condition is imposed on any longer interval.

**Differs from the paper's route.** The complete permutation expansion and displacement
balance supply the cost bound, rather than recursively contracting the first interval. -/
theorem hessenberg_coeff_deriv_zero {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ)
    (hnear : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) ≤ m →
      ∀ k, k ≤ m → D (PowerSeries.coeff k (A i j)) = 0) :
    D (PowerSeries.coeff m A.det) = 0 := by
  classical
  rw [← Matrix.det_transpose A, Matrix.det_apply, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  simp only [Matrix.transpose_apply, Units.smul_def, map_zsmul]
  rw [hessenberg_permutation_coeff_deriv_zero D A hA a ha hsub m hnear σ, smul_zero]

end SkewCornerDescent.Matrix
