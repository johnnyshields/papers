/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.HessenbergNormalIndependence

/-!
# Exact first-fresh coefficient of a full Hessenberg permutation term

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Only terms whose selected-subdiagonal count equals the requested order can
contribute the first fresh derivative. Their complete constant upper product
retains every occurrence and every exterior cap.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- Exact signed-interval frontier before summing permutation terms. Independence is
required only of strictly shorter upper intervals, at every normal order. -/
theorem hessenberg_permutation_coeff_deriv_frontier {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      ∀ k, D (PowerSeries.coeff k (A i j)) = 0)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) :
    D (PowerSeries.coeff m (∏ i : Fin n, A i (σ i))) =
      if (Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))).card = m then
        a ^ m • D (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ)),
          PowerSeries.constantCoeff (A i (σ i)))
      else 0 := by
  classical
  let lower := Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))
  let upper := Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ))
  have hproduct := hessenberg_permutation_product A σ hσ
    (PowerSeries.X * PowerSeries.C a) hsub
  change (∏ i : Fin n, A i (σ i)) =
    (PowerSeries.X * PowerSeries.C a) ^ lower.card * ∏ i ∈ upper, A i (σ i) at hproduct
  change _ = if lower.card = m then a ^ m • D (∏ i ∈ upper,
    PowerSeries.constantCoeff (A i (σ i))) else 0
  rw [hproduct, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']
  by_cases hcost : lower.card ≤ m
  · rw [ite_eq_left hcost, ← map_pow, PowerSeries.coeff_C_mul,
      Derivation.leibniz, Derivation.leibniz_pow, ha, smul_zero, smul_zero, smul_zero,
      add_zero]
    by_cases he : lower.card = m
    · simp only [he, ↓reduceIte, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_prod]
    · rw [ite_eq_right he]
      have hlt : lower.card < m := by omega
      have hu : D (PowerSeries.coeff (m - lower.card) (∏ i ∈ upper, A i (σ i))) = 0 := by
        apply coeff_deriv_prod_zero
        intro i hi k _
        have hi' : (i : ℕ) ≤ (σ i : ℕ) := by
          have := (Finset.mem_filter.mp hi).2
          omega
        exact hshort i (σ i) hi'
          ((hessenberg_permutation_interval_cost σ hσ i hi').trans_lt hlt) k
      rw [hu, smul_zero]
  · have he : lower.card ≠ m := by omega
    rw [ite_eq_right hcost, map_zero, ite_eq_right he]

/-- The full first-fresh determinant derivative is the exact cost-frontier sum. Each term
keeps all upper constant responses, so its later cyclic interpretation retains multiplicity.

**Differs from the paper's route.** The complete permutation expansion isolates the exact
cost frontier, rather than recursively contracting the first interval. -/
theorem hessenberg_coeff_deriv_frontier {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      ∀ k, D (PowerSeries.coeff k (A i j)) = 0) :
    D (PowerSeries.coeff m A.det) =
      ∑ σ : Equiv.Perm (Fin n),
        if (∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) ∧
            (Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))).card = m then
          (Equiv.Perm.sign σ : ℤ) •
            (a ^ m • D (∏ i ∈ Finset.univ.filter
              (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ)),
                PowerSeries.constantCoeff (A i (σ i))))
        else 0 := by
  classical
  rw [← Matrix.det_transpose A, Matrix.det_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Units.smul_def, map_zsmul]
  by_cases hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1
  · rw [hessenberg_permutation_coeff_deriv_frontier D A a ha hsub m hshort σ hσ]
    split_ifs <;> simp_all
  · have hz : (∏ i : Fin n, A i (σ i)) = 0 := by
      obtain ⟨i, hi⟩ := not_forall.mp hσ
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hA i (σ i) (by omega)
    simp [hσ, hz]

end SkewCornerDescent.Matrix
