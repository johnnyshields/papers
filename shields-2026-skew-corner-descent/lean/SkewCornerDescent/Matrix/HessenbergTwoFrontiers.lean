/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergNormalFrontier

/-!
# The two complete normal-cost frontiers

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact permutation expansion retains both the full-cost residue products
and the first normal jets of the one-shy frontier. Pair interactions and
coincident activities at cost two are not discarded. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- One original permutation contributes its full cost-zero residue or its
one-shy first normal jet. Shorter intervals are killed only by the stated
complete-series independence, never by a frozen inverse approximation. -/
theorem hessenberg_permutation_coeff_deriv_two_frontiers {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) + 1 < m →
      ∀ k, D (PowerSeries.coeff k (A i j)) = 0)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) :
    let lower := Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))
    let upper := Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ))
    D (PowerSeries.coeff m (∏ i, A i (σ i))) =
      if lower.card = m then
        a ^ m • D (∏ i ∈ upper, PowerSeries.constantCoeff (A i (σ i)))
      else if lower.card + 1 = m then
        a ^ (m - 1) • D (PowerSeries.coeff 1 (∏ i ∈ upper, A i (σ i)))
      else 0 := by
  classical
  let lower := Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))
  let upper := Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ))
  have hproduct := hessenberg_permutation_product A σ hσ
    (PowerSeries.X * PowerSeries.C a) hsub
  change (∏ i : Fin n, A i (σ i)) =
    (PowerSeries.X * PowerSeries.C a) ^ lower.card * ∏ i ∈ upper, A i (σ i) at hproduct
  change _ = if lower.card = m then a ^ m • D (∏ i ∈ upper,
    PowerSeries.constantCoeff (A i (σ i))) else if lower.card + 1 = m then
      a ^ (m - 1) • D (PowerSeries.coeff 1 (∏ i ∈ upper, A i (σ i))) else 0
  rw [hproduct, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']
  by_cases hcost : lower.card ≤ m
  · rw [ite_eq_left hcost, ← map_pow, PowerSeries.coeff_C_mul,
      Derivation.leibniz, Derivation.leibniz_pow, ha, smul_zero, smul_zero, smul_zero, add_zero]
    by_cases he : lower.card = m
    · simp only [he, ↓reduceIte, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_prod]
    · rw [ite_eq_right he]
      by_cases hnext : lower.card + 1 = m
      · have hdiff : m - lower.card = 1 := by omega
        have hexp : m - 1 = lower.card := by omega
        rw [ite_eq_left hnext, hdiff, hexp]
      · rw [ite_eq_right hnext]
        have hlt : lower.card + 1 < m := by omega
        have hu : D (PowerSeries.coeff (m - lower.card) (∏ i ∈ upper, A i (σ i))) = 0 := by
          apply coeff_deriv_prod_zero
          intro i hi k _
          have hi' : (i : ℕ) ≤ (σ i : ℕ) := by
            have := (Finset.mem_filter.mp hi).2
            omega
          have hinterval := hessenberg_permutation_interval_cost σ hσ i hi'
          change (σ i : ℕ) - (i : ℕ) ≤ lower.card at hinterval
          exact hshort i (σ i) hi' (by omega) k
        rw [hu, smul_zero]
  · have he : lower.card ≠ m := by omega
    have hnext : lower.card + 1 ≠ m := by omega
    rw [ite_eq_right hcost, map_zero, ite_eq_right he, ite_eq_right hnext]

/-- The entire determinant keeps every original permutation at both adjacent
frontiers. In particular, the cost-two repeated and neighboring pair terms
remain in the formula without an exceptional-case deletion. -/
theorem hessenberg_coeff_deriv_two_frontiers {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) + 1 < m →
      ∀ k, D (PowerSeries.coeff k (A i j)) = 0) :
    D (PowerSeries.coeff m A.det) =
      ∑ σ : Equiv.Perm (Fin n),
        if (∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) then
          let lower := Finset.univ.filter (fun i : Fin n => (σ i : ℕ) < (i : ℕ))
          let upper := Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ))
          (Equiv.Perm.sign σ : ℤ) •
            (if lower.card = m then
              a ^ m • D (∏ i ∈ upper, PowerSeries.constantCoeff (A i (σ i)))
            else if lower.card + 1 = m then
              a ^ (m - 1) • D (PowerSeries.coeff 1 (∏ i ∈ upper, A i (σ i)))
            else 0)
        else 0 := by
  classical
  rw [← Matrix.det_transpose A, Matrix.det_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Units.smul_def, map_zsmul]
  by_cases hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1
  · rw [ite_eq_left hσ,
      hessenberg_permutation_coeff_deriv_two_frontiers D A a ha hsub m hshort σ hσ]
  · have hz : (∏ i : Fin n, A i (σ i)) = 0 := by
      obtain ⟨i, hi⟩ := not_forall.mp hσ
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hA i (σ i) (by omega)
    rw [hz, map_zero, map_zero, ite_eq_right hσ, smul_zero]

end SkewCornerDescent.Matrix
