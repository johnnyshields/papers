/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.HessenbergNormalFrontier
import SkewCornerDescent.Matrix.HessenbergIntervalPermutation
import SkewCornerDescent.Matrix.HessenbergIntervalSum

/-!
# Literal interval contraction of a first-fresh permutation

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The entire exterior diagonal product is retained while the unique long interval
is differentiated. Every literal position remains an occurrence.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- Removing the forward start from the upper positions of an interval cycle leaves
exactly the original positions outside its closed interval. -/
theorem inverse_interval_cycle_upper_erase {n : ℕ} (i j : Fin n) (hij : i ≤ j) :
    (Finset.univ.filter (fun k : Fin n =>
      ¬ ((Fin.cycleIcc i j).symm k : ℕ) < (k : ℕ))).erase i =
      Finset.univ.filter (fun k : Fin n => k < i ∨ j < k) := by
  classical
  ext k
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [inverse_interval_cycle_apply i j hij k]
  split_ifs with hki hwin
  · subst k
    simp [not_lt_of_ge hij]
  · have hne := Fin.val_ne_of_ne hki
    change _ ↔ (k : ℕ) < (i : ℕ) ∨ (j : ℕ) < (k : ℕ)
    omega
  · have hne := Fin.val_ne_of_ne hki
    change _ ↔ (k : ℕ) < (i : ℕ) ∨ (j : ℕ) < (k : ℕ)
    omega

/-- On the exact interval frontier, the derivative is the long entry's derivative
multiplied by every exterior diagonal response, including both true caps. -/
theorem inverse_interval_cycle_upper_derivative {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) F)
    (i j : Fin n) (hij : i ≤ j)
    (hdiag : ∀ k : Fin n, D (A k k) = 0) :
    D (∏ k ∈ Finset.univ.filter (fun k : Fin n =>
      ¬ ((Fin.cycleIcc i j).symm k : ℕ) < (k : ℕ)),
        A k ((Fin.cycleIcc i j).symm k)) =
      (∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i ∨ j < k), A k k) • D (A i j) := by
  classical
  let σ := (Fin.cycleIcc i j).symm
  have hi : σ i = j := by
    apply Fin.ext
    simpa only [σ, ite_true, eq_self] using inverse_interval_cycle_apply i j hij i
  have hfixed : ∀ k : Fin n, k < i ∨ j < k → σ k = k := by
    intro k hk
    apply Fin.ext
    rw [inverse_interval_cycle_apply i j hij k]
    have hki : k ≠ i := by
      intro he
      subst k
      exact hk.elim (lt_irrefl _) (fun h => (not_lt_of_ge hij) h)
    rw [ite_eq_right hki, ite_eq_right]
    rcases hk with hk | hk <;> change _ at hk <;> omega
  have he := inverse_interval_cycle_upper_erase i j hij
  have hprod : (∏ k ∈ (Finset.univ.filter (fun k : Fin n =>
      ¬ (σ k : ℕ) < (k : ℕ))).erase i, A k (σ k)) =
      ∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i ∨ j < k), A k k := by
    rw [show (Finset.univ.filter (fun k : Fin n => ¬ (σ k : ℕ) < (k : ℕ))).erase i =
      Finset.univ.filter (fun k : Fin n => k < i ∨ j < k) from he]
    apply Finset.prod_congr rfl
    intro k hk
    rw [hfixed k (Finset.mem_filter.mp hk).2]
  have hmem : i ∈ Finset.univ.filter (fun k : Fin n => ¬ (σ k : ℕ) < (k : ℕ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
    exact not_lt_of_ge hij
  rw [deriv_prod_single D _ _ i hmem, hprod, hi]
  intro k hk hki
  have hk' : k ∈ (Finset.univ.filter (fun k : Fin n => ¬ (σ k : ℕ) < (k : ℕ))).erase i :=
    Finset.mem_erase.mpr ⟨hki, hk⟩
  rw [he] at hk'
  rw [hfixed k (Finset.mem_filter.mp hk').2]
  exact hdiag k

/-- A frontier permutation with no cost-exhausting forward interval contributes nothing:
all its upper constants are independently below the first fresh order. -/
theorem hessenberg_frontier_without_long_interval {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) F)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1) (m : ℕ)
    (hcost : (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      D (A i j) = 0)
    (hlong : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) → (σ i : ℕ) - (i : ℕ) ≠ m) :
    D (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (σ i : ℕ) < (i : ℕ)),
      A i (σ i)) = 0 := by
  classical
  apply deriv_prod_zero
  intro i hi
  have hi' : (i : ℕ) ≤ (σ i : ℕ) := by
    have := (Finset.mem_filter.mp hi).2
    omega
  apply hshort i (σ i) hi'
  have hle := hessenberg_permutation_interval_cost σ hσ i hi'
  rw [hcost] at hle
  have hne := hlong i hi'
  omega

/-- A cost-exhausting interval contracts the complete first-fresh coefficient to the
long constant entry and the full exterior diagonal product. -/
theorem hessenberg_permutation_coeff_deriv_interval {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ) (hm : 0 < m)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      ∀ k, D (PowerSeries.coeff k (A i j)) = 0)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (hcost : (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m)
    (i : Fin n) (hi : (i : ℕ) ≤ (σ i : ℕ))
    (hlong : (σ i : ℕ) - (i : ℕ) = m) :
    D (PowerSeries.coeff m (∏ k : Fin n, A k (σ k))) =
      a ^ m • ((∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i ∨ σ i < k),
        PowerSeries.constantCoeff (A k k)) • D (PowerSeries.constantCoeff (A i (σ i)))) := by
  classical
  rw [hessenberg_permutation_coeff_deriv_frontier D A a ha hsub m hshort σ hσ,
    ite_eq_left hcost]
  have he := hessenberg_permutation_eq_interval_cycle σ hσ i hi (hlong.trans hcost.symm)
  have hd := inverse_interval_cycle_upper_derivative D
    (fun k l => PowerSeries.constantCoeff (A k l)) i (σ i) hi
    (fun k => by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hshort k k (by omega) (by simpa only [Nat.sub_self] using hm) 0)
  have hleft : (∏ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (σ k : ℕ) < (k : ℕ)),
      PowerSeries.constantCoeff (A k (σ k))) =
      ∏ k ∈ Finset.univ.filter (fun k : Fin n =>
        ¬ ((Fin.cycleIcc i (σ i)).symm k : ℕ) < (k : ℕ)),
          PowerSeries.constantCoeff (A k ((Fin.cycleIcc i (σ i)).symm k)) := by
    conv_lhs => rw [he]
  rw [hleft, hd]

/-- The complete permutation coefficient is the sum of its literal cost-exhausting
starts. There is at most one such start, but no start is discarded in the formula. -/
theorem hessenberg_permutation_coeff_deriv_interval_sum {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ) (hm : 0 < m)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      ∀ k, D (PowerSeries.coeff k (A i j)) = 0)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1)
    (hcost : (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m) :
    D (PowerSeries.coeff m (∏ k : Fin n, A k (σ k))) =
      ∑ i : Fin n, if (i : ℕ) ≤ (σ i : ℕ) ∧ (σ i : ℕ) - (i : ℕ) = m then
        a ^ m • ((∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i ∨ σ i < k),
          PowerSeries.constantCoeff (A k k)) • D (PowerSeries.constantCoeff (A i (σ i))))
      else 0 := by
  classical
  by_cases hex : ∃ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) ∧ (σ i : ℕ) - (i : ℕ) = m
  · obtain ⟨i, hi, hlong⟩ := hex
    rw [hessenberg_permutation_coeff_deriv_interval D A a ha hsub m hm hshort σ hσ
      hcost i hi hlong]
    symm
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left ⟨hi, hlong⟩]
    · intro k _ hki
      have hk := hessenberg_permutation_unique_forward σ hσ i hi
        (hlong.trans hcost.symm) k hki
      have hnot : ¬ ((k : ℕ) ≤ (σ k : ℕ) ∧ (σ k : ℕ) - (k : ℕ) = m) := by omega
      rw [ite_eq_right hnot]
    · simp
  · have hnone : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) →
        (σ i : ℕ) - (i : ℕ) ≠ m := by
      intro i hi he
      exact hex ⟨i, hi, he⟩
    rw [hessenberg_permutation_coeff_deriv_frontier D A a ha hsub m hshort σ hσ,
      ite_eq_left hcost]
    have hz := hessenberg_frontier_without_long_interval D
      (fun i j => PowerSeries.constantCoeff (A i j)) σ hσ m hcost
      (fun i j hij hlt => by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hshort i j hij hlt 0) hnone
    rw [hz, smul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hi => hex ⟨i, hi⟩)]

/-- The complete first-fresh determinant derivative is indexed by every literal interval
of the required length. Exterior diagonals and coincident response occurrences are retained. -/
theorem hessenberg_coeff_deriv_intervals {n : ℕ}
    (D : Derivation ℚ F M) (A : Matrix (Fin n) (Fin n) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F) (ha : D a = 0)
    (hsub : ∀ i j : Fin n, (i : ℕ) = (j : ℕ) + 1 →
      A i j = PowerSeries.X * PowerSeries.C a)
    (m : ℕ) (hm : 0 < m)
    (hshort : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      ∀ k, D (PowerSeries.coeff k (A i j)) = 0) :
    D (PowerSeries.coeff m A.det) =
      ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m then
          ((-1 : ℤ) ^ m) • (a ^ m •
            ((∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i ∨ j < k),
              PowerSeries.constantCoeff (A k k)) • D (PowerSeries.constantCoeff (A i j))))
        else 0 := by
  classical
  rw [← hessenberg_interval_frontier_sum]
  rw [← Matrix.det_transpose A, Matrix.det_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Units.smul_def, map_zsmul]
  by_cases hσ : ∀ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) + 1
  · by_cases hc : (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m
    · rw [hessenberg_permutation_coeff_deriv_interval_sum D A a ha hsub m hm hshort σ hσ hc,
        Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (i : ℕ) ≤ (σ i : ℕ) ∧ (σ i : ℕ) - (i : ℕ) = m
      · rw [ite_eq_left hi, ite_eq_left ⟨hσ, hc, hi⟩]
        have hs : (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ m := by
          rw [hessenberg_permutation_interval_sign σ hσ i hi.1 (hi.2.trans hc.symm), hi.2]
          simp
        rw [hs]
      · rw [ite_eq_right hi, smul_zero,
          ite_eq_right (fun h => hi h.2.2)]
    · rw [hessenberg_permutation_coeff_deriv_frontier D A a ha hsub m hshort σ hσ,
        ite_eq_right hc, smul_zero]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [ite_eq_right (fun h => hc h.2.1)]
  · have hz : (∏ i : Fin n, A i (σ i)) = 0 := by
      obtain ⟨i, hi⟩ := not_forall.mp hσ
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hA i (σ i) (by omega)
    rw [hz, map_zero, map_zero, smul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun h => hσ h.1)]

end SkewCornerDescent.Matrix
