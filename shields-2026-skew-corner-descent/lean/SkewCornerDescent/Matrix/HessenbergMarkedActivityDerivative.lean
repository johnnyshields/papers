/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergIntervalProducts
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Full original activity differentiation retains each marked upper occurrence

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact signed interval factorization and Leibniz rule differentiate every
original upper activity separately. Normal-dependent inverse weights remain in
all products; only their genuine chosen-generator independence is used.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- The entire normalized signed permutation derivative is a sum over its
marked original upper occurrences, including both marks on a cost-two pair product. -/
theorem hessenberg_marked_activity_derivative {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : @Derivation ℚ R R _ _ _ _ _ (inferInstance : Algebra ℚ R).toModule)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) R) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ j : Fin N, j.val ≤ (σ j).val + 1) (t : R)
    (hsub : ∀ i j : Fin N, i.val = j.val + 1 → A i j = t)
    (ht : D t = 0) (w : Fin N → R) (hw : ∀ j, D (w j) = 0) :
    let upper := Finset.univ.filter (fun j : Fin N => j.val ≤ (σ j).val)
    let cost := (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card
    let activity := fun j : Fin N => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
    D ((Equiv.Perm.sign σ : ℤ) • (∏ j, A j (σ j)) * (∏ j, w j)) =
      (-1 : R) ^ cost * t ^ cost *
        ∑ i ∈ upper, (D (A i (σ i)) * ∏ l ∈ Finset.Icc i (σ i), w l) *
          ∏ j ∈ upper.erase i, activity j := by
  classical
  have product_rule (s : Finset (Fin N)) (f : Fin N → R) :
      D (∏ i ∈ s, f i) = ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih,
        Finset.sum_insert hi, Finset.erase_insert hi]
      have hs : (∑ j ∈ s, D (f j) * ∏ k ∈ (insert i s).erase j, f k) =
          f i * ∑ j ∈ s, D (f j) * ∏ k ∈ s.erase j, f k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := fun he => hi (he.symm ▸ hj)
        rw [Finset.erase_insert_of_ne hij, Finset.prod_insert (by
          intro hm
          exact hi (Finset.mem_of_mem_erase hm))]
        ring
      rw [hs]
      ring
  let upper := Finset.univ.filter (fun j : Fin N => j.val ≤ (σ j).val)
  let cost := (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card
  let activity := fun j : Fin N => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
  have hweights (s : Finset (Fin N)) : D (∏ j ∈ s, w j) = 0 := by
    rw [product_rule]
    simp only [hw, zero_mul, Finset.sum_const_zero]
  have hactivity (i : Fin N) : D (activity i) =
      D (A i (σ i)) * ∏ j ∈ Finset.Icc i (σ i), w j := by
    rw [Derivation.leibniz, hweights, smul_zero, zero_add, smul_eq_mul, mul_comm]
  have hneg : D (-1 : R) = 0 := by rw [map_neg, D.map_one_eq_zero, neg_zero]
  have hsign : D ((-1 : R) ^ cost) = 0 := by
    rw [Derivation.leibniz_pow, hneg, smul_zero, nsmul_zero]
  have htpow : D (t ^ cost) = 0 := by
    rw [Derivation.leibniz_pow, ht, smul_zero, nsmul_zero]
  have hpref : D ((-1 : R) ^ cost * t ^ cost) = 0 := by
    rw [Derivation.leibniz, hsign, htpow, smul_zero, smul_zero, add_zero]
  rw [hessenberg_signed_weighted_product A σ hσ t hsub w]
  change D ((-1 : R) ^ cost * t ^ cost * ∏ j ∈ upper, activity j) = _
  rw [Derivation.leibniz, hpref, smul_zero, add_zero, smul_eq_mul, product_rule]
  apply congrArg (fun x : R => (-1 : R) ^ cost * t ^ cost * x)
  apply Finset.sum_congr rfl
  intro i _
  rw [hactivity]

/-- The complete actual determinant differentiates into every marked admissible
upper occurrence. Nonadmissible permutations vanish by original matrix support,
not by a restriction of the determinant expansion. -/
theorem hessenberg_det_marked_activity_derivative
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : @Derivation ℚ R R _ _ _ _ _ (inferInstance : Algebra ℚ R).toModule)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) R) (hA : IsUpperHessenberg A) (t : R)
    (hsub : ∀ i j : Fin N, i.val = j.val + 1 → A i j = t)
    (ht : D t = 0) (w : Fin N → R) (hw : ∀ j, D (w j) = 0) :
    D (A.det * ∏ j, w j) =
      ∑ σ : Equiv.Perm (Fin N),
        if (∀ j : Fin N, j.val ≤ (σ j).val + 1) then
          let upper := Finset.univ.filter (fun j : Fin N => j.val ≤ (σ j).val)
          let cost := (Finset.univ.filter (fun j : Fin N => (σ j).val < j.val)).card
          let activity := fun j : Fin N => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
          (-1 : R) ^ cost * t ^ cost *
            ∑ i ∈ upper, (D (A i (σ i)) * ∏ l ∈ Finset.Icc i (σ i), w l) *
              ∏ j ∈ upper.erase i, activity j
        else 0 := by
  classical
  rw [← Matrix.det_transpose A, Matrix.det_apply, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply]
  by_cases hσ : ∀ j : Fin N, j.val ≤ (σ j).val + 1
  · rw [ite_eq_left hσ]
    exact hessenberg_marked_activity_derivative D A σ hσ t hsub ht w hw
  · rw [ite_eq_right hσ]
    obtain ⟨i, hi⟩ := not_forall.mp hσ
    have hz : (∏ j, A j (σ j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hA i (σ i) (by omega))
    rw [hz, smul_zero, zero_mul, map_zero]

/-- The complete signed selected-cost prefactor shifts the normal coefficient
without replacing any factor of the activity by a residue. -/
theorem normal_cost_prefactor_coeff {F : Type*} [CommRing F]
    (a : F) (p : PowerSeries F) (c m : ℕ) :
    PowerSeries.coeff m ((-1 : PowerSeries F) ^ c *
      (PowerSeries.X * PowerSeries.C a) ^ c * p) =
      if c ≤ m then (-1 : F) ^ c * a ^ c * PowerSeries.coeff (m - c) p else 0 := by
  have hs : (-1 : PowerSeries F) ^ c = PowerSeries.C ((-1 : F) ^ c) := by
    rw [map_pow, map_neg, map_one]
  have hp : (PowerSeries.X * PowerSeries.C a) ^ c =
      (PowerSeries.X : PowerSeries F) ^ c * PowerSeries.C (a ^ c) := by
    rw [mul_pow, map_pow]
  have he : PowerSeries.C ((-1 : F) ^ c) *
      (PowerSeries.X ^ c * PowerSeries.C (a ^ c)) * p =
      PowerSeries.X ^ c * (PowerSeries.C ((-1 : F) ^ c * a ^ c) * p) := by
    rw [map_mul]
    ring
  rw [hs, hp, he, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [PowerSeries.coeff_C_mul]
  · rfl

end SkewCornerDescent.Matrix
