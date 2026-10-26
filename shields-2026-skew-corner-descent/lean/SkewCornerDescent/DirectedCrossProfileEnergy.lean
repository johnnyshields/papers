/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.DirectedRatioEnergy

/-!
# Complete directed cross-profile energy

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Sparse ratio products cancel every earlier coefficient. Complete varying
self-products need only agree through the first profile discrepancy; no
normal inverse or higher endpoint coefficient is frozen. Sorry-free.
-/

namespace SkewCornerDescent
open scoped BigOperators

private theorem sparse_mul_coeff {R : Type*} [CommRing R]
    (f g : PowerSeries R) (w k : ℕ) (hk : 0 < k) (hkw : k < 2 * w)
    (hf0 : PowerSeries.constantCoeff f = 1) (hg0 : PowerSeries.constantCoeff g = 1)
    (hf : ∀ i, 0 < i → i < w → PowerSeries.coeff i f = 0)
    (hg : ∀ i, 0 < i → i < w → PowerSeries.coeff i g = 0) :
    PowerSeries.coeff k (f*g) = PowerSeries.coeff k f + PowerSeries.coeff k g := by
  classical
  rw [PowerSeries.coeff_mul]
  let S : Finset (ℕ × ℕ) := {(0,k),(k,0)}
  have hs : S ⊆ Finset.antidiagonal k := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  rw [← Finset.sum_subset hs]
  · simp only [S, Finset.sum_insert, Finset.mem_singleton, Prod.mk.injEq,
      show ¬ (0 = k ∧ k = 0) by omega, not_false_eq_true, Finset.sum_singleton,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, hg0, one_mul, mul_one]
    ring
  · rintro ⟨i,j⟩ hij hnot
    have he := Finset.mem_antidiagonal.mp hij
    have hn : ¬ ((i = 0 ∧ j = k) ∨ (i = k ∧ j = 0)) := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] using hnot
    by_cases hi : i < w
    · rw [hf i (by omega) hi, zero_mul]
    · rw [hg j (by omega) (by omega), mul_zero]

/-- Before two positive sparse jets can interact, the coefficient of a finite
product is the sum of its individual coefficients. -/
theorem near_one_prod_coeff_before_twice {R ι : Type*} [CommRing R]
    (s : Finset ι) (f : ι → PowerSeries R) (w k : ℕ) (hk : 0 < k) (hkw : k < 2 * w)
    (hf0 : ∀ i ∈ s, PowerSeries.constantCoeff (f i) = 1)
    (hf : ∀ i ∈ s, ∀ j, 0 < j → j < w → PowerSeries.coeff j (f i) = 0) :
    PowerSeries.coeff k (∏ i ∈ s, f i) = ∑ i ∈ s, PowerSeries.coeff k (f i) := by
  classical
  have hw : 0 < w := by omega
  induction s using Finset.induction_on with
  | empty => simp [hk.ne']
  | @insert i s hi ih =>
    have hs0 : ∀ j ∈ s, PowerSeries.constantCoeff (f j) = 1 :=
      fun j hj => hf0 j (Finset.mem_insert_of_mem hj)
    have hs : ∀ j ∈ s, ∀ l, 0 < l → l < w → PowerSeries.coeff l (f j) = 0 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hp0 : PowerSeries.constantCoeff (∏ j ∈ s, f j) = 1 := by
      rw [map_prod]
      exact Finset.prod_eq_one hs0
    rw [Finset.prod_insert hi, sparse_mul_coeff _ _ w k hk hkw
      (hf0 i (Finset.mem_insert_self _ _)) hp0
      (hf i (Finset.mem_insert_self _ _)) (near_one_prod_jets s f w hw hs0 hs).1,
      ih hs0 hs, Finset.sum_insert hi]

/-- The complete sum of directed profile ratios has no positive coefficient
below twice the first profile discrepancy. -/
theorem directed_profile_ratio_sum_low {F ι : Type*} [Field F] [Fintype ι]
    (f : ι → PowerSeries F) (σ : Equiv.Perm ι) (w : ℕ) (hw : 0 < w)
    (h0 : ∀ i, PowerSeries.constantCoeff (f i) = 1)
    (hmatch : ∀ i k, k < w → PowerSeries.coeff k (f i) = PowerSeries.coeff k (f (σ i)))
    (k : ℕ) (hk : 0 < k) (hkw : k < 2 * w) :
    ∑ i, PowerSeries.coeff k (f i * (f (σ i))⁻¹) = 0 := by
  classical
  have hfirst := directed_profile_ratio_first f σ w hw h0 hmatch
  have h := near_one_prod_coeff_before_twice Finset.univ
    (fun i => f i * (f (σ i))⁻¹) w k hk hkw
    (fun i _ => by simp [h0]) (fun i _ => (hfirst i).1)
  rw [directed_profile_ratio_product f σ h0] at h
  simpa only [PowerSeries.coeff_one, hk.ne', ↓reduceIte] using h.symm

private theorem sparse_weight_coeff {R : Type*} [CommRing R]
    (r G H : PowerSeries R) (w k : ℕ) (hk : k ≤ 2 * w)
    (hr : ∀ k, k < w → PowerSeries.coeff k r = 0)
    (hGH : ∀ k, k ≤ w → PowerSeries.coeff k G = PowerSeries.coeff k H) :
    PowerSeries.coeff k (r * G) = PowerSeries.coeff k (r * H) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  have he := Finset.mem_antidiagonal.mp hij
  by_cases hi : i < w
  · rw [hr i hi, zero_mul, zero_mul]
  · rw [hGH j (by omega)]

/-- Complete cross-minus-self profile products retain the directed energy when
their self-product jets agree through the first discrepancy degree. -/
theorem directed_cross_profile_energy {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
    (f g : ι → PowerSeries F) (σ : Equiv.Perm ι) (w : ℕ) (hw : 0 < w)
    (G : PowerSeries F) (hG0 : PowerSeries.constantCoeff G = 1)
    (hf0 : ∀ i, PowerSeries.constantCoeff (f i) = 1)
    (hmatch : ∀ i k, k < w → PowerSeries.coeff k (f i) = PowerSeries.coeff k (f (σ i)))
    (hself : ∀ i k, k ≤ w → PowerSeries.coeff k (f i * g i) = PowerSeries.coeff k G) :
    ∑ i, PowerSeries.coeff (2 * w) (f i * g (σ i) - f i * g i) =
      (1/2 : F) * ∑ i, (PowerSeries.coeff w (f i) -
        PowerSeries.coeff w (f (σ i))) ^ 2 := by
  classical
  let r := fun i => f i * (f (σ i))⁻¹ - 1
  have hfirst := directed_profile_ratio_first f σ w hw hf0 hmatch
  have hr : ∀ i k, k < w → PowerSeries.coeff k (r i) = 0 := by
    intro i k hk
    by_cases hk0 : k = 0
    · subst k
      simp [r, hf0]
    · simpa only [r, map_sub, PowerSeries.coeff_one, hk0, ↓reduceIte, sub_zero]
        using (hfirst i).1 k (Nat.pos_of_ne_zero hk0) hk
  have he : ∀ i, r i * (f (σ i) * g (σ i)) =
      f i * g (σ i) - f (σ i) * g (σ i) := by
    intro i
    dsimp only [r]
    rw [sub_mul, one_mul, ← mul_assoc, mul_assoc (f i),
      PowerSeries.inv_mul_cancel (f (σ i)) (by rw [hf0]; exact one_ne_zero), mul_one]
  have hsum : (∑ i, (f i * g (σ i) - f i * g i)) =
      ∑ i, r i * (f (σ i) * g (σ i)) := by
    simp_rw [he, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp σ (fun i => f i * g i)]
  have hcoeff : (∑ i, PowerSeries.coeff (2 * w)
      (f i * g (σ i) - f i * g i)) =
      PowerSeries.coeff (2 * w) ((∑ i, r i) * G) := by
    rw [← map_sum, hsum, map_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact sparse_weight_coeff (r i) _ G w (2 * w) le_rfl (hr i) (hself (σ i))
  have hlow : ∀ k, k < 2 * w → PowerSeries.coeff k (∑ i, r i) = 0 := by
    intro k hk
    rw [map_sum]
    by_cases hk0 : k = 0
    · exact Finset.sum_eq_zero (fun i _ => hr i k (by omega))
    · simp only [r, map_sub, PowerSeries.coeff_one, hk0, ↓reduceIte, sub_zero]
      exact directed_profile_ratio_sum_low f σ w hw hf0 hmatch k
        (Nat.pos_of_ne_zero hk0) hk
  rw [hcoeff, PowerSeries.coeff_mul]
  have hsingle : ∀ x ∈ Finset.antidiagonal (2 * w), x ≠ (2 * w,0) →
      PowerSeries.coeff x.1 (∑ i, r i) * PowerSeries.coeff x.2 G = 0 := by
    rintro ⟨i,j⟩ hij hne
    have heq := Finset.mem_antidiagonal.mp hij
    have hi : i ≠ 2 * w := by
      intro hi
      have hj : j = 0 := by omega
      exact hne (by simp [hi, hj])
    rw [hlow i (by omega), zero_mul]
  rw [Finset.sum_eq_single (2 * w,0) (fun x hx hne => hsingle x hx hne)
    (by simp), PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0, mul_one, map_sum]
  simp only [r, map_sub, PowerSeries.coeff_one, show 2 * w ≠ 0 by omega,
    ↓reduceIte, sub_zero]
  exact directed_profile_ratio_energy f σ w hw hf0 hmatch

/-- Below twice the first discrepancy, complete directed cross-minus-self
products cancel even when their higher self-product jets vary. -/
theorem directed_cross_profile_sum_low {F ι : Type*} [Field F] [Fintype ι]
    (f g : ι → PowerSeries F) (σ : Equiv.Perm ι) (w : ℕ) (hw : 0 < w)
    (G : PowerSeries F) (hf0 : ∀ i, PowerSeries.constantCoeff (f i) = 1)
    (hmatch : ∀ i k, k < w → PowerSeries.coeff k (f i) = PowerSeries.coeff k (f (σ i)))
    (hself : ∀ i k, k ≤ w → PowerSeries.coeff k (f i * g i) = PowerSeries.coeff k G)
    (k : ℕ) (hk : k < 2 * w) :
    ∑ i, PowerSeries.coeff k (f i * g (σ i) - f i * g i) = 0 := by
  classical
  let r := fun i => f i * (f (σ i))⁻¹ - 1
  have hfirst := directed_profile_ratio_first f σ w hw hf0 hmatch
  have hr : ∀ i l, l < w → PowerSeries.coeff l (r i) = 0 := by
    intro i l hl
    by_cases hl0 : l = 0
    · subst l
      simp [r, hf0]
    · simpa only [r, map_sub, PowerSeries.coeff_one, hl0, ↓reduceIte, sub_zero]
        using (hfirst i).1 l (Nat.pos_of_ne_zero hl0) hl
  have he : ∀ i, r i * (f (σ i) * g (σ i)) =
      f i * g (σ i) - f (σ i) * g (σ i) := by
    intro i
    dsimp only [r]
    rw [sub_mul, one_mul, ← mul_assoc, mul_assoc (f i),
      PowerSeries.inv_mul_cancel (f (σ i)) (by rw [hf0]; exact one_ne_zero), mul_one]
  have hsum : (∑ i, (f i * g (σ i) - f i * g i)) =
      ∑ i, r i * (f (σ i) * g (σ i)) := by
    simp_rw [he, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp σ (fun i => f i * g i)]
  have hcoeff : (∑ i, PowerSeries.coeff k (f i * g (σ i) - f i * g i)) =
      PowerSeries.coeff k ((∑ i, r i) * G) := by
    rw [← map_sum, hsum, map_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact sparse_weight_coeff (r i) _ G w k hk.le (hr i) (hself (σ i))
  have hlow : ∀ l, l < 2 * w → PowerSeries.coeff l (∑ i, r i) = 0 := by
    intro l hl
    rw [map_sum]
    by_cases hl0 : l = 0
    · exact Finset.sum_eq_zero (fun i _ => hr i l (by omega))
    · simp only [r, map_sub, PowerSeries.coeff_one, hl0, ↓reduceIte, sub_zero]
      exact directed_profile_ratio_sum_low f σ w hw hf0 hmatch l
        (Nat.pos_of_ne_zero hl0) hl
  rw [hcoeff, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have heq := Finset.mem_antidiagonal.mp hij
  rw [hlow i (by omega), zero_mul]

/-- A phase with exactly invariant incoming profiles has zero complete
cross-minus-self sum, without any assumption on its outgoing profiles. -/
theorem directed_cross_profile_invariant_sum {R ι : Type*} [CommRing R] [Fintype ι]
    (f g : ι → R) (σ : Equiv.Perm ι) (hf : ∀ i, f i = f (σ i)) :
    ∑ i, (f i * g (σ i) - f i * g i) = 0 := by
  classical
  rw [Finset.sum_sub_distrib]
  have he : (∑ i, f i * g (σ i)) = ∑ i, f (σ i) * g (σ i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hf i]
  rw [he, Equiv.sum_comp σ (fun i => f i * g i), sub_self]

end SkewCornerDescent
