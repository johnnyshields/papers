/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Directed ratio-cycle energy at the first surviving profile degree

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The product of actual directed ratios telescopes. Its first two nontrivial
jets give one half of the sum of squares, without reversed-edge symmetry or
an assumed logarithmic cancellation. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

private theorem near_one_mul_low {R : Type*} [CommRing R]
    (f g : PowerSeries R) (w k : ℕ) (hk : 0 < k) (hkw : k < w)
    (hf : ∀ i, 0 < i → i < w → PowerSeries.coeff i f = 0)
    (hg : ∀ i, 0 < i → i < w → PowerSeries.coeff i g = 0) :
    PowerSeries.coeff k (f * g) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have he := Finset.mem_antidiagonal.mp hij
  by_cases hi : i = 0
  · subst i
    simp only [zero_add] at he
    subst j
    rw [hg k hk hkw, mul_zero]
  · rw [hf i (Nat.pos_of_ne_zero hi) (by omega), zero_mul]

private theorem near_one_mul_first {R : Type*} [CommRing R]
    (f g : PowerSeries R) (w : ℕ) (hw : 0 < w)
    (hf0 : PowerSeries.constantCoeff f = 1) (hg0 : PowerSeries.constantCoeff g = 1)
    (hf : ∀ i, 0 < i → i < w → PowerSeries.coeff i f = 0) :
    PowerSeries.coeff w (f * g) = PowerSeries.coeff w f + PowerSeries.coeff w g := by
  classical
  rw [PowerSeries.coeff_mul]
  let S : Finset (ℕ × ℕ) := {(0,w),(w,0)}
  have hs : S ⊆ Finset.antidiagonal w := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_antidiagonal, zero_add, add_zero]
  rw [← Finset.sum_subset hs]
  · simp only [S, Finset.sum_insert, Finset.mem_singleton, Prod.mk.injEq,
      show ¬ (0 = w ∧ w = 0) by omega, not_false_eq_true, Finset.sum_singleton,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, hg0, one_mul, mul_one]
    ring
  · rintro ⟨i,j⟩ hij hnot
    have he := Finset.mem_antidiagonal.mp hij
    have hn : ¬ ((i = 0 ∧ j = w) ∨ (i = w ∧ j = 0)) := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] using hnot
    rw [hf i (by omega) (by omega), zero_mul]

private theorem near_one_mul_second {R : Type*} [CommRing R]
    (f g : PowerSeries R) (w : ℕ) (hw : 0 < w)
    (hf0 : PowerSeries.constantCoeff f = 1) (hg0 : PowerSeries.constantCoeff g = 1)
    (hf : ∀ i, 0 < i → i < w → PowerSeries.coeff i f = 0)
    (hg : ∀ i, 0 < i → i < w → PowerSeries.coeff i g = 0) :
    PowerSeries.coeff (2*w) (f*g) = PowerSeries.coeff (2*w) f +
      PowerSeries.coeff (2*w) g + PowerSeries.coeff w f * PowerSeries.coeff w g := by
  classical
  rw [PowerSeries.coeff_mul]
  let S : Finset (ℕ × ℕ) := {(0,2*w),(w,w),(2*w,0)}
  have hs : S ⊆ Finset.antidiagonal (2*w) := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> apply Finset.mem_antidiagonal.mpr <;> omega
  rw [← Finset.sum_subset hs]
  · simp only [S, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, show ¬ (0 = w ∧ 2*w = w) by omega,
      show ¬ (0 = 2*w ∧ 2*w = 0) by omega,
      show ¬ (w = 2*w ∧ w = 0) by omega, or_self, not_false_eq_true,
      Finset.sum_singleton, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hf0, hg0, one_mul, mul_one]
    ring
  · rintro ⟨i,j⟩ hij hnot
    have he := Finset.mem_antidiagonal.mp hij
    have hn : ¬ ((i = 0 ∧ j = 2*w) ∨ (i = w ∧ j = w) ∨ (i = 2*w ∧ j = 0)) := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] using hnot
    by_cases hi : i < w
    · rw [hf i (by omega) hi, zero_mul]
    · rw [hg j (by omega) (by omega), mul_zero]

/-- The complete finite product retains its exact first jet and all second
cross terms. No disjoint-product or independence premise is supplied. -/
theorem near_one_prod_jets {R ι : Type*} [CommRing R]
    (s : Finset ι) (f : ι → PowerSeries R) (w : ℕ) (hw : 0 < w)
    (hf0 : ∀ i ∈ s, PowerSeries.constantCoeff (f i) = 1)
    (hf : ∀ i ∈ s, ∀ k, 0 < k → k < w → PowerSeries.coeff k (f i) = 0) :
    (∀ k, 0 < k → k < w → PowerSeries.coeff k (∏ i ∈ s, f i) = 0) ∧
      PowerSeries.coeff w (∏ i ∈ s, f i) = ∑ i ∈ s, PowerSeries.coeff w (f i) ∧
      2 * PowerSeries.coeff (2*w) (∏ i ∈ s, f i) =
        2 * (∑ i ∈ s, PowerSeries.coeff (2*w) (f i)) +
          (∑ i ∈ s, PowerSeries.coeff w (f i)) ^ 2 -
          ∑ i ∈ s, PowerSeries.coeff w (f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, PowerSeries.coeff_one,
      show w ≠ 0 by omega, show 2*w ≠ 0 by omega, ↓reduceIte, mul_zero,
      zero_pow (show (2 : ℕ) ≠ 0 by decide), add_zero, sub_zero]
    refine ⟨?_, trivial, trivial⟩
    intro k hk _
    simp only [hk.ne', ↓reduceIte]
  | @insert i s hi ih =>
    have hs0 : ∀ j ∈ s, PowerSeries.constantCoeff (f j) = 1 :=
      fun j hj => hf0 j (Finset.mem_insert_of_mem hj)
    have hs : ∀ j ∈ s, ∀ k, 0 < k → k < w → PowerSeries.coeff k (f j) = 0 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hih := ih hs0 hs
    have hprod0 : PowerSeries.constantCoeff (∏ j ∈ s, f j) = 1 := by
      rw [map_prod]
      exact Finset.prod_eq_one hs0
    have hi0 := hf0 i (Finset.mem_insert_self _ _)
    have hilow := hf i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi]
    refine ⟨fun k hk hkw => near_one_mul_low _ _ w k hk hkw hilow hih.1, ?_, ?_⟩
    · rw [near_one_mul_first _ _ w hw hi0 hprod0 hilow, hih.2.1,
        Finset.sum_insert hi]
    · rw [near_one_mul_second _ _ w hw hi0 hprod0 hilow hih.1,
        Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, hih.2.1]
      linear_combination hih.2.2

/-- A telescoping directed ratio product has first surviving sum equal to
one half of the squared first differences. No reversed-edge symmetry is used. -/
theorem directed_ratio_product_energy {F ι : Type*} [Field F] [CharZero F]
    (s : Finset ι) (ratio : ι → PowerSeries F) (w : ℕ) (hw : 0 < w)
    (h0 : ∀ i ∈ s, PowerSeries.constantCoeff (ratio i) = 1)
    (hlow : ∀ i ∈ s, ∀ k, 0 < k → k < w → PowerSeries.coeff k (ratio i) = 0)
    (hprod : ∏ i ∈ s, ratio i = 1) :
    ∑ i ∈ s, PowerSeries.coeff (2*w) (ratio i) =
      (1/2 : F) * ∑ i ∈ s, PowerSeries.coeff w (ratio i) ^ 2 := by
  have h := near_one_prod_jets s ratio w hw h0 hlow
  rw [hprod] at h
  simp only [PowerSeries.coeff_one, show w ≠ 0 by omega,
    show 2*w ≠ 0 by omega, ↓reduceIte] at h
  have he : 2 * (∑ i ∈ s, PowerSeries.coeff (2*w) (ratio i)) =
      ∑ i ∈ s, PowerSeries.coeff w (ratio i) ^ 2 := by
    rw [← h.2.1] at h
    linear_combination -h.2.2
  linear_combination (1/2 : F) * he

/-- The complete product of actual directed profile ratios telescopes
under any finite permutation. Normalized profile constants produce all units. -/
theorem directed_profile_ratio_product {F ι : Type*} [Field F] [Fintype ι]
    (f : ι → PowerSeries F) (σ : Equiv.Perm ι)
    (h0 : ∀ i, PowerSeries.constantCoeff (f i) = 1) :
    ∏ i, f i * (f (σ i))⁻¹ = 1 := by
  classical
  have hshift : (∏ i, f (σ i)) = ∏ i, f i := by
    exact Equiv.prod_comp σ f
  have he : (∏ i, f i * (f (σ i))⁻¹) * (∏ i, f (σ i)) = ∏ i, f i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_assoc, PowerSeries.inv_mul_cancel (f (σ i)) (by rw [h0]; exact one_ne_zero),
      mul_one]
  rw [hshift] at he
  have hc : PowerSeries.constantCoeff (∏ i, f i) ≠ 0 := by
    rw [map_prod]
    simpa only [h0, Finset.prod_const_one] using (one_ne_zero : (1 : F) ≠ 0)
  have hinv := PowerSeries.mul_inv_cancel (∏ i, f i) hc
  have h := congrArg (fun x : PowerSeries F => x * (∏ i, f i)⁻¹) he
  simpa only [mul_assoc, hinv, mul_one] using h

/-- Low matching of the actual profiles produces the corresponding vanishing
ratio jets and identifies their first difference, with no frozen denominators. -/
theorem directed_profile_ratio_first {F ι : Type*} [Field F]
    (f : ι → PowerSeries F) (σ : Equiv.Perm ι) (w : ℕ) (hw : 0 < w)
    (h0 : ∀ i, PowerSeries.constantCoeff (f i) = 1)
    (hmatch : ∀ i k, k < w → PowerSeries.coeff k (f i) = PowerSeries.coeff k (f (σ i))) :
    ∀ i,
      (∀ k, 0 < k → k < w →
        PowerSeries.coeff k (f i * (f (σ i))⁻¹) = 0) ∧
      PowerSeries.coeff w (f i * (f (σ i))⁻¹) =
        PowerSeries.coeff w (f i) - PowerSeries.coeff w (f (σ i)) := by
  intro i
  let R := f i * (f (σ i))⁻¹
  have hr0 : PowerSeries.constantCoeff R = 1 := by
    simp only [R, map_mul, PowerSeries.constantCoeff_inv, h0, inv_one, mul_one]
  have he : R * f (σ i) = f i := by
    dsimp only [R]
    rw [mul_assoc, PowerSeries.inv_mul_cancel (f (σ i)) (by rw [h0]; exact one_ne_zero),
      mul_one]
  have hlow : ∀ k, 0 < k → k < w → PowerSeries.coeff k R = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk hkw
      have hj := near_one_mul_first R (f (σ i)) k hk hr0 (h0 _)
        (fun l hl hlk => ih l hlk hl (hlk.trans hkw))
      rw [he, hmatch i k hkw] at hj
      linear_combination -hj
  refine ⟨hlow, ?_⟩
  have hj := near_one_mul_first R (f (σ i)) w hw hr0 (h0 _) hlow
  rw [he] at hj
  linear_combination -hj

/-- The actual directed ratio cycle has one half of the sum of squared
first profile differences as its complete first surviving sum. The product,
units, and ratio low jets are all constructed from the profiles themselves. -/
theorem directed_profile_ratio_energy {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
    (f : ι → PowerSeries F) (σ : Equiv.Perm ι) (w : ℕ) (hw : 0 < w)
    (h0 : ∀ i, PowerSeries.constantCoeff (f i) = 1)
    (hmatch : ∀ i k, k < w → PowerSeries.coeff k (f i) = PowerSeries.coeff k (f (σ i))) :
    ∑ i, PowerSeries.coeff (2*w) (f i * (f (σ i))⁻¹) =
      (1/2 : F) * ∑ i, (PowerSeries.coeff w (f i) - PowerSeries.coeff w (f (σ i))) ^ 2 := by
  classical
  have hfirst := directed_profile_ratio_first f σ w hw h0 hmatch
  have h := directed_ratio_product_energy Finset.univ (fun i => f i * (f (σ i))⁻¹) w hw
    (fun i _ => by
      simp only [map_mul, PowerSeries.constantCoeff_inv, h0, inv_one, mul_one])
    (fun i _ => (hfirst i).1) (directed_profile_ratio_product f σ h0)
  simp_rw [(hfirst _).2] at h
  exact h

/-- A genuine first profile disagreement makes the complete directed energy
positive on an ordered field, including cycles without reversed-edge symmetry. -/
theorem directed_profile_ratio_energy_pos {F ι : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [Fintype ι]
    (f : ι → PowerSeries F) (σ : Equiv.Perm ι) (w : ℕ) (hw : 0 < w)
    (h0 : ∀ i, PowerSeries.constantCoeff (f i) = 1)
    (hmatch : ∀ i k, k < w → PowerSeries.coeff k (f i) = PowerSeries.coeff k (f (σ i)))
    (hne : ∃ i, PowerSeries.coeff w (f i) ≠ PowerSeries.coeff w (f (σ i))) :
    0 < ∑ i, PowerSeries.coeff (2*w) (f i * (f (σ i))⁻¹) := by
  classical
  obtain ⟨i, hi⟩ := hne
  have hsum : 0 < ∑ j, (PowerSeries.coeff w (f j) -
      PowerSeries.coeff w (f (σ j))) ^ 2 := by
    apply Finset.sum_pos' (fun j _ => sq_nonneg _)
    exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
  rw [directed_profile_ratio_energy f σ w hw h0 hmatch]
  exact mul_pos (by norm_num) hsum

end SkewCornerDescent
