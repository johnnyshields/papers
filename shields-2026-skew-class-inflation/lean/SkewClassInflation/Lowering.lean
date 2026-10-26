/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileInflation
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Lowering the full inflated determinant

Formalizes `eq:lowering-map` and `lem:inflation-lowering` in
`shields-2026-skew-class-inflation.tex`.  The map first takes the prescribed
ordinary homogeneous component, then lowers each positive generator index.
The determinant identity holds for every integer-indexed board, including
boards where inflation opens previously negative entries.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative
open scoped BigOperators

/-- The ordinary-degree-preserving filter followed by index lowering. -/
noncomputable def lowerSubstitution (t : ℕ) : CompleteRing →ₐ[ℚ] CompleteRing :=
  MvPolynomial.aeval fun k : ℕ+ => complete ((k : ℕ) - (t : ℤ))

/-- The linear lowering operation, on the actual rational complete-generator ring. -/
noncomputable def lowering (t n : ℕ) : CompleteRing →ₗ[ℚ] CompleteRing :=
  (lowerSubstitution t).toLinearMap.comp (MvPolynomial.homogeneousComponent n)

/-- Every complete generator has ordinary degree at most one, including units and zeros. -/
theorem complete_totalDegree_le_one (k : ℤ) : (complete k).totalDegree ≤ 1 := by
  rcases lt_trichotomy k 0 with h | rfl | h
  · simp [complete_of_neg h]
  · simp
  · let j : ℕ+ := ⟨k.toNat, by omega⟩
    have hc : complete k = MvPolynomial.X j := complete_of_pos h
    rw [hc, MvPolynomial.totalDegree_X]

/-- The top degree of a product with one slot per index retains precisely its positive slots. -/
theorem top_component_complete_prod {ι : Type*}
    (s : Finset ι) (k : ι → ℤ) :
    MvPolynomial.homogeneousComponent s.card (∏ i ∈ s, complete (k i)) =
      ∏ i ∈ s, if 0 < k i then complete (k i) else 0 := by
  classical
  by_cases hp : ∀ i ∈ s, 0 < k i
  · have hh : (∏ i ∈ s, complete (k i)).IsHomogeneous s.card := by
      have hh := MvPolynomial.IsHomogeneous.prod s (fun i => complete (k i))
        (fun _ => 1) (fun i hi => by
          rw [complete_of_pos (hp i hi)]
          exact MvPolynomial.isHomogeneous_X _ _)
      simpa using hh
    rw [MvPolynomial.homogeneousComponent_eq_self hh]
    exact Finset.prod_congr rfl fun i hi => by rw [ite_eq_left (hp i hi)]
  · push Not at hp
    obtain ⟨i, hi, hk⟩ := hp
    have hr : (∏ j ∈ s, if 0 < k j then complete (k j) else 0) = 0 :=
      Finset.prod_eq_zero hi (by rw [ite_eq_right (by omega)])
    rw [hr]
    rcases lt_or_eq_of_le hk with hk | hk
    · have hz : (∏ j ∈ s, complete (k j)) = 0 :=
        Finset.prod_eq_zero hi (complete_of_neg hk)
      rw [hz, map_zero]
    · have he : ∏ j ∈ s, complete (k j) = ∏ j ∈ s.erase i, complete (k j) := by
        rw [← Finset.mul_prod_erase s (fun j => complete (k j)) hi, hk, complete_zero,
          one_mul]
      rw [he]
      apply MvPolynomial.homogeneousComponent_eq_zero
      calc
        (∏ j ∈ s.erase i, complete (k j)).totalDegree ≤
            ∑ j ∈ s.erase i, (complete (k j)).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
        _ ≤ ∑ _j ∈ s.erase i, 1 :=
          Finset.sum_le_sum fun j _ => complete_totalDegree_le_one _
        _ < s.card := by
          simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
            Finset.card_erase_lt_of_mem hi

/-- After a positive shift, the filter and substitution recover each original determinant slot. -/
theorem lowerSubstitution_shifted_slot (t : ℕ) (ht : 0 < t) (k : ℤ) :
    lowerSubstitution t (if 0 < k + t then complete (k + t) else 0) = complete k := by
  by_cases h : 0 < k + t
  · let j : ℕ+ := ⟨(k + t).toNat, by omega⟩
    have hc : complete (k + t) = MvPolynomial.X j := complete_of_pos h
    rw [ite_eq_left h, hc]
    rw [lowerSubstitution, MvPolynomial.aeval_X]
    change complete (((k + t).toNat : ℤ) - t) = complete k
    congr 1
    omega
  · rw [ite_eq_right h, map_zero, complete_of_neg (by omega)]

/-- Lowering a full product works even when the shift introduced units or small positive labels. -/
theorem lowering_shifted_prod {ι : Type*}
    (s : Finset ι) (k : ι → ℤ) (t : ℕ) (ht : 0 < t) :
    lowering t s.card (∏ i ∈ s, complete (k i + t)) = ∏ i ∈ s, complete (k i) := by
  classical
  change lowerSubstitution t
    (MvPolynomial.homogeneousComponent s.card (∏ i ∈ s, complete (k i + t))) = _
  rw [top_component_complete_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => lowerSubstitution_shifted_slot t ht (k i)

/-- The lowering identity is a full-board determinant theorem, with no Hessenberg restriction. -/
theorem lowering_shifted_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (t : ℕ) (ht : 0 < t) :
    lowering t (Fintype.card ι) (Matrix.of fun i j => complete (A i j + t)).det =
      (Matrix.of fun i j => complete (A i j)).det := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  change lowerSubstitution t (MvPolynomial.homogeneousComponent (Fintype.card ι)
    ((σ.sign : CompleteRing) * ∏ i, complete (A (σ i) i + t))) = _
  have hs : (σ.sign : CompleteRing) = MvPolynomial.C (σ.sign : ℚ) := by simp
  rw [hs, MvPolynomial.homogeneousComponent_C_mul, map_mul]
  have hc : lowerSubstitution t (MvPolynomial.C (σ.sign : ℚ)) =
      MvPolynomial.C (σ.sign : ℚ) := by simp [lowerSubstitution]
  rw [hc]
  congr 1
  exact lowering_shifted_prod Finset.univ (fun i => A (σ i) i) t ht

/-- The determinant attached directly to the normalized full profile beta lists. -/
noncomputable def profileSchur {n : ℕ} (P : Profile n) : CompleteRing :=
  (Matrix.of fun i j => complete (P.xi i - P.zeta j)).det

/-- Inflation lowering on every connected profile in the manuscript's actual representation. -/
theorem lowering_inflated_profile {n : ℕ} (P : Profile n) (t : ℕ) (ht : 0 < t) :
    lowering t (n + 1) (profileSchur (Profile.inflate t P)) = profileSchur P := by
  simp only [profileSchur, Profile.index_inflate]
  simpa only [Fintype.card_fin, Matrix.of_apply] using
    lowering_shifted_det (Matrix.of fun i j => P.xi i - P.zeta j) t ht

/-- Equality after inflation implies equality before inflation, without a no-opening assumption. -/
theorem profileSchur_eq_of_inflate_eq {n : ℕ} (P Q : Profile n) (t : ℕ)
    (h : profileSchur (Profile.inflate t P) = profileSchur (Profile.inflate t Q)) :
    profileSchur P = profileSchur Q := by
  by_cases ht : 0 < t
  · have h' := congrArg (lowering t (n + 1)) h
    simpa only [lowering_inflated_profile P t ht, lowering_inflated_profile Q t ht] using h'
  · have ht : t = 0 := by omega
    simpa [ht] using h

end SkewClassInflation
