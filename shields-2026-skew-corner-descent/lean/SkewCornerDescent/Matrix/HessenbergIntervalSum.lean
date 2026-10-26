/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.HessenbergIntervalPermutation

/-!
# Exact reindexing of the permutation frontier by literal intervals

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The reindexing retains each original start and endpoint, including repeated response values.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The forward start of an inverse interval cycle lands at the literal right endpoint. -/
theorem inverse_interval_cycle_start {n : ℕ} (i j : Fin n) (hij : i ≤ j) :
    (Fin.cycleIcc i j).symm i = j := by
  apply Fin.ext
  simpa only [ite_true, eq_self] using inverse_interval_cycle_apply i j hij i

/-- Fixing the literal endpoints identifies exactly one permutation on the cost frontier. -/
theorem hessenberg_interval_frontier_iff {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j : Fin n) (hij : i ≤ j) (m : ℕ) (hlen : (j : ℕ) - (i : ℕ) = m) :
    ((∀ k : Fin n, (k : ℕ) ≤ (σ k : ℕ) + 1) ∧
      (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m ∧
      σ i = j) ↔ σ = (Fin.cycleIcc i j).symm := by
  classical
  constructor
  · rintro ⟨hσ, hcost, he⟩
    have hi : (i : ℕ) ≤ (σ i : ℕ) := by rw [he]; exact hij
    have hc : (σ i : ℕ) - (i : ℕ) =
        (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card := by
      rw [he, hlen, hcost]
    have h := hessenberg_permutation_eq_interval_cycle σ hσ i hi hc
    rwa [he] at h
  · intro he
    subst σ
    exact ⟨inverse_interval_cycle_hessenberg i j hij,
      (inverse_interval_cycle_cost i j hij).trans hlen,
      inverse_interval_cycle_start i j hij⟩

/-- Complete frontier reindexing is by positions, not distinct response values. The
finite sums retain every start even when two intervals have identical responses. -/
theorem hessenberg_interval_frontier_sum {n : ℕ} {G : Type*} [AddCommMonoid G]
    (m : ℕ) (f : Fin n → Fin n → G) :
    (∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
      if (∀ k : Fin n, (k : ℕ) ≤ (σ k : ℕ) + 1) ∧
          (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m ∧
          (i : ℕ) ≤ (σ i : ℕ) ∧ (σ i : ℕ) - (i : ℕ) = m then f i (σ i) else 0) =
      ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m then f i j else 0 := by
  classical
  have hexpand (σ : Equiv.Perm (Fin n)) (i : Fin n) :
      (if (∀ k : Fin n, (k : ℕ) ≤ (σ k : ℕ) + 1) ∧
          (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m ∧
          (i : ℕ) ≤ (σ i : ℕ) ∧ (σ i : ℕ) - (i : ℕ) = m then f i (σ i) else 0) =
      ∑ j : Fin n, if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m ∧
          (∀ k : Fin n, (k : ℕ) ≤ (σ k : ℕ) + 1) ∧
          (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m ∧
          σ i = j then f i j else 0 := by
    symm
    rw [Finset.sum_eq_single (σ i)]
    · congr 1
      apply propext
      tauto
    · intro j _ hne
      rw [ite_eq_right]
      intro h
      exact hne h.2.2.2.2.symm
    · simp
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hwin : (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m
  · rw [ite_eq_left hwin]
    have hiff := hessenberg_interval_frontier_iff (i := i) (j := j)
      (hij := hwin.1) (m := m) (hlen := hwin.2)
    have hterm (σ : Equiv.Perm (Fin n)) :
        (if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m ∧
            (∀ k : Fin n, (k : ℕ) ≤ (σ k : ℕ) + 1) ∧
            (Finset.univ.filter (fun k : Fin n => (σ k : ℕ) < (k : ℕ))).card = m ∧
            σ i = j then f i j else 0) =
          if σ = (Fin.cycleIcc i j).symm then f i j else 0 := by
      congr 1
      apply propext
      exact ⟨fun h => (hiff σ).mp h.2.2,
        fun h => ⟨hwin.1, hwin.2, (hiff σ).mpr h⟩⟩
    simp_rw [hterm]
    simp
  · rw [ite_eq_right hwin]
    apply Finset.sum_eq_zero
    intro σ _
    rw [ite_eq_right]
    intro h
    exact hwin ⟨h.1, h.2.1⟩

/-- Dividing by the complete nonzero diagonal product cancels exactly the exterior
positions. The remaining inverse window includes both endpoints and every repeated value. -/
theorem diagonal_product_inverse_interval {n : ℕ} {F : Type*} [Field F]
    (d : Fin n → F) (hd : ∀ k, d k ≠ 0) (i j : Fin n) :
    (∏ k : Fin n, d k)⁻¹ *
      (∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i ∨ j < k), d k) =
        ∏ k ∈ Finset.Icc i j, (d k)⁻¹ := by
  classical
  have hinside : Finset.univ.filter (fun k : Fin n => ¬ (k < i ∨ j < k)) =
      Finset.Icc i j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    omega
  have hp := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun k : Fin n => k < i ∨ j < k) d
  rw [hinside] at hp
  have hout : (∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i ∨ j < k), d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => hd k)
  rw [← hp, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hout, mul_one, Finset.prod_inv_distrib]

end SkewCornerDescent.Matrix
