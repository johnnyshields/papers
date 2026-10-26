/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergSingleMarkedIndexing
import SkewCornerDescent.Matrix.HessenbergOneShyIndexing

/-!
# Complete marked frontier reduction to intervals and disjoint pairs

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact selected cost excludes every shorter marked entry. Both permitted
lengths retain their full activities, including both marks when the cost is two.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- At the lower cost frontier, excluding shorter marked entries leaves exactly
one cost-exhausting interval. Every diagonal inverse weight is retained. -/
theorem hessenberg_marked_one_length_sum {N m : ℕ}
    {R : Type*} [CommRing R] (A G : Matrix (Fin N) (Fin N) R)
    (w : Fin N → R) (hw : ∀ j, A j j * w j = 1)
    (hshort : ∀ i j : Fin N, i.val ≤ j.val → j.val - i.val < m → G i j = 0) :
    (∑ σ : Equiv.Perm (Fin N),
      if (∀ j, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ (σ i).val),
          (G i (σ i) * ∏ k ∈ Finset.Icc i (σ i), w k) *
            ∏ j ∈ (Finset.univ.filter (fun j => j.val ≤ (σ j).val)).erase i,
              A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k
      else 0) =
    ∑ i : Fin N, ∑ j : Fin N,
      if i.val ≤ j.val ∧ j.val - i.val = m then
        G i j * ∏ k ∈ Finset.Icc i j, w k else 0 := by
  classical
  rw [← hessenberg_single_marked_activity_sum A G w hw m]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : (∀ j, j.val ≤ (σ j).val + 1) ∧
      (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m
  · simp only [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hm : (σ i).val - i.val = m
    · rw [ite_eq_left hm]
    · rw [ite_eq_right hm]
      have hiup := (Finset.mem_filter.mp hi).2
      have hb := hessenberg_permutation_interval_cost σ h.1 i hiup
      rw [h.2] at hb
      have hz := hshort i (σ i) hiup (by omega)
      rw [hz, zero_mul, zero_mul]
  · simp only [ite_eq_right h]

/-- All marked activities at cost `m`, with shorter marks excluded, are exactly
one full interval or one long interval paired with a genuine disjoint pair. -/
theorem hessenberg_marked_two_length_sum {N m : ℕ} (hm : 2 ≤ m)
    {R : Type*} [CommRing R] (A G : Matrix (Fin N) (Fin N) R)
    (w : Fin N → R) (hw : ∀ j, A j j * w j = 1)
    (hshort : ∀ i j : Fin N, i.val ≤ j.val → j.val - i.val + 1 < m → G i j = 0) :
    (∑ σ : Equiv.Perm (Fin N),
      if (∀ j, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ (σ i).val),
          (G i (σ i) * ∏ k ∈ Finset.Icc i (σ i), w k) *
            ∏ j ∈ (Finset.univ.filter (fun j => j.val ≤ (σ j).val)).erase i,
              A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k
      else 0) =
    (∑ i : Fin N, ∑ j : Fin N,
      if i.val ≤ j.val ∧ j.val - i.val = m then
        G i j * ∏ k ∈ Finset.Icc i j, w k else 0) +
    ∑ p : OneShyIntervalPair N m,
      (G p.longStart p.longEnd * ∏ k ∈ Finset.Icc p.longStart p.longEnd, w k) *
        (A p.pairStart p.pairEnd * ∏ k ∈ Finset.Icc p.pairStart p.pairEnd, w k) := by
  classical
  let f := fun (σ : Equiv.Perm (Fin N)) (i : Fin N) =>
    (G i (σ i) * ∏ k ∈ Finset.Icc i (σ i), w k) *
      ∏ j ∈ (Finset.univ.filter (fun j => j.val ≤ (σ j).val)).erase i,
        A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k
  have hs : (∑ σ : Equiv.Perm (Fin N),
      if (∀ j, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ (σ i).val), f σ i else 0) =
    (∑ σ : Equiv.Perm (Fin N),
      if (∀ j, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ (σ i).val),
          if (σ i).val - i.val = m then f σ i else 0 else 0) +
    (∑ σ : Equiv.Perm (Fin N),
      if (∀ j, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ (σ i).val),
          if (σ i).val - i.val = m - 1 then f σ i else 0 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : (∀ j, j.val ≤ (σ j).val + 1) ∧
        (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m
    · simp only [ite_eq_left h]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hiup := (Finset.mem_filter.mp hi).2
      have hbound := hessenberg_permutation_interval_cost σ h.1 i hiup
      rw [h.2] at hbound
      by_cases hfull : (σ i).val - i.val = m
      · have hnot : (σ i).val - i.val ≠ m - 1 := by omega
        rw [ite_eq_left hfull, ite_eq_right hnot, add_zero]
      · rw [ite_eq_right hfull, zero_add]
        by_cases hone : (σ i).val - i.val = m - 1
        · rw [ite_eq_left hone]
        · rw [ite_eq_right hone]
          have hz := hshort i (σ i) hiup (by omega)
          simp only [f, hz, zero_mul]
    · simp only [ite_eq_right h, add_zero]
  change (∑ σ : Equiv.Perm (Fin N),
    if (∀ j, j.val ≤ (σ j).val + 1) ∧
        (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then
      ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ (σ i).val), f σ i else 0) = _
  rw [hs]
  congr 1
  · exact hessenberg_single_marked_activity_sum A G w hw m
  · exact one_shy_filtered_activity_sum hm A G w hw

end SkewCornerDescent.Matrix
