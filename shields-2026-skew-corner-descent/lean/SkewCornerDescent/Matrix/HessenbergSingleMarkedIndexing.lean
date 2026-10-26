/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergIntervalSum
import SkewCornerDescent.Matrix.HessenbergFrontierActivities

/-!
# Exact marked indexing of a cost-exhausting interval

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A marked interval spending the full selected cost has no other nontrivial
upper activity. Exact positional reindexing retains every interval start.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {N : ℕ} {R : Type*} [CommRing R]

/-- Every other upper activity of a cost-exhausting marked interval is a genuine
canceled diagonal, even if the marked activity itself vanishes. -/
theorem single_interval_remaining_activity (A : Matrix (Fin N) (Fin N) R)
    (w : Fin N → R) (hw : ∀ j, A j j * w j = 1)
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ j, j.val ≤ (σ j).val + 1)
    (i : Fin N) (hi : i.val ≤ (σ i).val)
    (hcost : (σ i).val - i.val =
      (Finset.univ.filter (fun j => (σ j).val < j.val)).card) :
    (∏ j ∈ (Finset.univ.filter (fun j => j.val ≤ (σ j).val)).erase i,
      A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k) = 1 := by
  classical
  apply Finset.prod_eq_one
  intro j hj
  have hne := (Finset.mem_erase.mp hj).1
  have hup := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
  have hdown := hessenberg_permutation_unique_forward σ hσ i hi hcost j hne
  have he : σ j = j := Fin.ext (by omega)
  rw [he, Finset.Icc_self, Finset.prod_singleton]
  exact hw j

/-- The complete marked full-cost sum is exactly the sum over literal interval
endpoints. No marked numerator is canceled and equal response values stay distinct. -/
theorem hessenberg_single_marked_activity_sum (A G : Matrix (Fin N) (Fin N) R)
    (w : Fin N → R) (hw : ∀ j, A j j * w j = 1) (m : ℕ) :
    (∑ σ : Equiv.Perm (Fin N),
      if (∀ j, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then
        ∑ i ∈ Finset.univ.filter (fun i => i.val ≤ (σ i).val),
          if (σ i).val - i.val = m then
            (G i (σ i) * ∏ k ∈ Finset.Icc i (σ i), w k) *
              ∏ j ∈ (Finset.univ.filter (fun j => j.val ≤ (σ j).val)).erase i,
                A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k
          else 0
      else 0) =
    ∑ i : Fin N, ∑ j : Fin N,
      if i.val ≤ j.val ∧ j.val - i.val = m then
        G i j * ∏ k ∈ Finset.Icc i j, w k else 0 := by
  classical
  rw [← hessenberg_interval_frontier_sum m
    (fun i j => G i j * ∏ k ∈ Finset.Icc i j, w k)]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : (∀ j, j.val ≤ (σ j).val + 1) ∧
      (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m
  · rw [ite_eq_left h, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val ≤ (σ i).val
    · rw [ite_eq_left hi]
      by_cases hm : (σ i).val - i.val = m
      · rw [ite_eq_left hm, ite_eq_left ⟨h.1, h.2, hi, hm⟩,
          single_interval_remaining_activity A w hw σ h.1 i hi (hm.trans h.2.symm), mul_one]
      · rw [ite_eq_right hm, ite_eq_right (fun he => hm he.2.2.2)]
    · rw [ite_eq_right hi, ite_eq_right (fun he => hi he.2.2.1)]
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun he => h ⟨he.1, he.2.1⟩)

end SkewCornerDescent.Matrix
