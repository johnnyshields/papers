/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedPoleSum
import SkewCornerDescent.PhaseInventory
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Exposed leading poles of actual cyclic word inventories

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original coefficients»
(`sec:dual`, `lem:peeling`, `thm:dual-period`). Every start, occurrence and repeated wrap is
retained. Maximal counts and common-sign residual lengths are produced from the word, rather
than carried as valuation assumptions. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- Every position belongs to one full response class, even when coordinates are dependent. -/
theorem sum_class_window_counts {G α : Type*} [AddCommGroup G] [Fintype α] [DecidableEq α]
    (word : G → α) (step : G) (j : ℕ) (i : G) :
    (∑ X, windowSum (classMask word X) step j i) = j := by
  unfold windowSum
  rw [Finset.sum_comm]
  simp [classMask]

/-- Regrouping a complete window keeps each class's exact occurrence multiplicity. -/
theorem windowProduct_eq_class_product {G α R : Type*} [AddCommGroup G]
    [Fintype α] [DecidableEq α] [CommMonoid R]
    (word : G → α) (response : α → R) (step : G) (j : ℕ) (i : G) :
    windowProduct (response ∘ word) step j i =
      ∏ X, response X ^ windowSum (classMask word X) step j i := by
  unfold windowProduct windowSum
  calc
    _ = ∏ a ∈ Finset.range j, ∏ X, response X ^ classMask word X (i + a • step) := by
      apply Finset.prod_congr rfl
      intro a _
      simp [classMask]
    _ = ∏ X, ∏ a ∈ Finset.range j, response X ^ classMask word X (i + a • step) :=
      Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro X _
      rw [Finset.prod_pow_eq_pow_sum]

/-- Exact largest window count of a class, with all starts retained. -/
noncomputable def maximalClassWindowCount {G α : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq α] (word : G → α) (step : G) (j : ℕ) (X : α) : ℕ :=
  Finset.univ.sup (windowSum (classMask word X) step j)

/-- A nonempty cyclic word attains its actual maximum, including the zero-window case. -/
theorem exists_maximal_class_window {G α : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq α] (word : G → α) (step : G) (j : ℕ) (X : α) :
    ∃ i, windowSum (classMask word X) step j i =
      maximalClassWindowCount word step j X := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty : (Finset.univ : Finset G).Nonempty)
    (windowSum (classMask word X) step j)
  exact ⟨i, hi.symm⟩

/-- In either exposed chamber the inverse-window cleared numerator has exactly its maximal
anchor pole. All pole bounds and the common negative-chamber length come from actual counts. -/
theorem cyclic_inverse_window_numerator_eval_pos {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [CommRing R]
    (word : G → α) (step : G) (j : ℕ) (X : α) (num den : α → R)
    (φ : R →+* ℝ) (sign : ℝ) (hroot : φ (num X) = 0)
    (hden : ∀ Y, 0 < φ (den Y))
    (hsign : ∀ Y, Y ≠ X → 0 < sign * φ (num Y)) :
    let count := fun Y i => windowSum (classMask word Y) step j i
    let bound := maximalClassWindowCount word step j
    0 < sign ^ ((∑ Y ∈ Finset.univ.erase X, bound Y) - (j - bound X)) *
      φ (clearedPoleSum Finset.univ (num X) (bound X) (count X)
        (fun i => den X ^ count X i * ∏ Y ∈ Finset.univ.erase X,
          num Y ^ (bound Y - count Y i) * den Y ^ count Y i)) := by
  classical
  dsimp only
  let count := fun Y i => windowSum (classMask word Y) step j i
  let bound := maximalClassWindowCount word step j
  have hb : ∀ Y i, count Y i ≤ bound Y := fun _ _ => Finset.le_sup (Finset.mem_univ _)
  obtain ⟨i, hi⟩ := exists_maximal_class_window word step j X
  apply clearedInverseResponseSum_eval_pos Finset.univ (Finset.univ.erase X) (num X) (den X)
    (bound X) ((∑ Y ∈ Finset.univ.erase X, bound Y) - (j - bound X))
    (count X) bound (fun i Y => count Y i) num den φ sign hroot (hden X)
  · exact fun i _ => hb X i
  · exact ⟨i, Finset.mem_univ _, hi⟩
  · intro Y hY
    exact hsign Y (Finset.mem_erase.mp hY).1
  · exact fun Y _ => hden Y
  · intro i _ hi
    have ht : (∑ Y ∈ Finset.univ.erase X, count Y i) + bound X = j := by
      rw [← hi, Finset.sum_erase_add _ _ (Finset.mem_univ X)]
      exact sum_class_window_counts word step j i
    have he : (∑ Y ∈ Finset.univ.erase X, (bound Y - count Y i)) +
        (∑ Y ∈ Finset.univ.erase X, count Y i) = ∑ Y ∈ Finset.univ.erase X, bound Y := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun Y _ => Nat.sub_add_cancel (hb Y i)
    omega

/-- Specialization rules out cancellation by the anchor numerator. -/
theorem cyclic_inverse_window_numerator_not_dvd {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [CommRing R]
    (word : G → α) (step : G) (j : ℕ) (X : α) (num den : α → R)
    (φ : R →+* ℝ) (sign : ℝ) (hroot : φ (num X) = 0)
    (hden : ∀ Y, 0 < φ (den Y))
    (hsign : ∀ Y, Y ≠ X → 0 < sign * φ (num Y)) :
    let count := fun Y i => windowSum (classMask word Y) step j i
    let bound := maximalClassWindowCount word step j
    ¬ num X ∣ clearedPoleSum Finset.univ (num X) (bound X) (count X)
      (fun i => den X ^ count X i * ∏ Y ∈ Finset.univ.erase X,
        num Y ^ (bound Y - count Y i) * den Y ^ count Y i) := by
  have hpos := cyclic_inverse_window_numerator_eval_pos word step j X num den φ sign
    hroot hden hsign
  dsimp only at hpos ⊢
  rintro ⟨a, ha⟩
  rw [ha, map_mul, hroot, zero_mul, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The same produced polynomial numerator equals the complete cyclic reciprocal inventory in
the original fraction field. Neither all-start multiplicity nor repeated wraps are discarded. -/
theorem cyclic_inverse_window_numerator_fraction {G α R F : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [CommRing R] [Field F]
    (word : G → α) (step : G) (j : ℕ) (X : α) (num den : α → R)
    (φ : R →+* F) (hnum : ∀ Y, φ (num Y) ≠ 0) :
    let count := fun Y i => windowSum (classMask word Y) step j i
    let bound := maximalClassWindowCount word step j
    φ (clearedPoleSum Finset.univ (num X) (bound X) (count X)
      (fun i => den X ^ count X i * ∏ Y ∈ Finset.univ.erase X,
        num Y ^ (bound Y - count Y i) * den Y ^ count Y i)) /
      (φ (num X) ^ bound X * ∏ Y ∈ Finset.univ.erase X, φ (num Y) ^ bound Y) =
      ∑ i, (windowProduct ((fun Y => φ (num Y) / φ (den Y)) ∘ word) step j i)⁻¹ := by
  classical
  dsimp only
  let count := fun Y i => windowSum (classMask word Y) step j i
  let bound := maximalClassWindowCount word step j
  have hb : ∀ Y i, count Y i ≤ bound Y := fun _ _ => Finset.le_sup (Finset.mem_univ _)
  rw [clearedInverseResponseSum_fraction Finset.univ (Finset.univ.erase X)
    (num X) (den X) (bound X) (count X) bound (fun i Y => count Y i) num den φ
    (hnum X) (fun Y _ => hnum Y) (fun i _ => hb X i) (fun i _ Y _ => hb Y i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [windowProduct_eq_class_product word (fun Y => φ (num Y) / φ (den Y))]
  simp only [← Finset.prod_inv_distrib, ← inv_pow, inv_div]
  exact Finset.mul_prod_erase Finset.univ
    (fun Y => (φ (den Y) / φ (num Y)) ^ windowSum (classMask word Y) step j i)
    (Finset.mem_univ X)

end SkewCornerDescent.CyclicWindows
