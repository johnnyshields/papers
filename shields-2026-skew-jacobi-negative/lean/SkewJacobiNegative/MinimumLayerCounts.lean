/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseSafeCuts

/-!
# Five-row uncollected minimum-gap layers

The positional counts in `eq:task-count` of
`shields-2026-skew-jacobi-negative.tex`.  All subsets of the four seam
positions are counted; no bound is placed on any diagram parameter.
-/

namespace SkewJacobiNegative.Staircase
open scoped BigOperators
open Finset Gluing

/-- Number of joined minimum seams in one actual interval-expansion mask. -/
def markedSeams (M : Finset (Fin 4)) (S : Fin 4 → Bool) : ℕ :=
  (M.filter fun i => S i = true).card

/-- The uncollected masks belonging to one minimum-generator layer. -/
def maskLayerCount (M : Finset (Fin 4)) (j : ℕ) : ℕ :=
  (univ.filter fun S : Fin 4 → Bool => markedSeams M S = j).card

/-- Exhaustive positional combinatorics, uniform in the numerical gap values. -/
theorem mask_layer_count_finite (M : Finset (Fin 4)) (j : Fin 5) :
    maskLayerCount M j.val = M.card.choose j.val * 2 ^ (4 - M.card) := by
  revert M j
  decide +kernel

/-- A mask cannot select more than the available four seams. -/
theorem markedSeams_le_four (M : Finset (Fin 4)) (S : Fin 4 → Bool) :
    markedSeams M S ≤ 4 := by
  exact (Finset.card_filter_le _ _).trans (Finset.card_le_univ _)

/-- The same count formula holds for every natural layer, including empty higher layers. -/
theorem mask_layer_count (M : Finset (Fin 4)) (j : ℕ) :
    maskLayerCount M j = M.card.choose j * 2 ^ (4 - M.card) := by
  by_cases hj : j < 5
  · exact mask_layer_count_finite M ⟨j, hj⟩
  · have hm : M.card ≤ 4 := Finset.card_le_univ M
    have hz : univ.filter (fun S : Fin 4 → Bool => markedSeams M S = j) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro S hS
      have he := (Finset.mem_filter.mp hS).2
      have hb := markedSeams_le_four M S
      omega
    rw [maskLayerCount, hz, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega), zero_mul]

/-- Every interval term belongs to exactly one layer; all sixteen masks are retained. -/
theorem mask_layers_sum (M : Finset (Fin 4)) :
    (∑ j : Fin 5, maskLayerCount M j.val) = 16 := by
  revert M
  decide +kernel

/-- The minimum-gap position set in an actual five-row profile. -/
def minimumSeams (P : Profile 4) (z : ℕ+) : Finset (Fin 4) :=
  univ.filter fun i => P.g i = z.val

@[simp] theorem minimumSeams_card (P : Profile 4) (z : ℕ+) :
    (minimumSeams P z).card = minimumMultiplicity P z := by
  rw [minimumSeams, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

/-- The manuscript's binomial layer count, before any equal-label collection. -/
theorem minimum_layer_term_count (P : Profile 4) (z : ℕ+) (j : ℕ) :
    maskLayerCount (minimumSeams P z) j =
      (minimumSeams P z).card.choose j * 2 ^ (4 - (minimumSeams P z).card) :=
  mask_layer_count _ _

theorem minimum_layers_total (P : Profile 4) (z : ℕ+) :
    (∑ j : Fin 5, maskLayerCount (minimumSeams P z) j.val) = 16 := mask_layers_sum _

/-- A minimum seam value is strictly below every row, in every finite order. -/
theorem row_gt_minimum {n : ℕ} (P : Profile n) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val)
    (i : Fin (n + 1)) : z.val < P.r i := by
  obtain ⟨j₀, _⟩ := hocc
  have hn : 0 < n := by have := j₀.isLt; omega
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val, hi⟩
    have he : j.castSucc = i := Fin.ext rfl
    have hg := P.g_lt_castSucc j
    rw [he] at hg
    exact (hmin j).trans_lt hg
  · let j : Fin n := ⟨n - 1, by omega⟩
    have he : j.succ = i := by apply Fin.ext; dsimp [j]; omega
    have hg := P.g_lt_succ j
    rw [he] at hg
    exact (hmin j).trans_lt hg

/-- The minimum generator cannot occur as an interval label, including singleton intervals. -/
theorem interval_gt_minimum {n : ℕ} (P : Profile n) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val)
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    (z.val : ℤ) < P.intervalLabel a b := by
  have hr := row_gt_minimum P z hmin hocc a
  have hc := P.toBetaDiagram.col_strictAnti.antitone hab
  change P.zeta b ≤ P.zeta a at hc
  have hi := P.xi_sub_zeta a
  rw [GeneralHessenberg.intervalLabel_eq_index P a b hab]
  omega

end SkewJacobiNegative.Staircase
