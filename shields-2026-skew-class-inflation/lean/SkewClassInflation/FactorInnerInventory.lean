/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.LargePartCoefficients

/-!
# Exact inner-inventory recovery for arbitrary product mates

The inner half of factor transport for `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Actual sampled factors and
outer inventory equality supply the same nonzero larger-part multiplier,
which cancels in every multipart inner coefficient.  Sorry-free.
-/

namespace SkewClassInflation

/-- Every positive composition has exactly one full-weight singleton coarsening. -/
theorem coarseningInventory_count_singleton {N : ℕ} (α : Composition N)
    (a : ℕ+) (ha : a.val = N) :
    (coarseningInventory α).count (([a] : List ℕ+) : Multiset ℕ+) = 1 := by
  classical
  rw [coarseningInventory_count_orders α [a] (by simpa only [List.map_singleton,
    List.sum_singleton] using ha)]
  have ho : partitionOrders [a] = {[a.val]} := by
    ext w
    simp only [partitionOrders, List.mem_toFinset, List.mem_permutations,
      List.map_singleton, Finset.mem_singleton, List.perm_singleton]
  rw [ho]
  have hf : ({[a.val]} : Finset (List ℕ)).filter
      (fun w => wordProperCuts w ⊆ properCuts α) = {[a.val]} := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    have he := Finset.mem_singleton.mp hw
    rw [he, wordProperCuts_single]
    exact Finset.empty_subset _
  rw [hf, Finset.card_singleton]

/-- Matching product inventories and matching outer inventories force matching inner inventories. -/
theorem compositionProduct_inner_inventory {M N : ℕ}
    (δ γ : Composition M) (ε η : Composition N) (hM : 2 ≤ M) (hN : 0 < N)
    (houter : coarseningInventory γ = coarseningInventory δ)
    (hproduct : coarseningInventory (compositionProduct γ η) =
      coarseningInventory (compositionProduct δ ε)) :
    coarseningInventory η = coarseningInventory ε := by
  apply coarseningInventory_eq_of_weighted_counts _ _ hN
  intro l hsum
  by_cases hl : 2 ≤ l.length
  · let q : ℕ+ := ⟨(M - 1) * N, Nat.mul_pos (by omega) hN⟩
    have hc := congrArg (fun C : Multiset (Multiset ℕ+) =>
      C.count ((q :: l : List ℕ+) : Multiset ℕ+)) hproduct
    rw [compositionProduct_largePart_count γ η hM hN l hsum hl,
      compositionProduct_largePart_count δ ε hM hN l hsum hl,
      coarseningInventory_cut_type γ δ houter 1] at hc
    have hmult : l.length - 1 + compositionCutType δ 1 ≠ 0 := by omega
    exact mul_left_cancel₀ hmult hc
  · have hne : l ≠ [] := by intro he; rw [he, List.map_nil, List.sum_nil] at hsum; omega
    have hlen : l.length = 1 := by
      have hh : 0 < l.length := List.length_pos_iff.mpr hne
      omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    have ha : a.val = N := by simpa only [List.map_singleton, List.sum_singleton] using hsum
    rw [coarseningInventory_count_singleton η a ha, coarseningInventory_count_singleton ε a ha]

/-- Every actual sampled inner of an arbitrary product mate has the original full inventory. -/
theorem inventory_mate_inner_inventory {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hM : 2 ≤ M) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε)) :
    coarseningInventory (periodicInner θ) = coarseningInventory ε := by
  apply compositionProduct_inner_inventory δ (periodicOuter θ) ε (periodicInner θ) hM hN
  · exact inventory_mate_outer_inventory δ ε (by omega) hN θ hInv
  · rw [inventory_mate_periodic_factorization δ ε hN θ hInv]
    exact hInv

/-- Arbitrary product mates factor literally into mates of both original factors. -/
theorem inventory_mate_factor_transport {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hM : 2 ≤ M) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε)) :
    compositionProduct (periodicOuter θ) (periodicInner θ) = θ ∧
      coarseningInventory (periodicOuter θ) = coarseningInventory δ ∧
      coarseningInventory (periodicInner θ) = coarseningInventory ε :=
  ⟨inventory_mate_periodic_factorization δ ε hN θ hInv,
    inventory_mate_outer_inventory δ ε (by omega) hN θ hInv,
    inventory_mate_inner_inventory δ ε hM hN θ hInv⟩

end SkewClassInflation
