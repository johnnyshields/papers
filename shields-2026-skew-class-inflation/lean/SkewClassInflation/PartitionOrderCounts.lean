/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionCoarseningInventory

/-!
# Coarsening multiplicities as counts of actual retained orders

The finite-order coefficient reading used by the ribbon factorization
input to `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Permutation words are
deduplicated before counting, so repeated partition parts retain their
correct multiplicity.  The weight condition is explicit.  Sorry-free.
-/

namespace SkewClassInflation

/-- Distinct natural words obtained by ordering a specified list of positive partition parts. -/
def partitionOrders (l : List ℕ+) : Finset (List ℕ) :=
  (l.map PNat.val).permutations.toFinset

/-- The order set is exactly the actual unordered natural multiset of the given positive parts. -/
theorem partitionOrders_mem_iff (l : List ℕ+) (w : List ℕ) :
    w ∈ partitionOrders l ↔ (w : Multiset ℕ) = (l : Multiset ℕ+).map PNat.val := by
  simp only [partitionOrders, List.mem_toFinset, List.mem_permutations,
    Multiset.map_coe, Multiset.coe_eq_coe]

/-- Every ordered candidate consists of positive actual parts. -/
theorem partitionOrders_pos (l : List ℕ+) (w : List ℕ) (hw : w ∈ partitionOrders l) :
    ∀ a ∈ w, 0 < a := by
  have hp : w.Perm (l.map PNat.val) := List.mem_permutations.mp (List.mem_toFinset.mp hw)
  intro a ha
  obtain ⟨p, _, he⟩ := List.mem_map.mp (hp.subset ha)
  simpa only [he] using p.pos

/-- Every candidate ordering retains the exact specified partition weight. -/
theorem partitionOrders_sum (l : List ℕ+) (w : List ℕ) (hw : w ∈ partitionOrders l) :
    w.sum = (l.map PNat.val).sum :=
  (List.mem_permutations.mp (List.mem_toFinset.mp hw)).sum_eq

/-- A mask produces the partition exactly when its literal word is one of the actual orders. -/
theorem coarseningPartition_eq_list_iff_order {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) (S : Fin n → Bool) (l : List ℕ+) :
    coarseningPartition r hr S = (l : Multiset ℕ+) ↔ coarsenRows r S ∈ partitionOrders l := by
  rw [partitionOrders_mem_iff]
  constructor
  · intro he
    have hh := congrArg (Multiset.map PNat.val) he
    rw [coarseningPartition_values] at hh
    exact hh
  · intro he
    apply Multiset.map_injective PNat.coe_injective
    rw [coarseningPartition_values]
    exact he

/-- Every actual coefficient is the number of distinct partition orders retaining original cuts. -/
theorem coarseningInventory_count_orders {N : ℕ} (α : Composition N) (l : List ℕ+)
    (hsum : (l.map PNat.val).sum = N) :
    (coarseningInventory α).count (l : Multiset ℕ+) =
      ((partitionOrders l).filter (fun w => wordProperCuts w ⊆ properCuts α)).card := by
  classical
  by_cases hN : 0 < N
  · obtain ⟨n, r, hr, hα⟩ := exists_positive_row_word α hN
    have hw : (∑ i, r i) = N := by
      have hh := congrArg List.sum hα
      simpa only [List.sum_ofFn, α.blocks_sum] using hh
    have hc : properCuts (rowComposition r hr) = properCuts α :=
      properCuts_eq_of_blocks_eq (rowComposition r hr) α hα
    rw [coarseningInventory_eq_of_row_word α r hr hα,
      coarseningPartitions_count_filter r hr (l : Multiset ℕ+)]
    refine Finset.card_bij (fun S _ => coarsenRows r S) ?_ ?_ ?_
    · intro S hS
      have hm := (Finset.mem_filter.mp hS).2
      apply Finset.mem_filter.mpr
      refine ⟨(coarseningPartition_eq_list_iff_order r hr S l).mp hm, ?_⟩
      have hs := coarsenedComposition_cuts_subset r hr S
      rw [← wordProperCuts_blocks (coarsenedComposition r hr S), hc] at hs
      exact hs
    · intro S hS T hT he
      exact coarsenRows_injective r hr he
    · intro w hword
      obtain ⟨horder, hcuts⟩ := Finset.mem_filter.mp hword
      have hwpos := partitionOrders_pos l w horder
      have hwsum : w.sum = ∑ i, r i :=
        (partitionOrders_sum l w horder).trans (hsum.trans hw.symm)
      let γ : Composition (∑ i, r i) := ⟨w, fun {a} ha => hwpos a ha, hwsum⟩
      have hγ : properCuts γ ⊆ properCuts (rowComposition r hr) := by
        rw [← wordProperCuts_blocks γ, hc]
        exact hcuts
      obtain ⟨S, hS⟩ := (coarsenRows_exists_iff_cuts_subset r hr γ).mpr hγ
      have horderS : coarsenRows r S ∈ partitionOrders l := by rw [hS]; exact horder
      exact ⟨S, Finset.mem_filter.mpr ⟨by simp,
        (coarseningPartition_eq_list_iff_order r hr S l).mpr horderS⟩, hS⟩
  · have hzero : N = 0 := by omega
    have hblocks : α.blocks = [] := α.blocks_eq_nil.mpr hzero
    have hsum0 : (l.map PNat.val).sum = 0 := hsum.trans hzero
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons a l =>
        have ha := a.pos
        simp only [List.map_cons, List.sum_cons] at hsum0
        omega
    subst l
    rw [coarseningInventory_of_nil α hblocks]
    have ho : partitionOrders ([] : List ℕ+) = {[]} := by simp [partitionOrders]
    rw [ho]
    have hf : ({[]} : Finset (List ℕ)).filter (fun w => wordProperCuts w ⊆ properCuts α) =
        {[]} := by
      apply Finset.filter_eq_self.mpr
      intro w hw
      have he : w = [] := Finset.mem_singleton.mp hw
      subst w
      rw [wordProperCuts_nil]
      exact Finset.empty_subset _
    rw [hf, Finset.card_singleton]
    rfl

end SkewClassInflation
