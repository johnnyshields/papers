/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CoarseningCutSets
import Mathlib.Data.List.Permutation

/-!
# Two-part coarsenings and reflected cut multiplicities

The two-part reading of the actual coarsening multiset used by the
ribbon factorization input to `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Ordered coarsenings have
unique masks; unordered two-part partitions retain both possible
orders, with the repeated-part case counted only once.  Sorry-free.
-/

namespace SkewClassInflation

private theorem word_multiset_eq_pair (w : List ℕ) (a b : ℕ) :
    (w : Multiset ℕ) = a ::ₘ b ::ₘ 0 ↔ w = [a, b] ∨ w = [b, a] := by
  change (w : Multiset ℕ) = ([a, b] : List ℕ) ↔ _
  rw [Multiset.coe_eq_coe, List.perm_pair]

/-- A specified actual unordered two-part partition permits exactly the two displayed orders. -/
theorem coarseningPartition_eq_pair {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (S : Fin n → Bool) (a b : ℕ+) :
    coarseningPartition r hr S = a ::ₘ b ::ₘ 0 ↔
      coarsenRows r S = [a.val, b.val] ∨ coarsenRows r S = [b.val, a.val] := by
  constructor
  · intro he
    have hh := congrArg (Multiset.map PNat.val) he
    rw [coarseningPartition_values] at hh
    exact (word_multiset_eq_pair _ _ _).mp hh
  · intro he
    apply Multiset.map_injective PNat.coe_injective
    rw [coarseningPartition_values]
    exact (word_multiset_eq_pair _ _ _).mpr he

/-- A two-part ordered coarsening exists precisely when its single boundary is an original cut. -/
theorem coarsenRows_two_exists {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (a b : ℕ+) (hs : a.val + b.val = ∑ i, r i) :
    (∃ S : Fin n → Bool, coarsenRows r S = [a.val, b.val]) ↔
      a.val ∈ properCuts (rowComposition r hr) := by
  let γ : Composition (∑ i, r i) :=
    ⟨[a.val, b.val], by simp [a.pos, b.pos], by simpa only [List.sum_cons, List.sum_nil,
      add_zero] using hs⟩
  have hc : properCuts γ = {a.val} := by
    rw [← wordProperCuts_blocks γ]
    change wordProperCuts ([a.val] ++ [b.val]) = _
    rw [wordProperCuts_append_single]
    rfl
  have hh := coarsenRows_exists_iff_cuts_subset r hr γ
  rw [hc, Finset.singleton_subset_iff] at hh
  exact hh

/-- Positivity makes the preimage of every specified ordered coarsening a singleton or empty. -/
theorem coarsenRows_preimage_card {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (w : List ℕ) :
    (Finset.univ.filter (fun S : Fin n → Bool => coarsenRows r S = w)).card =
      if ∃ S : Fin n → Bool, coarsenRows r S = w then 1 else 0 := by
  classical
  by_cases he : ∃ S : Fin n → Bool, coarsenRows r S = w
  · obtain ⟨S, hS⟩ := he
    have hf : Finset.univ.filter (fun T : Fin n → Bool => coarsenRows r T = w) = {S} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hT
        exact coarsenRows_injective r hr (hT.trans hS.symm)
      · rintro rfl
        exact hS
    rw [hf, Finset.card_singleton, ite_eq_left ⟨S, hS⟩]
  · rw [ite_eq_right he]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    have hh := (Finset.mem_filter.mp hS).2
    exact he ⟨S, hh⟩

/-- Exact unordered two-part multiplicity, with the midpoint order counted only once. -/
theorem coarseningPartitions_count_pair {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (a b : ℕ+) (hs : a.val + b.val = ∑ i, r i) :
    (coarseningPartitions r hr).count (a ::ₘ b ::ₘ 0) =
      if a = b then (if a.val ∈ properCuts (rowComposition r hr) then 1 else 0)
      else (if a.val ∈ properCuts (rowComposition r hr) then 1 else 0) +
        (if b.val ∈ properCuts (rowComposition r hr) then 1 else 0) := by
  classical
  rw [coarseningPartitions_count_filter r hr (a ::ₘ b ::ₘ 0)]
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    have hf : (Finset.univ.filter (fun S : Fin n → Bool =>
        coarseningPartition r hr S = a ::ₘ a ::ₘ 0)) =
        Finset.univ.filter (fun S : Fin n → Bool => coarsenRows r S = [a.val, a.val]) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        coarseningPartition_eq_pair, or_self]
    rw [hf, coarsenRows_preimage_card r hr [a.val, a.val]]
    simp only [coarsenRows_two_exists r hr a a hs]
  · rw [ite_eq_right hab]
    let F := Finset.univ.filter (fun S : Fin n → Bool => coarsenRows r S = [a.val, b.val])
    let G := Finset.univ.filter (fun S : Fin n → Bool => coarsenRows r S = [b.val, a.val])
    have hf : (Finset.univ.filter (fun S : Fin n → Bool =>
        coarseningPartition r hr S = a ::ₘ b ::ₘ 0)) = F ∪ G := by
      ext S
      simp only [F, G, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, coarseningPartition_eq_pair]
    have hd : Disjoint F G := by
      apply Finset.disjoint_left.mpr
      intro S hF hG
      have h1 := (Finset.mem_filter.mp hF).2
      have h2 := (Finset.mem_filter.mp hG).2
      have he : [a.val, b.val] = [b.val, a.val] := h1.symm.trans h2
      exact hab (PNat.coe_injective (List.cons.inj he).1)
    rw [hf, Finset.card_union_of_disjoint hd]
    dsimp only [F, G]
    rw [coarsenRows_preimage_card r hr [a.val, b.val],
      coarsenRows_preimage_card r hr [b.val, a.val]]
    have hs' : b.val + a.val = ∑ i, r i := by rw [Nat.add_comm]; exact hs
    simp only [coarsenRows_two_exists r hr a b hs, coarsenRows_two_exists r hr b a hs']

/-- Doubling the midpoint multiplicity gives the same reflected-cut count in both regimes. -/
theorem coarsening_two_cut_type {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (a b : ℕ+) (hs : a.val + b.val = ∑ i, r i) :
    (if a = b then 2 else 1) * (coarseningPartitions r hr).count (a ::ₘ b ::ₘ 0) =
      (if a.val ∈ properCuts (rowComposition r hr) then 1 else 0) +
        (if b.val ∈ properCuts (rowComposition r hr) then 1 else 0) := by
  classical
  rw [coarseningPartitions_count_pair r hr a b hs]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, two_mul]
  · simp only [ite_eq_right hab, one_mul]

/-- Equal actual coarsening inventories preserve the two-part cut type, including the midpoint. -/
theorem reflected_cut_type_of_coarsening_eq {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) (a b : ℕ+)
    (hR : a.val + b.val = ∑ i, r i) (hS : a.val + b.val = ∑ i, s i)
    (he : coarseningPartitions r hr = coarseningPartitions s hs) :
    (if a.val ∈ properCuts (rowComposition r hr) then 1 else 0) +
        (if b.val ∈ properCuts (rowComposition r hr) then 1 else 0) =
      (if a.val ∈ properCuts (rowComposition s hs) then 1 else 0) +
        (if b.val ∈ properCuts (rowComposition s hs) then 1 else 0) := by
  have h1 := coarsening_two_cut_type r hr a b hR
  have h2 := coarsening_two_cut_type s hs a b hS
  rw [he] at h1
  exact h1.symm.trans h2

end SkewClassInflation
