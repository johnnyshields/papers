/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ReflectedCutTypes

/-!
# Literal row words of reconstructible ribbons

Canonical composition reconstruction transfers to arbitrary positive row
vectors, with the total weight produced by their actual coarsening equality.
This supplies the word-level conclusion used for
`lem:merged-block-rigidity` of `shields-2026-skew-class-inflation.tex`.
Sorry-free.
-/

namespace SkewClassInflation

/-- Reconstruction is unchanged by a proved equality of the complete literal words. -/
theorem ribbonReconstructible_of_blocks_eq {M N : ℕ} (α : Composition M) (β : Composition N)
    (he : α.blocks = β.blocks) (hr : ribbonReconstructible α) : ribbonReconstructible β := by
  have hh : (⟨M, α⟩ : (K : ℕ) × Composition K) = ⟨N, β⟩ :=
    Composition.sigma_eq_iff_blocks_eq.mpr he
  cases hh
  exact hr

/-- Actual equal ribbon functions reconstruct the whole positive word up to its reversal. -/
theorem ribbon_eq_reconstruct_of_reconstructible {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hrec : ribbonReconstructible (rowComposition r hr))
    (he : ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s)) :
    List.ofFn s = List.ofFn r ∨ List.ofFn s = (List.ofFn r).reverse := by
  have hparts := (ribbon_eq_iff_coarseningPartitions r s hr hs).mp he
  have hweight := coarseningPartitions_row_sum r s hr hs hparts
  let β := (rowComposition s hs).cast hweight.symm
  have hInv : coarseningInventory β = coarseningInventory (rowComposition r hr) := by
    have hb : β.blocks = (rowComposition s hs).blocks := rfl
    rw [coarseningInventory_eq_of_blocks_eq β (rowComposition s hs) hb,
      coarseningInventory_rowComposition, coarseningInventory_rowComposition]
    exact hparts.symm
  rcases hrec β hInv with hh | hh
  · exact Or.inl (congrArg Composition.blocks hh)
  · apply Or.inr
    change β.blocks = (rowComposition r hr).blocks.reverse
    rw [← Composition.reverse_blocks]
    exact congrArg Composition.blocks hh

/-- Equal actual nonempty ribbon functions preserve the original parts with multiplicity. -/
theorem ribbon_eq_blocks_perm {M N : ℕ} (α : Composition M) (β : Composition N)
    (hM : 0 < M) (hN : 0 < N) (he : ribbonWord α.blocks = ribbonWord β.blocks) :
    α.blocks.Perm β.blocks := by
  obtain ⟨n, r, hr, hα⟩ := exists_positive_row_word α hM
  obtain ⟨m, s, hs, hβ⟩ := exists_positive_row_word β hN
  have hword : ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s) := by
    rw [hα, hβ]
    exact he
  have hparts := (ribbon_eq_iff_coarseningPartitions r s hr hs).mp hword
  have hh := congrArg (Multiset.map PNat.val)
    (coarseningPartitions_rowPartition r s hr hs hparts)
  rw [rowPartition_values, rowPartition_values, hα, hβ] at hh
  exact Multiset.coe_eq_coe.mp hh

/-- The all-one outer word has a literal singleton ribbon class. -/
theorem ribbonClass_ones (M : ℕ) (hM : 0 < M) :
    ribbonClass (Composition.ones M) = {Composition.ones M} := by
  ext β
  constructor
  · intro hβ
    apply Set.mem_singleton_iff.mpr
    apply Composition.eq_ones_iff.mpr
    have hp := ribbon_eq_blocks_perm β (Composition.ones M) hM hM hβ
    intro a ha
    have hh := hp.subset ha
    rw [Composition.ones_blocks] at hh
    exact List.eq_of_mem_replicate hh
  · intro hβ
    rw [Set.mem_singleton_iff] at hβ
    subst β
    rfl

end SkewClassInflation
