/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ResidueCoarsenings
import SkewClassInflation.CompositionCoarseningInventory

/-!
# Actual unordered coarsening residues of ordinary products

The inventory form of the residue-count input to factor-reversal
classification in `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Inventory membership supplies
an actual ordered adjacent coarsening before residue reduction is
applied.  Every repeated part is retained with its multiplicity.
Sorry-free.
-/

namespace SkewClassInflation

/-- Every actual nonempty inventory member is realized by a composition retaining original cuts. -/
theorem coarseningInventory_member_composition {N : ℕ} (α : Composition N) (hN : 0 < N)
    (μ : Multiset ℕ+) (hμ : μ ∈ coarseningInventory α) :
    ∃ ζ : Composition N, properCuts ζ ⊆ properCuts α ∧
      (ζ.blocks : Multiset ℕ) = μ.map PNat.val := by
  obtain ⟨n, r, hr, hword⟩ := exists_positive_row_word α hN
  rw [coarseningInventory_eq_of_row_word α r hr hword] at hμ
  obtain ⟨S, _, hS⟩ := Multiset.mem_map.mp hμ
  have hsum := congrArg List.sum hword
  rw [List.sum_ofFn, α.blocks_sum] at hsum
  let ζ := (coarsenedComposition r hr S).cast hsum
  refine ⟨ζ, ?_, ?_⟩
  · have hrow : properCuts (rowComposition r hr) = properCuts α :=
      properCuts_eq_of_blocks_eq (rowComposition r hr) α hword
    have hc := coarsenedComposition_cuts_subset r hr S
    change properCuts ((coarsenedComposition r hr S).cast hsum) ⊆ properCuts α
    rw [properCuts_cast]
    rwa [hrow] at hc
  · have hv := coarseningPartition_values r hr S
    rw [hS] at hv
    exact hv.symm

/-- The original actual positive parts, retaining repeated values in their unordered form. -/
def compositionPartition {N : ℕ} (α : Composition N) : Multiset ℕ+ :=
  (positiveWord α.blocks (fun _ ha => α.blocks_pos ha) : Multiset ℕ+)

/-- Forgetting positivity recovers the complete actual original part multiset. -/
theorem compositionPartition_values {N : ℕ} (α : Composition N) :
    (compositionPartition α).map PNat.val = (α.blocks : Multiset ℕ) := by
  rw [compositionPartition, Multiset.map_coe, positiveWord_values]

/-- Every composition retaining original cuts contributes its actual part partition. -/
theorem coarseningInventory_contains_composition {N : ℕ}
    (α ζ : Composition N) (hN : 0 < N) (hcuts : properCuts ζ ⊆ properCuts α) :
    compositionPartition ζ ∈ coarseningInventory α := by
  obtain ⟨n, r, hr, hword⟩ := exists_positive_row_word α hN
  have hsum := congrArg List.sum hword
  rw [List.sum_ofFn, α.blocks_sum] at hsum
  have hrow : properCuts (rowComposition r hr) = properCuts α :=
    properCuts_eq_of_blocks_eq (rowComposition r hr) α hword
  have hc : properCuts (ζ.cast hsum.symm) ⊆ properCuts (rowComposition r hr) := by
    rw [properCuts_cast, hrow]
    exact hcuts
  obtain ⟨S, hS⟩ := (coarsenRows_exists_iff_cuts_subset r hr (ζ.cast hsum.symm)).mpr hc
  change coarsenRows r S = ζ.blocks at hS
  have hpart : coarseningPartition r hr S = compositionPartition ζ := by
    change ((positiveWord (coarsenRows r S) (coarsenRows_pos r hr S) : List ℕ+) : Multiset ℕ+) =
      ((positiveWord ζ.blocks (fun a ha => ζ.blocks_pos ha) : List ℕ+) : Multiset ℕ+)
    exact congrArg (fun w : List ℕ+ => (w : Multiset ℕ+))
      (positiveWord_congr _ _ hS)
  rw [coarseningInventory_eq_of_row_word α r hr hword, ← hpart]
  exact coarseningPartition_mem r hr S

/-- Reading residues from the actual partition agrees with reading the original ordered parts. -/
theorem compositionPartition_residue_values {K : ℕ} (ζ : Composition K) (n : ℕ) :
    (compositionPartition ζ).map (fun a => a.val % n) =
      ((ζ.blocks.map (fun x => x % n) : List ℕ) : Multiset ℕ) := by
  simpa only [Multiset.map_map, Multiset.map_coe, Function.comp_def] using
    congrArg (Multiset.map (fun x : ℕ => x % n)) (compositionPartition_values ζ)

/-- The actual multiset of nonzero part residues of a positive partition. -/
def positivePartitionResidues (μ : Multiset ℕ+) (n : ℕ) : Multiset ℕ :=
  (μ.map (fun a => a.val % n)).filter (fun x => x ≠ 0)

/-- The nonzero residue multiset retains exactly the actual positive residue word. -/
theorem positivePartitionResidues_compositionPartition {K : ℕ} (ζ : Composition K) (n : ℕ) :
    positivePartitionResidues (compositionPartition ζ) n =
      (residueWord ζ.blocks n : Multiset ℕ) := by
  rw [positivePartitionResidues, compositionPartition_residue_values, Multiset.filter_coe]
  rfl

/-- A one-tour actual coarsening partition has no more nonzero residues than the inner has parts. -/
theorem coarseningInventory_residue_bound {M N : ℕ} (γ : Composition M) (β : Composition N)
    (hM : 0 < M) (hN : 0 < N) (μ : Multiset ℕ+)
    (hμ : μ ∈ coarseningInventory (compositionProduct γ β))
    (hsum : (μ.map (fun a => a.val % N)).sum = N) :
    (positivePartitionResidues μ N).card ≤ β.length := by
  obtain ⟨ζ, hcuts, hvalues⟩ := coarseningInventory_member_composition
    (compositionProduct γ β) (Nat.mul_pos hM hN) μ hμ
  have hremValues : ((ζ.blocks.map (fun x => x % N) : List ℕ) : Multiset ℕ) =
      μ.map (fun a => a.val % N) := by
    simpa only [Multiset.map_coe, Multiset.map_map, Function.comp_def] using
      congrArg (Multiset.map (fun x : ℕ => x % N)) hvalues
  have hsumWord : (ζ.blocks.map (fun x => x % N)).sum = N := by
    have hh := congrArg Multiset.sum hremValues
    change (ζ.blocks.map (fun x => x % N)).sum = (μ.map (fun a => a.val % N)).sum at hh
    exact hh.trans hsum
  have hfilter := congrArg (Multiset.filter (fun x : ℕ => x ≠ 0)) hremValues
  rw [Multiset.filter_coe] at hfilter
  have hcard := congrArg Multiset.card hfilter
  change (residueWord ζ.blocks N).length = (positivePartitionResidues μ N).card at hcard
  rw [← hcard]
  exact residue_coarsening_length_bound γ β hN ζ hcuts hsumWord

end SkewClassInflation
