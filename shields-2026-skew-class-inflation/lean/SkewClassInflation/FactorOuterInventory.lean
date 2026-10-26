/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ScaledWordCuts

/-!
# Exact recovery of the actual sampled outer inventory

The outer half of factor transport for `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Partitions all of whose parts
are whole inner weights count precisely the retained-cut coarsenings
of the sampled outer factor.  Sorry-free.
-/

namespace SkewClassInflation

/-- Every member of a positive composition's actual inventory has its exact total weight. -/
theorem coarseningInventory_member_weight {M : ℕ} (α : Composition M) (hM : 0 < M)
    (μ : Multiset ℕ+) (hμ : μ ∈ coarseningInventory α) :
    (μ.map PNat.val).sum = M := by
  obtain ⟨ζ, _, hvalues⟩ := coarseningInventory_member_composition α hM μ hμ
  have hh := congrArg Multiset.sum hvalues
  change ζ.blocks.sum = (μ.map PNat.val).sum at hh
  exact hh.symm.trans ζ.blocks_sum

/-- Equality of all correctly weighted list coefficients determines a positive inventory. -/
theorem coarseningInventory_eq_of_weighted_counts {M : ℕ} (α β : Composition M)
    (hM : 0 < M)
    (hcounts : ∀ l : List ℕ+, (l.map PNat.val).sum = M →
      (coarseningInventory α).count (l : Multiset ℕ+) =
        (coarseningInventory β).count (l : Multiset ℕ+)) :
    coarseningInventory α = coarseningInventory β := by
  classical
  apply Multiset.ext.mpr
  intro μ
  by_cases hw : (μ.map PNat.val).sum = M
  · have hl : (μ.toList.map PNat.val).sum = M := by
      have hh := congrArg (fun ν : Multiset ℕ+ => (ν.map PNat.val).sum)
        (Multiset.coe_toList μ)
      exact hh.trans hw
    simpa only [Multiset.coe_toList] using hcounts μ.toList hl
  · have hα : μ ∉ coarseningInventory α := fun hm =>
      hw (coarseningInventory_member_weight α hM μ hm)
    have hβ : μ ∉ coarseningInventory β := fun hm =>
      hw (coarseningInventory_member_weight β hM μ hm)
    rw [Multiset.count_eq_zero.mpr hα, Multiset.count_eq_zero.mpr hβ]

/-- Scaled partition coefficients recover the full corresponding sampled-outer coefficient. -/
theorem coarseningInventory_count_scaled_outer {M N : ℕ}
    (θ : Composition (M * N)) (hN : 0 < N) (l : List ℕ+)
    (hsum : (l.map PNat.val).sum = M) :
    (coarseningInventory θ).count (l.map (scalePositivePart N hN) : Multiset ℕ+) =
      (coarseningInventory (periodicOuter θ)).count (l : Multiset ℕ+) := by
  classical
  have hs : ((l.map (scalePositivePart N hN)).map PNat.val).sum = M * N := by
    rw [scalePositivePart_values, sum_map_mul_right, hsum]
  rw [coarseningInventory_count_orders θ _ hs,
    coarseningInventory_count_orders (periodicOuter θ) l hsum]
  symm
  refine Finset.card_bij (fun w _ => w.map (fun x => x * N)) ?_ ?_ ?_
  · intro w hw
    obtain ⟨ho, hc⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [partitionOrders_scale]
      exact Finset.mem_image.mpr ⟨w, ho, rfl⟩
    · exact (scaled_word_cuts_subset_iff θ w ((partitionOrders_sum l w ho).trans hsum)
        (partitionOrders_pos l w ho)).mpr hc
  · intro u _ v _ he
    exact (List.map_injective_iff.mpr (fun a b h =>
      mul_right_cancel₀ (Nat.ne_of_gt hN) h)) he
  · intro v hv
    obtain ⟨ho, hc⟩ := Finset.mem_filter.mp hv
    rw [partitionOrders_scale] at ho
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ho
    refine ⟨w, Finset.mem_filter.mpr ⟨hw, ?_⟩, rfl⟩
    exact (scaled_word_cuts_subset_iff θ w ((partitionOrders_sum l w hw).trans hsum)
      (partitionOrders_pos l w hw)).mp hc

/-- Every inventory mate has the source outer factor's exact complete coarsening inventory. -/
theorem inventory_mate_outer_inventory {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hM : 0 < M) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε)) :
    coarseningInventory (periodicOuter θ) = coarseningInventory δ := by
  apply coarseningInventory_eq_of_weighted_counts _ _ hM
  intro l hsum
  rw [← coarseningInventory_count_scaled_outer θ hN l hsum, hInv,
    coarseningInventory_count_scaled_outer (compositionProduct δ ε) hN l hsum,
    periodicOuter_compositionProduct δ ε hN]

end SkewClassInflation
