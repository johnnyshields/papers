/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FourPartCutMasks

/-!
# Actual inventory meaning of the four-part subset table

The four-part counting bridge for factor-reversal reconstruction in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The exact labeled coarsening count equals the subset-mask count for
the actual four positive parts.  Repeated part values remain labeled
throughout, with their multiplicity already supplied by the inventory.
Sorry-free.
-/

namespace SkewClassInflation

/-- A literal four-part word has exactly its three actual proper prefix positions. -/
theorem wordProperCuts_four (a b c d : ℕ) :
    wordProperCuts [a, b, c, d] = {a, a + b, a + b + c} := by
  change wordProperCuts ([a, b, c] ++ [d]) = _
  rw [wordProperCuts_append_single]
  simp [prefixEnds, Nat.add_assoc]

/-- Actual four-part retention reads the first part, first pair, and reflected last part. -/
theorem fourPart_retained_iff {N : ℕ} (α : Composition N) (a b c d : ℕ)
    (hsum : a + b + c + d = N) :
    wordProperCuts [a, b, c, d] ⊆ properCuts α ↔
      a ∈ properCuts α ∧ a + b ∈ properCuts α ∧ N - d ∈ properCuts α := by
  have hh : a + b + c = N - d := by omega
  rw [wordProperCuts_four, hh]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- Exact actual labeled four-part counts agree with the subset-mask representation. -/
theorem labeled_fourPart_mask_count {N : ℕ} (α : Composition N) (a b c d : ℕ+)
    (hsum : a.val + b.val + c.val + d.val = N) :
    (labeledCoarseningOrders α ![a, b, c, d]).card =
      fourPartMaskCount (fourPartLeftCuts α a.val b.val c.val)
        (fourPartRightCuts α a.val b.val c.val) := by
  classical
  let f := fourPartValues a.val b.val c.val d.val
  have hvalues : (fun i : Fin 4 => (![a, b, c, d] i).val) = f := by
    funext i
    fin_cases i <;> rfl
  have hbase : (List.ofFn f).sum = N := by
    change a.val + (b.val + (c.val + (d.val + 0))) = N
    omega
  unfold fourPartMaskCount labeledCoarseningOrders
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hvalues]
  have hword : labeledOrderWord f σ = [f (σ 0), f (σ 1), f (σ 2), f (σ 3)] := rfl
  have hσsum : f (σ 0) + f (σ 1) + f (σ 2) + f (σ 3) = N := by
    have hh := (σ.ofFn_comp_perm f).sum_eq.trans hbase
    change (labeledOrderWord f σ).sum = N at hh
    rw [hword] at hh
    simp only [List.sum_cons, List.sum_nil, add_zero] at hh
    omega
  rw [hword, fourPart_retained_iff α _ _ _ _ hσsum,
    fourPart_mask_single α a.val b.val c.val d.val hsum,
    fourPart_mask_pair α a.val b.val c.val d.val hsum _ _
      (fun he => (by decide : (0 : Fin 4) ≠ 1) (σ.injective he)),
    fourPart_mask_complement α a.val b.val c.val d.val hsum]
  simp only [actualCutBool, Bool.and_eq_true, decide_eq_true_eq]
  exact and_assoc.symm

/-- Equal actual inventories preserve the full four-part subset-mask count. -/
theorem fourPart_mask_count_invariant {N : ℕ} (α β : Composition N)
    (he : coarseningInventory α = coarseningInventory β) (a b c d : ℕ+)
    (hsum : a.val + b.val + c.val + d.val = N) :
    fourPartMaskCount (fourPartLeftCuts α a.val b.val c.val)
        (fourPartRightCuts α a.val b.val c.val) =
      fourPartMaskCount (fourPartLeftCuts β a.val b.val c.val)
        (fourPartRightCuts β a.val b.val c.val) := by
  rw [← labeled_fourPart_mask_count α a b c d hsum,
    ← labeled_fourPart_mask_count β a b c d hsum]
  apply labeledCoarseningOrders_card_invariant α β he
  change a.val + (b.val + (c.val + (d.val + 0))) = N
  omega

end SkewClassInflation
