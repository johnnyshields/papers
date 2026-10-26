/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CoarseningTwoParts

/-!
# Reconstruction when no reflected cut has a single orientation

The symmetric-cut case of the ribbon classification input to
`lem:overlap-power-rigidity` of `shields-2026-skew-class-inflation.tex`.
Exact two-part multiplicities determine every original cut when its
reflection is always present or absent with it.  The source inventory
also supplies total weight equality.  Sorry-free.
-/

namespace SkewClassInflation

/-- A reflection-symmetric proper cut set is completely determined by its coarsening inventory. -/
theorem symmetric_cuts_reconstruct {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hsym : ∀ x, 0 < x → x < ∑ i, r i →
      (x ∈ properCuts (rowComposition r hr) ↔
        (∑ i, r i) - x ∈ properCuts (rowComposition r hr)))
    (he : coarseningPartitions r hr = coarseningPartitions s hs) :
    List.ofFn r = List.ofFn s := by
  classical
  have hweight := coarseningPartitions_row_sum r s hr hs he
  have hcuts : properCuts (rowComposition r hr) = properCuts (rowComposition s hs) := by
    ext x
    by_cases hx : 0 < x ∧ x < ∑ i, r i
    · let a : ℕ+ := ⟨x, hx.1⟩
      let b : ℕ+ := ⟨(∑ i, r i) - x, Nat.sub_pos_of_lt hx.2⟩
      have hR : a.val + b.val = ∑ i, r i := Nat.add_sub_of_le hx.2.le
      have hS : a.val + b.val = ∑ i, s i := hR.trans hweight
      have ht := reflected_cut_type_of_coarsening_eq r s hr hs a b hR hS he
      change (if x ∈ properCuts (rowComposition r hr) then 1 else 0) +
          (if (∑ i, r i) - x ∈ properCuts (rowComposition r hr) then 1 else 0) =
        (if x ∈ properCuts (rowComposition s hs) then 1 else 0) +
          (if (∑ i, r i) - x ∈ properCuts (rowComposition s hs) then 1 else 0) at ht
      have href := hsym x hx.1 hx.2
      by_cases hp : x ∈ properCuts (rowComposition r hr)
      · have hpr := href.mp hp
        by_cases hq : x ∈ properCuts (rowComposition s hs)
        · exact iff_of_true hp hq
        · simp only [ite_eq_left hp, ite_eq_left hpr, ite_eq_right hq] at ht
          split_ifs at ht <;> omega
      · have hpr : (∑ i, r i) - x ∉ properCuts (rowComposition r hr) :=
          fun h => hp (href.mpr h)
        by_cases hq : x ∈ properCuts (rowComposition s hs)
        · simp only [ite_eq_right hp, ite_eq_right hpr, ite_eq_left hq] at ht
          split_ifs at ht <;> omega
        · exact iff_of_false hp hq
    · constructor <;> intro hm
      · exact (hx (properCuts_bounds _ x hm)).elim
      · have hb := properCuts_bounds (rowComposition s hs) x hm
        rw [← hweight] at hb
        exact (hx hb).elim
  have hc : rowComposition r hr = (rowComposition s hs).cast hweight.symm := by
    apply properCuts_injective
    rw [properCuts_cast]
    exact hcuts
  exact congrArg Composition.blocks hc

/-- The same reconstruction applies directly to actual equal ribbon functions. -/
theorem ribbon_eq_reconstruct_of_symmetric_cuts {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hsym : ∀ x, 0 < x → x < ∑ i, r i →
      (x ∈ properCuts (rowComposition r hr) ↔
        (∑ i, r i) - x ∈ properCuts (rowComposition r hr)))
    (he : ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s)) :
    List.ofFn r = List.ofFn s :=
  symmetric_cuts_reconstruct r s hr hs hsym
    ((ribbon_eq_iff_coarseningPartitions r s hr hs).mp he)

/-- A genuinely reversal-symmetric source word has no other ordered ribbon mate. -/
theorem ribbon_eq_reconstruct_of_reverse_word {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hrev : (List.ofFn r).reverse = List.ofFn r)
    (he : ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s)) :
    List.ofFn r = List.ofFn s := by
  apply ribbon_eq_reconstruct_of_symmetric_cuts r s hr hs ?_ he
  intro x hx hxN
  simp only [← wordProperCuts_blocks (rowComposition r hr)]
  change (x ∈ wordProperCuts (List.ofFn r)) ↔
    (∑ i, r i) - x ∈ wordProperCuts (List.ofFn r)
  have hh := wordProperCuts_reverse_reflect (List.ofFn r) x
    (by rw [List.sum_ofFn]; exact hxN.le)
  rw [hrev] at hh
  simpa only [List.sum_ofFn] using hh

end SkewClassInflation
