/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Defs

/-!
# The characteristic-two boundary: the weight-seventeen pair

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:recognition`
(`subsec:parity`, `prop:parity`).

The compositions `U₁₇ = (1,1,1,1,1,1,1,1,9)` and `V₁₇ = (1,1,2,4,2,1,1,2,3)` have the same
coarsening multiplicities modulo two in every block count at most three, but different
coarsening polynomials.  Everything is a finite computation on the two cut sets.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

/-- Cut set of `U₁₇ = (1,1,1,1,1,1,1,1,9)`. -/
def cutsU17 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8}

/-- Cut set of `V₁₇ = (1,1,2,4,2,1,1,2,3)`. -/
def cutsV17 : Finset ℕ := {1, 2, 4, 8, 10, 11, 12, 14}

/-- `prop:parity`, cut sets: the displayed cut sets are the prefix sums of `U₁₇` and `V₁₇`. -/
theorem parity_cuts :
    cutsU17 = (List.range 8).toFinset.image (fun i => i + 1) ∧
    cutsV17 = {1, 1 + 1, 1 + 1 + 2, 1 + 1 + 2 + 4, 1 + 1 + 2 + 4 + 2, 1 + 1 + 2 + 4 + 2 + 1,
      1 + 1 + 2 + 4 + 2 + 1 + 1, 1 + 1 + 2 + 4 + 2 + 1 + 1 + 2} ∧
    IsCutSet 17 cutsU17 ∧ IsCutSet 17 cutsV17 := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> unfold IsCutSet <;> decide

/-- `prop:parity`, reflected pairs: both cut sets contain exactly one point of every reflected
pair `{x, 17 - x}` modulo `17`. -/
theorem parity_one_of_each_pair :
    (∀ x ∈ Finset.Ioo 0 17, (x ∈ cutsU17 ↔ 17 - x ∉ cutsU17)) ∧
    (∀ x ∈ Finset.Ioo 0 17, (x ∈ cutsV17 ↔ 17 - x ∉ cutsV17)) := by
  refine ⟨by decide, by decide⟩

/-- `prop:parity`, disagreement set: the symmetric difference of the cut sets is
`{3,5,6,7,10,11,12,14}`, which is one complete doubling-negation orbit `x ↦ -2x` modulo `17`. -/
theorem parity_disagreement :
    symmDiff cutsU17 cutsV17 = {3, 5, 6, 7, 10, 11, 12, 14} ∧
    symmDiff cutsU17 cutsV17 =
      (Finset.range 8).image (fun k : ℕ => (((-2 : ZMod 17) ^ k * 3 : ZMod 17)).val) := by
  refine ⟨by decide, by decide⟩

/-- The coarsening multiplicity vanishes off the block lists of retained subsets. -/
theorem mult_eq_zero_of_notMem (n : ℕ) (S : Finset ℕ) (lam : Multiset ℕ)
    (h : lam ∉ S.powerset.image (gaps n)) : mult n S lam = 0 := by
  unfold mult
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro T hT hg
  exact h (Finset.mem_image.2 ⟨T, hT, hg⟩)

/-- The finite check behind `prop:parity`: for every block list of a retained subset of either
cut set with at most three blocks, the two multiplicities agree modulo two. -/
theorem parity_congruence_finite :
    ∀ lam ∈ ((cutsU17.powerset.image (gaps 17)) ∪ (cutsV17.powerset.image (gaps 17))).filter
        (fun l => Multiset.card l ≤ 3),
      mult 17 cutsU17 lam % 2 = mult 17 cutsV17 lam % 2 := by
  decide +kernel

/-- `prop:parity`, congruence: `G_{U₁₇}^{[≤3]} ≡ G_{V₁₇}^{[≤3]} (mod 2)`, as equality modulo two
of the multiplicities of every partition with at most three parts. -/
theorem parity_congruence (lam : Multiset ℕ) (hl : Multiset.card lam ≤ 3) :
    mult 17 cutsU17 lam % 2 = mult 17 cutsV17 lam % 2 := by
  by_cases h : lam ∈ (cutsU17.powerset.image (gaps 17)) ∪ (cutsV17.powerset.image (gaps 17))
  · exact parity_congruence_finite lam (Finset.mem_filter.2 ⟨h, hl⟩)
  · rw [Finset.mem_union, not_or] at h
    rw [mult_eq_zero_of_notMem 17 _ _ h.1, mult_eq_zero_of_notMem 17 _ _ h.2]

/-- `prop:parity`, coefficients at `(14,2,1)`: two and zero. -/
theorem parity_coeff_14_2_1 :
    mult 17 cutsU17 {14, 2, 1} = 2 ∧ mult 17 cutsV17 {14, 2, 1} = 0 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- `prop:parity`, coefficients at `(14,1,1,1)`: one and zero. -/
theorem parity_coeff_14_1_1_1 :
    mult 17 cutsU17 {14, 1, 1, 1} = 1 ∧ mult 17 cutsV17 {14, 1, 1, 1} = 0 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- Evaluation `h_j ↦ j + 1` on `Λ_ℤ`; it sends `h₀ = 1` to `1` as well. -/
noncomputable def evalSucc : Lam →+* ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun j : ℕ+ => ((j : ℕ) : ℤ) + 1)

theorem evalSucc_hgen (j : ℕ) : evalSucc (hgen j) = (j : ℤ) + 1 := by
  unfold hgen
  split_ifs with h
  · exact MvPolynomial.eval₂_X (RingHom.id ℤ) (fun j : ℕ+ => ((j : ℕ) : ℤ) + 1) (⟨j, h⟩ : ℕ+)
  · have : j = 0 := by omega
    subst this
    simp

theorem evalSucc_G (n : ℕ) (S : Finset ℕ) :
    evalSucc (G n S) =
      ∑ T ∈ S.powerset, (Multiset.map (fun g : ℕ => (g : ℤ) + 1) (gaps n T)).prod := by
  unfold G
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun g _ => evalSucc_hgen g

/-- `prop:parity`, distinct inventories: `G_{U₁₇} ≠ G_{V₁₇}`, separated by the evaluation
`h_j ↦ j + 1` (the values are `164128` and `334032`). -/
theorem parity_G_ne : G 17 cutsU17 ≠ G 17 cutsV17 := by
  intro h
  have h2 := congrArg evalSucc h
  rw [evalSucc_G, evalSucc_G] at h2
  revert h2
  decide +kernel

/-- `prop:parity`: the statement of the paper's proposition in one place. -/
theorem parity_weight_seventeen :
    (∀ lam : Multiset ℕ, Multiset.card lam ≤ 3 →
      mult 17 cutsU17 lam % 2 = mult 17 cutsV17 lam % 2) ∧
    G 17 cutsU17 ≠ G 17 cutsV17 ∧
    (mult 17 cutsU17 {14, 2, 1} = 2 ∧ mult 17 cutsV17 {14, 2, 1} = 0) ∧
    (mult 17 cutsU17 {14, 1, 1, 1} = 1 ∧ mult 17 cutsV17 {14, 1, 1, 1} = 0) :=
  ⟨parity_congruence, parity_G_ne, parity_coeff_14_2_1, parity_coeff_14_1_1_1⟩

end SkewRibbonCoarsenings
