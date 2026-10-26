/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LinearFactorSplitting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Integer root exponents of a split rational quotient

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Grouping repeated numerator and
denominator roots produces a finite set of nonzero integer exponents.

Sorry-free.
-/

namespace SkewCornerDescent

variable {k : Type*} [Field k] [DecidableEq k]

/-- Signed multiplicity of a root in a rational numerator and denominator. -/
noncomputable def splitRootExponent (p q : Polynomial k) (α : k) : ℤ :=
  (p.roots.count α : ℤ) - q.roots.count α

/-- Distinct active labels after all equal root occurrences have been cancelled. -/
noncomputable def splitActiveRoots (p q : Polynomial k) : Finset k :=
  (p.roots.toFinset ∪ q.roots.toFinset).filter fun α => splitRootExponent p q α ≠ 0

/-- Every active label has a nonzero signed exponent. -/
theorem splitActiveRoots_exponent_ne_zero (p q : Polynomial k) {α : k}
    (hα : α ∈ splitActiveRoots p q) : splitRootExponent p q α ≠ 0 :=
  (Finset.mem_filter.mp hα).2

/-- The finite active support contains exactly the labels with nonzero signed multiplicity. -/
theorem mem_splitActiveRoots_iff (p q : Polynomial k) (α : k) :
    α ∈ splitActiveRoots p q ↔ splitRootExponent p q α ≠ 0 := by
  constructor
  · exact splitActiveRoots_exponent_ne_zero p q
  · intro hα
    apply Finset.mem_filter.mpr
    refine ⟨?_, hα⟩
    by_contra hn
    have hp : α ∉ p.roots := by
      intro hp
      exact hn (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hp))
    have hq : α ∉ q.roots := by
      intro hq
      exact hn (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hq))
    exact hα (by simp only [splitRootExponent, Multiset.count_eq_zero_of_notMem hp,
      Multiset.count_eq_zero_of_notMem hq, Nat.cast_zero, sub_self])

/-- Summing root multiplicities over any containing set retains all repeated occurrences. -/
theorem sum_root_counts (p : Polynomial k) (s : Finset k) (hsub : p.roots.toFinset ⊆ s) :
    ∑ α ∈ s, (p.roots.count α : ℤ) = p.roots.card := by
  have hm := Finset.sum_multiset_map_count p.roots (fun _ => (1 : ℤ))
  change (p.roots.map (Function.const k (1 : ℤ))).sum = _ at hm
  simp only [Multiset.map_const, Multiset.sum_replicate, nsmul_eq_mul, mul_one] at hm
  rw [hm]
  symm
  apply Finset.sum_subset hsub
  intro α _ hα
  simp only [Multiset.mem_toFinset] at hα
  rw [Multiset.count_eq_zero_of_notMem hα, Nat.cast_zero]

/-- The sum of active integer exponents is exactly the numerator minus denominator degree. -/
theorem splitActiveRoots_sum (p q : Polynomial k) (hp : p.Splits) (hq : q.Splits) :
    ∑ α ∈ splitActiveRoots p q, splitRootExponent p q α =
      (p.natDegree : ℤ) - q.natDegree := by
  classical
  rw [splitActiveRoots, Finset.sum_filter]
  have hf (z : ℤ) : (if z ≠ 0 then z else 0) = z := by
    split_ifs with hz
    · rfl
    · simp only [ne_eq, not_not] at hz
      exact hz.symm
  simp only [hf]
  simp only [splitRootExponent]
  rw [Finset.sum_sub_distrib,
    sum_root_counts p _ Finset.subset_union_left,
    sum_root_counts q _ Finset.subset_union_right,
    ← hp.natDegree_eq_card_roots, ← hq.natDegree_eq_card_roots]

/-- Evaluation of a split polynomial groups full multiplicities on any containing label set. -/
theorem splitPolynomial_eval_grouped {E : Type*} [Field E] [Algebra k E]
    (x : E) (p : Polynomial k) (hp : p.Splits) (s : Finset k)
    (hsub : p.roots.toFinset ⊆ s) :
    Polynomial.aeval x p = algebraMap k E p.leadingCoeff *
      ∏ α ∈ s, (x - algebraMap k E α) ^ p.roots.count α := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [map_mul, Polynomial.aeval_C, map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [Finset.prod_multiset_map_count]
  congr 1
  apply Finset.prod_subset hsub
  intro α _ hα
  simp only [Multiset.mem_toFinset] at hα
  rw [Multiset.count_eq_zero_of_notMem hα, pow_zero]

/-- Split rational quotients have the exact finite active-label integer-power factorization. -/
theorem splitRational_eval_factorization {E : Type*} [Field E] [Algebra k E]
    (x : E) (p q : Polynomial k) (hp : p.Splits) (hq : q.Splits)
    (hx : ∀ α : k, x ≠ algebraMap k E α) :
    Polynomial.aeval x p / Polynomial.aeval x q =
      algebraMap k E (p.leadingCoeff / q.leadingCoeff) *
        ∏ α ∈ splitActiveRoots p q, (x - algebraMap k E α) ^ splitRootExponent p q α := by
  classical
  let s := p.roots.toFinset ∪ q.roots.toFinset
  rw [splitPolynomial_eval_grouped x p hp s Finset.subset_union_left,
    splitPolynomial_eval_grouped x q hq s Finset.subset_union_right,
    mul_div_mul_comm, ← map_div₀, ← Finset.prod_div_distrib]
  congr 1
  have hg : ∀ α ∈ s, (x - algebraMap k E α) ^ p.roots.count α /
      (x - algebraMap k E α) ^ q.roots.count α =
        (x - algebraMap k E α) ^ splitRootExponent p q α := by
    intro α _
    rw [splitRootExponent, zpow_sub₀ (sub_ne_zero.mpr (hx α)), zpow_natCast, zpow_natCast]
  rw [Finset.prod_congr rfl hg]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro α hsα hα
  have he : splitRootExponent p q α = 0 := by
    by_contra hn
    exact hα (Finset.mem_filter.mpr ⟨hsα, hn⟩)
  rw [he, zpow_zero]

end SkewCornerDescent
