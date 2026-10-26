/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.LocalAlternative
import SkewRibbonCoarsenings.Labels

/-!
# Weights at most four in the local alternative

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:realization`
(`prop:local-alternative`, `prop:budget`: weights at most four).

At weights `n ≤ 4`, two-block data fix every symmetric cut pair and the midpoint, with at most one
asymmetric reflected pair left, whose two orientations are global reversals; weight one has a single
composition.  Concretely: two cut sets of weight `n ≤ 4` are identical, reversed, or distinguished
by a partition with at most two parts.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

/-- The partitions into two parts used at weight `n ≤ 4`. -/
def smallCands : ℕ → List (Multiset ℕ)
  | 2 => [{1, 1}]
  | 3 => [{1, 2}]
  | 4 => [{1, 3}, {2, 2}]
  | _ => []

theorem small_decide :
    ∀ n ∈ ({0, 1, 2, 3, 4} : Finset ℕ), ∀ S ∈ (Finset.Ioo 0 n).powerset,
      ∀ S' ∈ (Finset.Ioo 0 n).powerset,
        S' = S ∨ S' = revCuts n S ∨ ∃ lam ∈ smallCands n, mult n S lam ≠ mult n S' lam := by
  decide +kernel

theorem small_facts : ∀ m ∈ ({2, 3, 4} : Finset ℕ), ∀ lam ∈ smallCands m,
    (∀ x ∈ lam, 0 < x) ∧ lam.sum = m ∧ Multiset.card lam ≤ 2 ∧ kappa lam ≤ 2 := by
  decide +kernel

theorem small_mult : ∀ m ∈ ({2, 3, 4} : Finset ℕ), ∀ lam ∈ smallCands m,
    ∀ S ∈ (Finset.Ioo 0 m).powerset, mult m S lam ≤ 2 := by
  decide +kernel

/-- `prop:local-alternative`, weights at most four (and `prop:budget`): for `n ≤ 4` and any budget
with `2 ≤ H n` when `2 ≤ n` and `1 ≤ H n` when `n = 1`, the alternative holds with
the first, second or last case only. -/
theorem small_alternative {H : ℕ → ℕ} {n : ℕ} (hn : n ≤ 4) (hH2 : 2 ≤ n → 2 ≤ H n)
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    S' = S ∨ S' = revCuts n S ∨ ∃ lam : Multiset ℕ, CoarseCertificate H n S S' lam := by
  have hmem : n ∈ ({0, 1, 2, 3, 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  rcases small_decide n hmem S (Finset.mem_powerset.mpr hS) S' (Finset.mem_powerset.mpr hS') with
    h | h | ⟨lam, hl, hne⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    refine ⟨lam, ?_⟩
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> simp [smallCands] at hl
    have hm : n ∈ ({2, 3, 4} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    obtain ⟨h1, h2, h3, h4⟩ := small_facts n hm lam hl
    have a1 := small_mult n hm lam hl S (Finset.mem_powerset.mpr hS)
    have a2 := small_mult n hm lam hl S' (Finset.mem_powerset.mpr hS')
    refine ⟨h1, h2, h3.trans (hH2 hn2), ?_, distinctExceptPair_of_kappa_le_two h4⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

end SkewRibbonCoarsenings
