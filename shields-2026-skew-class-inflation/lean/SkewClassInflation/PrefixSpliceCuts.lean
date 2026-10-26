/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorWindowCounts

/-!
# Actual cuts retained by prefix and suffix splicing

The ordered window-comparison step for factor transport in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
These word identities track the actual retained boundaries, including
both boundaries adjacent to a new connecting part.  Sorry-free.
-/

namespace SkewClassInflation

/-- Every nonempty prefix of a proper initial segment ends at an original proper cut. -/
theorem prefixEnds_take_subset_cuts (w : List ℕ) (t : ℕ) (ht : t < w.length) :
    prefixEnds (w.take t) ⊆ wordProperCuts w := by
  intro x hx
  obtain ⟨s, hs0, hst, hsum⟩ := (prefixEnds_mem_partial (w.take t) x).mp hx
  have hst' : s ≤ t := by rw [List.length_take] at hst; omega
  refine (wordProperCuts_mem_partial w x).mpr ⟨s, hs0, by omega, ?_⟩
  rwa [List.take_take, Nat.min_eq_left hst'] at hsum

/-- Every proper cut of an initial segment is a proper cut of the original word. -/
theorem wordProperCuts_take_subset (w : List ℕ) (t : ℕ) :
    wordProperCuts (w.take t) ⊆ wordProperCuts w := by
  intro x hx
  obtain ⟨s, hs0, hst, hsum⟩ := (wordProperCuts_mem_partial (w.take t) x).mp hx
  have hs : s < w.length ∧ s ≤ t := by rw [List.length_take] at hst; omega
  refine (wordProperCuts_mem_partial w x).mpr ⟨s, hs0, hs.1, ?_⟩
  rwa [List.take_take, Nat.min_eq_left hs.2] at hsum

/-- Proper cuts in a suffix retain their original coordinates after its prefix sum is added. -/
theorem wordProperCuts_drop_translate (w : List ℕ) (t : ℕ) (x : ℕ)
    (hx : x ∈ wordProperCuts (w.drop t)) :
    (w.take t).sum + x ∈ wordProperCuts w := by
  obtain ⟨s, hs0, hslen, hsum⟩ := (wordProperCuts_mem_partial (w.drop t) x).mp hx
  have hlen : t + s < w.length := by rw [List.length_drop] at hslen; omega
  refine (wordProperCuts_mem_partial w _).mpr ⟨t + s, by omega, hlen, ?_⟩
  rw [List.take_add, List.sum_append, hsum]

/-- A positive-rank nonterminal prefix sum is itself an actual proper cut. -/
theorem take_sum_mem_wordProperCuts (w : List ℕ) (t : ℕ)
    (ht0 : 0 < t) (ht : t < w.length) : (w.take t).sum ∈ wordProperCuts w :=
  (wordProperCuts_mem_partial w _).mpr ⟨t, ht0, ht, rfl⟩

/-- Splicing two actual words keeps the initial prefix and the terminal suffix boundaries. -/
theorem word_splice_cuts_subset (u v : List ℕ) (t gap L J : ℕ)
    (ht0 : 0 < t) (htu : t < u.length) (htv : t < v.length)
    (hjoin : L + (u.take t).sum + gap = J + (v.take t).sum) :
    (wordProperCuts (u.take t ++ gap :: v.drop t)).image (fun x => L + x) ⊆
      (wordProperCuts u).image (fun x => L + x) ∪
        (wordProperCuts v).image (fun x => J + x) := by
  classical
  have hu : u.take t ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [List.length_take, List.length_nil] at hlen
    omega
  have hv : v.drop t ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [List.length_drop, List.length_nil] at hlen
    omega
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  rw [wordProperCuts_append _ _ hu (by simp), wordProperCuts_cons _ _ hv] at hy
  rcases Finset.mem_union.mp hy with hy | hy
  · apply Finset.mem_union.mpr ∘ Or.inl
    exact Finset.mem_image.mpr ⟨y, wordProperCuts_take_subset u t hy, rfl⟩
  · rcases Finset.mem_insert.mp hy with he | hy
    · apply Finset.mem_union.mpr ∘ Or.inl
      exact Finset.mem_image.mpr ⟨(u.take t).sum,
        take_sum_mem_wordProperCuts u t ht0 htu, by rw [he]⟩
    · obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hy
      rcases Finset.mem_insert.mp hz with hz | hz
      · apply Finset.mem_union.mpr ∘ Or.inr
        refine Finset.mem_image.mpr ⟨(v.take t).sum,
          take_sum_mem_wordProperCuts v t ht0 htv, ?_⟩
        rw [← he, hz]
        omega
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
        apply Finset.mem_union.mpr ∘ Or.inr
        refine Finset.mem_image.mpr ⟨(v.take t).sum + q,
          wordProperCuts_drop_translate v t q hq, ?_⟩
        rw [← he]
        omega

end SkewClassInflation
