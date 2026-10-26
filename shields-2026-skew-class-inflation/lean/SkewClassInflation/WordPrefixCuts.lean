/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionCuts
import SkewClassInflation.SuffixWords

/-!
# Prefix cuts of literal positive words

The word-to-boundary bridge used in `eq:overlap-cut-set` and
`eq:ribbon-composition` of `shields-2026-skew-class-inflation.tex`.
The prefix inventory includes the terminal sum, so appending a final
part turns it into the exact proper cut set.  Sorry-free.
-/

namespace SkewClassInflation

/-- All nonempty prefix sums, including the complete word's sum. -/
def prefixEnds : List ℕ → Finset ℕ
  | [] => ∅
  | a :: l => insert a ((prefixEnds l).image (fun x => a + x))

/-- Prefix endpoints distribute over literal word concatenation. -/
theorem prefixEnds_append (u v : List ℕ) :
    prefixEnds (u ++ v) = prefixEnds u ∪ (prefixEnds v).image (fun x => u.sum + x) := by
  classical
  induction u with
  | nil => simp [prefixEnds]
  | cons a u ih =>
    simp only [List.cons_append, prefixEnds, ih, Finset.image_union,
      Finset.image_image, List.sum_cons]
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Function.comp_apply]
    constructor
    · rintro (rfl | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨y, hy, rfl⟩)
      · exact Or.inr ⟨y, hy, by omega⟩
    · rintro ((rfl | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
      · exact Or.inr (Or.inr ⟨y, hy, by omega⟩)

/-- Changing only the first part translates every nonempty prefix sum equally. -/
theorem prefixEnds_head_add (a d : ℕ) (l : List ℕ) :
    prefixEnds ((a + d) :: l) = (prefixEnds (a :: l)).image (fun x => d + x) := by
  classical
  simp only [prefixEnds, Finset.image_insert, Finset.image_image]
  congr 1
  · omega
  · apply Finset.image_congr
    intro x hx
    dsimp only [Function.comp_apply]
    omega

/-- The terminal part contributes no proper cut; all preceding nonempty prefixes do. -/
theorem wordSuffixSet_reverse_append_single (u : List ℕ) (b : ℕ) :
    wordSuffixSet (u ++ [b]).reverse = prefixEnds u := by
  classical
  induction u with
  | nil => simp [prefixEnds, wordSuffixSet]
  | cons a u ih =>
    rw [List.cons_append]
    have he : wordSuffixSet (a :: (u ++ [b])).reverse =
        insert a ((wordSuffixSet (u ++ [b]).reverse).image (fun x => a + x)) := by
      ext x
      simp only [wordSuffixSet, List.reverse_reverse, List.length_reverse,
        List.length_cons, List.length_append,
        Finset.mem_image, Finset.mem_Ico, Finset.mem_insert]
      constructor
      · rintro ⟨i, ⟨hi0, hiL⟩, hi⟩
        cases i with
        | zero => omega
        | succ i =>
          rw [List.take_succ_cons, List.sum_cons] at hi
          by_cases hiz : i = 0
          · subst i
            simp only [List.take_zero, List.sum_nil, add_zero] at hi
            exact Or.inl hi.symm
          · exact Or.inr ⟨(List.take i (u ++ [b])).sum,
              ⟨i, ⟨by omega, by omega⟩, rfl⟩, hi⟩
      · rintro (rfl | ⟨y, ⟨i, ⟨hi0, hiL⟩, hi⟩, rfl⟩)
        · exact ⟨1, ⟨by omega, by omega⟩, by simp⟩
        · refine ⟨i + 1, ⟨by omega, by omega⟩, ?_⟩
          rw [List.take_succ_cons, List.sum_cons, hi]
    rw [he, ih, prefixEnds]

/-- The prefix recursion computes the actual proper cuts of a composition. -/
theorem properCuts_blocks_append_single {N : ℕ} (α : Composition N)
    (u : List ℕ) (b : ℕ) (he : α.blocks = u ++ [b]) :
    properCuts α = prefixEnds u := by
  rw [properCuts_eq_suffixSet, ← wordSuffixSet_blocks,
    Composition.reverse_blocks, he, wordSuffixSet_reverse_append_single]

/-- With positive parts, every recorded endpoint is positive and at most the total sum. -/
theorem prefixEnds_bounds (u : List ℕ) (hu : ∀ a ∈ u, 0 < a) :
    ∀ x ∈ prefixEnds u, 0 < x ∧ x ≤ u.sum := by
  induction u with
  | nil => simp [prefixEnds]
  | cons a u ih =>
    intro x hx
    have ha := hu a List.mem_cons_self
    have ht : ∀ b ∈ u, 0 < b := fun b hb => hu b (List.mem_cons_of_mem _ hb)
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp only [List.sum_cons]
      omega
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hh := ih ht y hy
      simp only [List.sum_cons]
      omega

end SkewClassInflation
