/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.WordNearConcatenation
import SkewClassInflation.WordPrefixCuts

/-!
# Nonzero residue words and their actual prefix cuts

The modular coarsening input to factor-reversal generation in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Zero residues may repeat an existing prefix position but never create
an additional positive prefix position.  Sorry-free.
-/

namespace SkewClassInflation

/-- Deleting zero natural parts preserves the actual whole-word sum. -/
theorem nonzero_filter_sum (w : List ℕ) :
    (w.filter (fun x => decide (x ≠ 0))).sum = w.sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    by_cases ha : a = 0
    · subst a
      rw [List.filter_cons_of_neg (by decide)]
      simpa only [List.sum_cons, zero_add] using ih
    · rw [List.filter_cons_of_pos (by simp only [ha, ne_eq, not_false_eq_true, decide_true])]
      simp only [List.sum_cons, ih]

/-- The prefix recursion lists precisely the nonempty prefix sums, including the full sum. -/
theorem prefixEnds_mem_partial (w : List ℕ) (x : ℕ) :
    x ∈ prefixEnds w ↔ ∃ i : ℕ, 0 < i ∧ i ≤ w.length ∧ (w.take i).sum = x := by
  have he : wordProperCuts (w ++ [0]) = prefixEnds w :=
    wordSuffixSet_reverse_append_single w 0
  rw [← he, wordProperCuts_mem_partial]
  constructor
  · rintro ⟨i, hi, hlen, hsum⟩
    have hilen : i ≤ w.length := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have ht : (w ++ [0]).take i = w.take i := List.take_append_of_le_length hilen
    exact ⟨i, hi, hilen, by rwa [ht] at hsum⟩
  · rintro ⟨i, hi, hlen, hsum⟩
    refine ⟨i, hi, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    rw [List.take_append_of_le_length hlen]
    exact hsum

/-- Below the terminal sum, recorded prefix endpoints are exactly the actual proper cuts. -/
theorem wordProperCuts_prefixEnds_of_lt (w : List ℕ) (x : ℕ) (hx : x < w.sum) :
    x ∈ wordProperCuts w ↔ x ∈ prefixEnds w := by
  rw [wordProperCuts_mem_partial, prefixEnds_mem_partial]
  constructor
  · rintro ⟨i, hi, hlen, hsum⟩
    exact ⟨i, hi, hlen.le, hsum⟩
  · rintro ⟨i, hi, hlen, hsum⟩
    refine ⟨i, hi, ?_, hsum⟩
    by_contra he
    have hieq : i = w.length := by omega
    rw [hieq, List.take_length] at hsum
    omega

/-- Filtering zero parts deletes exactly the possible zero prefix endpoint. -/
theorem prefixEnds_filter_nonzero (w : List ℕ) :
    prefixEnds (w.filter (fun x => decide (x ≠ 0))) = (prefixEnds w).erase 0 := by
  induction w with
  | nil => simp only [List.filter_nil, prefixEnds, Finset.erase_empty]
  | cons a w ih =>
    by_cases ha : a = 0
    · subst a
      rw [List.filter_cons_of_neg (by decide), ih]
      simp only [prefixEnds, zero_add, Finset.image_id', Finset.erase_insert_eq_erase]
    · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
      have hbool : decide (a ≠ 0) = true := by simp only [ha, ne_eq, not_false_eq_true, decide_true]
      rw [List.filter_cons_of_pos (p := fun x : ℕ => decide (x ≠ 0)) hbool]
      simp only [prefixEnds, ih]
      ext y
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨x, ⟨hx0, hx⟩, he⟩)
        · exact ⟨ha, Or.inl rfl⟩
        · exact ⟨by omega, Or.inr ⟨x, hx, he⟩⟩
      · rintro ⟨hy0, he | ⟨x, hx, he⟩⟩
        · exact Or.inl he
        · by_cases hx0 : x = 0
          · left
            omega
          · exact Or.inr ⟨x, ⟨hx0, hx⟩, he⟩

/-- Summing actual part residues preserves the residue of the whole original sum. -/
theorem sum_mod_map (w : List ℕ) (m : ℕ) :
    ((w.map (fun x => x % m)).sum) % m = w.sum % m := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mod, Nat.mod_mod, ih]

/-- The actual positive residue word obtained by deleting precisely the zero residues. -/
def residueWord (w : List ℕ) (m : ℕ) : List ℕ :=
  (w.map (fun x => x % m)).filter (fun x => decide (x ≠ 0))

/-- Every actual part retained in the residue word is positive. -/
theorem residueWord_pos (w : List ℕ) (m : ℕ) : ∀ x ∈ residueWord w m, 0 < x := by
  intro x hx
  have hh := (List.mem_filter.mp hx).2
  exact Nat.pos_of_ne_zero (of_decide_eq_true hh)

/-- Its actual weight is exactly the unfiltered sum of the part residues. -/
theorem residueWord_sum (w : List ℕ) (m : ℕ) :
    (residueWord w m).sum = (w.map (fun x => x % m)).sum :=
  nonzero_filter_sum _

end SkewClassInflation
