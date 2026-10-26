/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.LargePartOrders

/-!
# Actual prefix coordinates around an inserted larger part

The cut-coordinate calculation for inner-inventory extraction in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
An insertion adds no coordinate shift before its position and exactly
the inserted weight after it.  Sorry-free.
-/

namespace SkewClassInflation

/-- Insertion changes the actual length by one at every valid insertion rank. -/
theorem insertLargePart_length (w : List ℕ) (q k : ℕ) (hk : k ≤ w.length) :
    (insertLargePart w q k).length = w.length + 1 := by
  simp only [insertLargePart, List.length_append, List.length_take,
    List.length_cons, List.length_drop]
  omega

/-- Every prefix ending before the inserted part is the original prefix. -/
theorem take_insertLargePart_of_le (w : List ℕ) (q k s : ℕ)
    (hk : k ≤ w.length) (hs : s ≤ k) :
    (insertLargePart w q k).take s = w.take s := by
  rw [insertLargePart, List.take_append_of_le_length (by rw [List.length_take]; omega),
    List.take_take, Nat.min_eq_left hs]

/-- Every prefix ending after the inserted part has precisely its weight added. -/
theorem take_insertLargePart_sum_of_gt (w : List ℕ) (q k s : ℕ)
    (hk : k ≤ w.length) (hs : k < s) :
    ((insertLargePart w q k).take s).sum = q + (w.take (s - 1)).sum := by
  have hlen : (w.take k).length = k := by rw [List.length_take, Nat.min_eq_left hk]
  rw [insertLargePart, List.take_append, hlen]
  have ht : min s k = k := Nat.min_eq_right (by omega)
  rw [List.take_take, ht]
  have he : s - k = (s - k - 1) + 1 := by omega
  rw [he, List.take_succ_cons, List.sum_append, List.sum_cons]
  have hparts : w.take (s - 1) = w.take k ++ (w.drop k).take (s - k - 1) := by
    have hi : s - 1 = k + (s - k - 1) := by omega
    rw [hi, List.take_add]
  rw [hparts, List.sum_append]
  omega

/-- An internal inserted part leaves every proper cut at an original cut or its shifted copy. -/
theorem insertLargePart_internal_cut_origin (w : List ℕ) (q k x : ℕ)
    (hk0 : 0 < k) (hk : k < w.length) (hx : x ∈ wordProperCuts (insertLargePart w q k)) :
    ∃ y ∈ wordProperCuts w, x = y ∨ x = q + y := by
  obtain ⟨s, hs0, hslen, hsum⟩ := (wordProperCuts_mem_partial _ x).mp hx
  rw [insertLargePart_length w q k hk.le] at hslen
  by_cases hs : s ≤ k
  · rw [take_insertLargePart_of_le w q k s hk.le hs] at hsum
    exact ⟨x, (wordProperCuts_mem_partial w x).mpr ⟨s, hs0, by omega, hsum⟩, Or.inl rfl⟩
  · rw [take_insertLargePart_sum_of_gt w q k s hk.le (by omega)] at hsum
    exact ⟨(w.take (s - 1)).sum,
      (wordProperCuts_mem_partial w _).mpr ⟨s - 1, by omega, by omega, rfl⟩,
      Or.inr hsum.symm⟩

/-- Every original proper cut survives in at least one of the two coordinate ranges. -/
theorem insertLargePart_cut_lift (w : List ℕ) (q k y : ℕ) (hk : k ≤ w.length)
    (hy : y ∈ wordProperCuts w) :
    ∃ x ∈ wordProperCuts (insertLargePart w q k), x = y ∨ x = q + y := by
  obtain ⟨s, hs0, hslen, hsum⟩ := (wordProperCuts_mem_partial w y).mp hy
  by_cases hs : s ≤ k
  · refine ⟨y, (wordProperCuts_mem_partial _ _).mpr ⟨s, hs0, ?_, ?_⟩, Or.inl rfl⟩
    · rw [insertLargePart_length w q k hk]
      omega
    · rw [take_insertLargePart_of_le w q k s hk hs]
      exact hsum
  · refine ⟨q + y, (wordProperCuts_mem_partial _ _).mpr ⟨s + 1, by omega, ?_, ?_⟩,
      Or.inr rfl⟩
    · rw [insertLargePart_length w q k hk]
      omega
    · rw [take_insertLargePart_sum_of_gt w q k (s + 1) hk (by omega),
        Nat.add_sub_cancel, hsum]

end SkewClassInflation
