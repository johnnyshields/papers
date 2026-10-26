/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionSuffixes

/-!
# Proper suffix sets along an ordered word

Formalizes the literal suffix-sum convention in `eq:suffix-set` of
`shields-2026-skew-class-inflation.tex`.  The Mathlib composition boundary
encoding is identified with the partial sums of the reversed row word,
then with its head-tail recursion.  Sorry-free.
-/

namespace SkewClassInflation

/-- Proper suffix sums, directly as partial sums of the reversed finite block word. -/
def wordSuffixSet (l : List ℕ) : Finset ℕ :=
  (Finset.Ico 1 l.length).image (fun i => (l.reverse.take i).sum)

/-- Every proper suffix is exactly one nonterminal boundary of the reversed composition. -/
theorem suffixSet_mem_partial {M : ℕ} (α : Composition M) (k : ℕ) :
    k ∈ suffixSet α ↔ ∃ i, 0 < i ∧ i < α.length ∧ (α.reverse.blocks.take i).sum = k := by
  have hlen : α.reverse.length = α.length := by simp [Composition.length, Composition.reverse]
  constructor
  · intro hk
    obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
    have hjM := (Finset.mem_erase.mp hj).1
    have hj0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hb := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hb
    change α.reverse.boundary i = j at hi
    have hval : (α.reverse.blocks.take i.val).sum = j.val := congrArg Fin.val hi
    have hi0 : i ≠ 0 := by
      intro h
      rw [h, Composition.boundary_zero] at hi
      exact hj0 hi.symm
    have hiM : i ≠ Fin.last α.reverse.length := by
      intro h
      rw [h, Composition.boundary_last] at hi
      exact hjM hi.symm
    have hi0' : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
    have hiM' : i.val < α.reverse.length := by
      have hi := i.isLt
      have hh : i.val ≠ α.reverse.length := fun h => hiM (Fin.ext h)
      omega
    exact ⟨i.val, hi0', by omega, hval.trans hjk⟩
  · rintro ⟨i, hi0, hiM, hik⟩
    let t : Fin (α.reverse.length + 1) := ⟨i, by omega⟩
    let j := α.reverse.boundary t
    have hj0 : j ≠ 0 := by
      intro h
      have hi := α.reverse.boundary.injective (h.trans α.reverse.boundary_zero.symm)
      have hiv := congrArg Fin.val hi
      change i = 0 at hiv
      omega
    have hjM : j ≠ Fin.last M := by
      intro h
      have hi := α.reverse.boundary.injective (h.trans α.reverse.boundary_last.symm)
      have hiv := congrArg Fin.val hi
      change i = α.reverse.length at hiv
      omega
    have hj : j.val ∈ suffixSet α := (suffixSet_mem_iff α j hj0 hjM).mpr
      (Finset.mem_map.mpr ⟨t, Finset.mem_univ _, rfl⟩)
    have hjk : j.val = k := hik
    exact hjk ▸ hj

/-- Direct finite word suffix sums agree with the actual composition suffix set. -/
theorem wordSuffixSet_blocks {M : ℕ} (α : Composition M) :
    wordSuffixSet α.blocks = suffixSet α := by
  ext k
  simp only [wordSuffixSet, Finset.mem_image, Finset.mem_Ico, suffixSet_mem_partial,
    Composition.reverse_blocks, Composition.length]
  constructor
  · rintro ⟨i, ⟨hi0, hiM⟩, hi⟩
    exact ⟨i, hi0, hiM, hi⟩
  · rintro ⟨i, hi0, hiM, hi⟩
    exact ⟨i, ⟨hi0, hiM⟩, hi⟩

/-- A singleton word has no proper suffix sum. -/
theorem wordSuffixSet_single (a : ℕ) : wordSuffixSet [a] = ∅ := by simp [wordSuffixSet]

/-- Prepending a block adds the old whole-word sum as the one new proper suffix boundary. -/
theorem wordSuffixSet_cons (a : ℕ) (l : List ℕ) (hl : l ≠ []) :
    wordSuffixSet (a :: l) = insert l.sum (wordSuffixSet l) := by
  classical
  have hlen : 0 < l.length := List.length_pos_iff.mpr hl
  ext k
  simp only [wordSuffixSet, Finset.mem_image, Finset.mem_Ico, List.length_cons,
    Finset.mem_insert]
  have ht (i : ℕ) (hi : i ≤ l.length) : ((a :: l).reverse.take i).sum = (l.reverse.take i).sum := by
    simp [List.reverse_cons, List.take_append, List.length_reverse, Nat.sub_eq_zero_of_le hi]
  have hall : (l.reverse.take l.length).sum = l.sum := by
    rw [List.take_of_length_le (by simp), List.sum_reverse]
  constructor
  · rintro ⟨i, ⟨hi0, hiM⟩, hik⟩
    by_cases hi : i = l.length
    · left
      rw [ht i (by omega), hi] at hik
      rw [hall] at hik
      exact hik.symm
    · right
      exact ⟨i, ⟨hi0, by omega⟩, (ht i (by omega)).symm.trans hik⟩
  · rintro (hk | ⟨i, ⟨hi0, hiM⟩, hik⟩)
    · refine ⟨l.length, ⟨hlen, by omega⟩, ?_⟩
      rw [ht _ le_rfl]
      rw [hall]
      exact hk.symm
    · exact ⟨i, ⟨hi0, by omega⟩, (ht i (by omega)).trans hik⟩

end SkewClassInflation
