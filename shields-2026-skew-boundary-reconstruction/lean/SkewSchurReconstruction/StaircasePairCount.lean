/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.StaircaseReversal

/-!
# Counting staircase reversal pairs

The binary-word counts following `prop:staircase-reversal` in “Reversal pairs
on the locus” (`subsec:locus-family`).  Words reverse by the actual
`TwoSeries.wordReverse`.  Palindromes are parametrized by their first half;
nonpalindromic pairs are an image of genuine two-element reversal orbits.
The fiber count proves exact divisibility and nonnegative subtraction.
Lengths zero and one are included.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- All interior binary words of length `M`. -/
abbrev BinaryWord (M : ℕ) := Fin M → Bool

/-- Exactly the binary words fixed by actual reversal. -/
noncomputable def palindromicWords (M : ℕ) : Finset (BinaryWord M) := by
  classical
  exact Finset.univ.filter (fun w => TwoSeries.wordReverse w = w)

/-- Exactly the words with distinct reversal. -/
noncomputable def nonpalindromicWords (M : ℕ) : Finset (BinaryWord M) := by
  classical
  exact Finset.univ.filter (fun w => TwoSeries.wordReverse w ≠ w)

/-- The unordered reversal pair associated with a word. -/
noncomputable def reversalWordPair {M : ℕ} (w : BinaryWord M) : Finset (BinaryWord M) := by
  classical
  exact {w, TwoSeries.wordReverse w}

/-- The actual set of unordered nonpalindromic reversal pairs. -/
noncomputable def nonpalindromicReversalPairs (M : ℕ) : Finset (Finset (BinaryWord M)) :=
  (nonpalindromicWords M).image reversalWordPair

private def palindromeFoldIndex {M : ℕ} (i : Fin M) : Fin ((M + 1) / 2) :=
  ⟨min i.val i.rev.val, by
    have hi := i.isLt
    simp only [Fin.val_rev]
    omega⟩

private theorem palindromeFoldIndex_rev {M : ℕ} (i : Fin M) :
    palindromeFoldIndex i.rev = palindromeFoldIndex i := by
  apply Fin.ext
  change min i.rev.val i.rev.rev.val = min i.val i.rev.val
  simp only [Fin.rev_rev, min_comm]

private def firstHalfIndex {M : ℕ} (i : Fin ((M + 1) / 2)) : Fin M :=
  ⟨i.val, by have hi := i.isLt; omega⟩

private theorem palindromeFoldIndex_firstHalf {M : ℕ} (i : Fin ((M + 1) / 2)) :
    palindromeFoldIndex (firstHalfIndex i) = i := by
  apply Fin.ext
  change min i.val (M - (i.val + 1)) = i.val
  have hi := i.isLt
  omega

private theorem firstHalf_fold_eq_or {M : ℕ} (i : Fin M) :
    firstHalfIndex (palindromeFoldIndex i) = i ∨
      firstHalfIndex (palindromeFoldIndex i) = i.rev := by
  by_cases hi : i.val ≤ i.rev.val
  · left
    apply Fin.ext
    change min i.val i.rev.val = i.val
    exact min_eq_left hi
  · right
    apply Fin.ext
    change min i.val i.rev.val = i.rev.val
    exact min_eq_right (le_of_not_ge hi)

/-- A palindrome is uniquely determined by its first ceiling-half word. -/
def palindromeHalfEquiv (M : ℕ) :
    BinaryWord ((M + 1) / 2) ≃ {w : BinaryWord M // TwoSeries.wordReverse w = w} where
  toFun h := ⟨fun i => h (palindromeFoldIndex i), by
    funext i
    change h (palindromeFoldIndex i.rev) = h (palindromeFoldIndex i)
    rw [palindromeFoldIndex_rev]⟩
  invFun w := fun i => w.val (firstHalfIndex i)
  left_inv h := by
    funext i
    change h (palindromeFoldIndex (firstHalfIndex i)) = h i
    rw [palindromeFoldIndex_firstHalf]
  right_inv w := by
    apply Subtype.ext
    funext i
    change w.val (firstHalfIndex (palindromeFoldIndex i)) = w.val i
    rcases firstHalf_fold_eq_or i with hi | hi
    · rw [hi]
    · rw [hi]
      exact congrFun w.property i

theorem binary_words_card (M : ℕ) :
    (Finset.univ : Finset (BinaryWord M)).card = 2 ^ M := by
  simp [BinaryWord]

theorem palindromic_words_card (M : ℕ) :
    (palindromicWords M).card = 2 ^ ((M + 1) / 2) := by
  classical
  have h := Fintype.card_congr (palindromeHalfEquiv M)
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_subtype, palindromicWords] using h.symm

/-- Palindrome and nonpalindrome cardinalities add to the total without truncation. -/
theorem reversal_word_partition_count (M : ℕ) :
    (palindromicWords M).card + (nonpalindromicWords M).card = 2 ^ M := by
  classical
  have h := (Finset.univ : Finset (BinaryWord M)).card_filter_add_card_filter_not
    (fun w => TwoSeries.wordReverse w = w)
  simpa only [palindromicWords, nonpalindromicWords, binary_words_card] using h

/-- In particular the subtraction in the orbit-count formula is nonnegative. -/
theorem palindromic_count_le_total (M : ℕ) : 2 ^ ((M + 1) / 2) ≤ 2 ^ M := by
  have h := reversal_word_partition_count M
  rw [palindromic_words_card] at h
  omega

theorem nonpalindromic_words_card (M : ℕ) :
    (nonpalindromicWords M).card = 2 ^ M - 2 ^ ((M + 1) / 2) := by
  have h := reversal_word_partition_count M
  rw [palindromic_words_card] at h
  omega

private theorem reversal_nonpalindromic {M : ℕ} {w : BinaryWord M}
    (hw : TwoSeries.wordReverse w ≠ w) :
    TwoSeries.wordReverse (TwoSeries.wordReverse w) ≠ TwoSeries.wordReverse w := by
  rw [TwoSeries.wordReverse_reverse]
  exact hw.symm

private theorem reversalWordPair_reverse {M : ℕ} (w : BinaryWord M) :
    reversalWordPair (TwoSeries.wordReverse w) = reversalWordPair w := by
  classical
  simp only [reversalWordPair, TwoSeries.wordReverse_reverse, Finset.pair_comm]

private theorem reversalWordPair_eq_iff {M : ℕ} (u w : BinaryWord M) :
    reversalWordPair u = reversalWordPair w ↔ u = w ∨ u = TwoSeries.wordReverse w := by
  classical
  constructor
  · intro he
    have hu : u ∈ reversalWordPair u := by simp [reversalWordPair]
    rw [he] at hu
    simpa only [reversalWordPair, Finset.mem_insert, Finset.mem_singleton] using hu
  · rintro (rfl | rfl)
    · rfl
    · exact reversalWordPair_reverse w

/-- Every image fiber over a nonpalindromic pair consists of exactly its two words. -/
theorem reversal_pair_fiber {M : ℕ} {w : BinaryWord M}
    (hw : w ∈ nonpalindromicWords M) :
    (nonpalindromicWords M).filter (fun u => reversalWordPair u = reversalWordPair w) =
      reversalWordPair w := by
  classical
  have hwne : TwoSeries.wordReverse w ≠ w := (Finset.mem_filter.mp hw).2
  have hwr : TwoSeries.wordReverse w ∈ nonpalindromicWords M :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, reversal_nonpalindromic hwne⟩
  apply Finset.ext
  intro u
  constructor
  · intro hu
    have he := (reversalWordPair_eq_iff u w).mp (Finset.mem_filter.mp hu).2
    simpa only [reversalWordPair, Finset.mem_insert, Finset.mem_singleton] using he
  · intro hu
    have he : u = w ∨ u = TwoSeries.wordReverse w := by
      simpa only [reversalWordPair, Finset.mem_insert, Finset.mem_singleton] using hu
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hw, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hwr, reversalWordPair_reverse w⟩

/-- Orbit fibers, not truncated division, prove that twice the pair count is exact. -/
theorem nonpalindromic_pairs_double_card (M : ℕ) :
    2 * (nonpalindromicReversalPairs M).card = (nonpalindromicWords M).card := by
  classical
  have hmap : Set.MapsTo (reversalWordPair : BinaryWord M → Finset (BinaryWord M))
      (nonpalindromicWords M : Set (BinaryWord M))
      (nonpalindromicReversalPairs M : Set (Finset (BinaryWord M))) := by
    intro w hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hc := Finset.card_eq_sum_card_fiberwise hmap
  have hf : ∀ p ∈ nonpalindromicReversalPairs M,
      ((nonpalindromicWords M).filter (fun w => reversalWordPair w = p)).card = 2 := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    rw [reversal_pair_fiber hw]
    have hne : TwoSeries.wordReverse w ≠ w := (Finset.mem_filter.mp hw).2
    simp [reversalWordPair, hne.symm]
  rw [Finset.sum_congr rfl hf] at hc
  simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] using hc.symm

/-- The numerator is an exact multiple of two, including zero and one letter. -/
theorem reversal_pair_numerator_even (M : ℕ) :
    2 ∣ 2 ^ M - 2 ^ ((M + 1) / 2) := by
  rw [← nonpalindromic_words_card, ← nonpalindromic_pairs_double_card]
  exact dvd_mul_right 2 _

/-- The exact count of unordered nonpalindromic reversal pairs. -/
theorem nonpalindromic_reversal_pairs_card (M : ℕ) :
    (nonpalindromicReversalPairs M).card =
      (2 ^ M - 2 ^ ((M + 1) / 2)) / 2 := by
  have h := nonpalindromic_pairs_double_card M
  rw [nonpalindromic_words_card] at h
  rw [← h]
  omega

/-- The natural staircase encoding preserves all binary words, hence these counts
are counts of genuine words in the staircase construction as well. -/
theorem binaryLength_injective (M : ℕ) : Function.Injective (@binaryLength M) := by
  intro x y he
  funext i
  have h := congrFun he i
  cases hx : x i <;> cases hy : y i <;> simp [binaryLength, hx, hy] at h ⊢

theorem staircase_binary_words_card (M : ℕ) :
    ((Finset.univ : Finset (BinaryWord M)).image binaryLength).card = 2 ^ M := by
  classical
  rw [Finset.card_image_of_injective _ (binaryLength_injective M), binary_words_card]

/-- Explicit boundary cases of the exact orbit count. -/
theorem reversal_pair_boundary_cases :
    (nonpalindromicReversalPairs 0).card = 0 ∧
      (nonpalindromicReversalPairs 1).card = 0 := by
  simp [nonpalindromic_reversal_pairs_card]

end SkewSchurReconstruction
