/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.LargePartRetention

/-!
# Exact admissible insertion ranks for the larger part

The multiplicity factor in inner-inventory extraction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Both endpoint positions are counted separately even when the two outer
boundary tests coincide.  Sorry-free.
-/

namespace SkewClassInflation

/-- The two endpoint tests and every internal insertion rank. -/
def largePartRanks {M : ℕ} (δ : Composition M) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (k + 1)).filter (fun i =>
    if i = 0 then M - 1 ∈ properCuts δ else if i = k then 1 ∈ properCuts δ else True)

/-- Admissible ranks have exactly their stated endpoint tests and actual rank bounds. -/
theorem mem_largePartRanks {M : ℕ} (δ : Composition M) (k i : ℕ) :
    i ∈ largePartRanks δ k ↔ i ≤ k ∧
      (if i = 0 then M - 1 ∈ properCuts δ else if i = k then 1 ∈ properCuts δ else True) := by
  classical
  simp only [largePartRanks, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The exact rank count includes both midpoint endpoint occurrences, without collapsing them. -/
theorem largePartRanks_card {M : ℕ} (δ : Composition M) (k : ℕ) (hk : 0 < k) :
    (largePartRanks δ k).card = k - 1 + compositionCutType δ 1 := by
  classical
  let good := fun i =>
    if i = 0 then M - 1 ∈ properCuts δ else if i = k then 1 ∈ properCuts δ else True
  have hfirst : (if good 0 then (1 : ℕ) else 0) =
      if M - 1 ∈ properCuts δ then 1 else 0 := by simp only [good, ite_true]
  have hlast : (if good k then (1 : ℕ) else 0) =
      if 1 ∈ properCuts δ then 1 else 0 := by
    simp only [good, Nat.ne_of_gt hk, ite_false, ite_true]
  have hmiddle : ∀ i ∈ Finset.range (k - 1), (if good (i + 1) then (1 : ℕ) else 0) = 1 := by
    intro i hi
    have hb := Finset.mem_range.mp hi
    have h0 : i + 1 ≠ 0 := by omega
    have hk' : i + 1 ≠ k := by omega
    simp only [good, h0, hk', ite_false, ite_true]
  have he : k = (k - 1) + 1 := by omega
  have hsum : (∑ i ∈ Finset.range k, if good i then (1 : ℕ) else 0) =
      k - 1 + (if M - 1 ∈ properCuts δ then 1 else 0) := by
    have hh := Finset.sum_range_succ' (fun i => if good i then (1 : ℕ) else 0) (k - 1)
    have ht := congrArg (fun n => ∑ i ∈ Finset.range n, if good i then (1 : ℕ) else 0) he
    rw [ht, hh]
    rw [hfirst]
    have hm : (∑ i ∈ Finset.range (k - 1), if good (i + 1) then (1 : ℕ) else 0) = k - 1 := by
      rw [Finset.sum_congr rfl hmiddle]
      simp
    rw [hm]
  change ((Finset.range (k + 1)).filter good).card = _
  rw [Finset.card_filter, Finset.sum_range_succ, hsum, hlast]
  simp only [compositionCutType]
  omega

/-- Retained larger-part orders are the inner retained orders at the admissible ranks. -/
theorem insertLargePart_retained_iff {M N : ℕ}
    (δ : Composition M) (ε : Composition N) (hM : 2 ≤ M) (hN : 0 < N)
    (w : List ℕ) (hsum : w.sum = N) (hpos : ∀ a ∈ w, 0 < a)
    (hlen : 0 < w.length) (i : ℕ) (hi : i ≤ w.length) :
    wordProperCuts (insertLargePart w ((M - 1) * N) i) ⊆
        properCuts (compositionProduct δ ε) ↔
      wordProperCuts w ⊆ properCuts ε ∧ i ∈ largePartRanks δ w.length := by
  rw [mem_largePartRanks]
  by_cases hi0 : i = 0
  · subst i
    rw [insertLargePart_first_retained_iff δ ε hM hN w hsum hpos]
    simp only [ite_true, hi, true_and]
    exact and_comm
  · by_cases hil : i = w.length
    · subst i
      rw [insertLargePart_last_retained_iff δ ε hM hN w hsum hpos]
      simp only [Nat.ne_of_gt hlen, ite_false, ite_true, le_refl, true_and]
      exact and_comm
    · rw [insertLargePart_internal_retained_iff δ ε hM w hsum hpos i
        (by omega) (by omega)]
      simp only [hi0, hil, ite_false, hi, and_true]

end SkewClassInflation
