/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.LargePartPrefixes

/-!
# Retained cuts of an inserted whole-weight larger part

The inner-inventory extraction step in factor transport for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
At an internal insertion rank, both sides of the larger part read the
same actual inner cut set.  Sorry-free.
-/

namespace SkewClassInflation

/-- Every proper coordinate inside an actual product copy reads its original inner cut. -/
theorem compositionProduct_copy_cut {M N : ℕ} (δ : Composition M) (ε : Composition N)
    (i x : ℕ) (hi : i < M) (hx : 0 < x) (hxN : x < N) :
    i * N + x ∈ properCuts (compositionProduct δ ε) ↔ x ∈ properCuts ε := by
  have hh := compositionWindow_cuts (compositionProduct δ ε) N i x hx hxN
  rw [compositionWindow_compositionProduct δ ε i hi] at hh
  exact hh.symm

/-- Inserting the larger whole-weight part internally preserves exactly the inner coarsenings. -/
theorem insertLargePart_internal_retained_iff {M N : ℕ}
    (δ : Composition M) (ε : Composition N) (hM : 2 ≤ M)
    (w : List ℕ) (hsum : w.sum = N) (hpos : ∀ a ∈ w, 0 < a)
    (k : ℕ) (hk0 : 0 < k) (hk : k < w.length) :
    wordProperCuts (insertLargePart w ((M - 1) * N) k) ⊆
        properCuts (compositionProduct δ ε) ↔ wordProperCuts w ⊆ properCuts ε := by
  have hbound : ∀ y ∈ wordProperCuts w, 0 < y ∧ y < N := by
    intro y hy
    simpa only [hsum] using wordProperCuts_bounds w hpos y hy
  have hfirst (y : ℕ) (hy : y ∈ wordProperCuts w) :
      y ∈ properCuts (compositionProduct δ ε) ↔ y ∈ properCuts ε := by
    have hb := hbound y hy
    simpa only [zero_mul, zero_add] using
      compositionProduct_copy_cut δ ε 0 y (by omega) hb.1 hb.2
  have hlast (y : ℕ) (hy : y ∈ wordProperCuts w) :
      (M - 1) * N + y ∈ properCuts (compositionProduct δ ε) ↔ y ∈ properCuts ε := by
    have hb := hbound y hy
    exact compositionProduct_copy_cut δ ε (M - 1) y (by omega) hb.1 hb.2
  constructor
  · intro hs y hy
    obtain ⟨x, hx, he | he⟩ := insertLargePart_cut_lift w ((M - 1) * N) k y hk.le hy
    · have hc := hs hx
      rw [he] at hc
      exact (hfirst y hy).mp hc
    · have hc := hs hx
      rw [he] at hc
      exact (hlast y hy).mp hc
  · intro hs x hx
    obtain ⟨y, hy, he | he⟩ :=
      insertLargePart_internal_cut_origin w ((M - 1) * N) k x hk0 hk hx
    · rw [he]
      exact (hfirst y hy).mpr (hs hy)
    · rw [he]
      exact (hlast y hy).mpr (hs hy)

/-- All nonempty prefix endpoints consist of the actual proper cuts and the full sum. -/
theorem prefixEnds_eq_insert_sum (w : List ℕ) (hne : w ≠ []) :
    prefixEnds w = insert w.sum (wordProperCuts w) := by
  rw [← wordProperCuts_append_single w 0,
    wordProperCuts_append w [0] hne (by simp), wordProperCuts_single,
    Finset.image_empty]
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
  exact or_comm

/-- Actual whole-inner cut coordinates read exactly the corresponding outer cuts. -/
theorem compositionProduct_multiple_cut {M N : ℕ} (δ : Composition M) (ε : Composition N)
    (hN : 0 < N) (j : ℕ) (hj0 : 0 < j) (hj : j < M) :
    j * N ∈ properCuts (compositionProduct δ ε) ↔ j ∈ properCuts δ := by
  rw [compositionProduct_cuts δ ε (j * N) (Nat.mul_pos hj0 hN)
    (Nat.mul_lt_mul_of_pos_right hj hN), Nat.mul_mod_left, ite_eq_left rfl,
    Nat.mul_div_cancel j hN]

/-- A leading larger part is permitted precisely by the last outer cut. -/
theorem insertLargePart_first_retained_iff {M N : ℕ}
    (δ : Composition M) (ε : Composition N) (hM : 2 ≤ M) (hN : 0 < N)
    (w : List ℕ) (hsum : w.sum = N) (hpos : ∀ a ∈ w, 0 < a) :
    wordProperCuts (insertLargePart w ((M - 1) * N) 0) ⊆
        properCuts (compositionProduct δ ε) ↔
      M - 1 ∈ properCuts δ ∧ wordProperCuts w ⊆ properCuts ε := by
  have hne : w ≠ [] := by intro he; rw [he, List.sum_nil] at hsum; omega
  have hstart : insertLargePart w ((M - 1) * N) 0 = ((M - 1) * N) :: w := by
    simp only [insertLargePart, List.take_zero, List.drop_zero, List.nil_append]
  rw [hstart, wordProperCuts_cons _ w hne, Finset.insert_subset_iff,
    compositionProduct_multiple_cut δ ε hN (M - 1) (by omega) (by omega)]
  apply and_congr_right
  intro _
  rw [Finset.image_subset_iff]
  constructor <;> intro hs x hx
  · have hb := wordProperCuts_bounds w hpos x hx
    rw [hsum] at hb
    exact (compositionProduct_copy_cut δ ε (M - 1) x (by omega) hb.1 hb.2).mp (hs x hx)
  · have hb := wordProperCuts_bounds w hpos x hx
    rw [hsum] at hb
    exact (compositionProduct_copy_cut δ ε (M - 1) x (by omega) hb.1 hb.2).mpr (hs hx)

/-- A terminal larger part is permitted precisely by the first outer cut. -/
theorem insertLargePart_last_retained_iff {M N : ℕ}
    (δ : Composition M) (ε : Composition N) (hM : 2 ≤ M) (hN : 0 < N)
    (w : List ℕ) (hsum : w.sum = N) (hpos : ∀ a ∈ w, 0 < a) :
    wordProperCuts (insertLargePart w ((M - 1) * N) w.length) ⊆
        properCuts (compositionProduct δ ε) ↔
      1 ∈ properCuts δ ∧ wordProperCuts w ⊆ properCuts ε := by
  have hne : w ≠ [] := by intro he; rw [he, List.sum_nil] at hsum; omega
  have hend : insertLargePart w ((M - 1) * N) w.length = w ++ [(M - 1) * N] := by
    simp only [insertLargePart, List.take_length, List.drop_length]
  rw [hend, wordProperCuts_append_single, prefixEnds_eq_insert_sum w hne,
    hsum, Finset.insert_subset_iff]
  have hboundary := compositionProduct_multiple_cut δ ε hN 1 (by omega) (by omega)
  simp only [one_mul] at hboundary
  rw [hboundary]
  apply and_congr_right
  intro _
  constructor <;> intro hs x hx
  · have hb := wordProperCuts_bounds w hpos x hx
    rw [hsum] at hb
    have hc := compositionProduct_copy_cut δ ε 0 x (by omega) hb.1 hb.2
    simp only [zero_mul, zero_add] at hc
    exact hc.mp (hs hx)
  · have hb := wordProperCuts_bounds w hpos x hx
    rw [hsum] at hb
    have hc := compositionProduct_copy_cut δ ε 0 x (by omega) hb.1 hb.2
    simp only [zero_mul, zero_add] at hc
    exact hc.mpr (hs hx)

end SkewClassInflation
