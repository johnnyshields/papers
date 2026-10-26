/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorWindowPeriodicity
import SkewClassInflation.PartitionOrderCounts

/-!
# Scaling actual coarsening words and their proper cuts

The outer-inventory recovery step in factor transport for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Multiplication of all positive parts scales every retained boundary by
the same positive inner weight.  Sorry-free.
-/

namespace SkewClassInflation

/-- Multiplication scales the sum of every actual finite natural word. -/
theorem sum_map_mul_right (w : List ℕ) (n : ℕ) :
    (w.map (fun x => x * n)).sum = w.sum * n := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

/-- The actual proper prefix coordinates scale with the literal word. -/
theorem wordProperCuts_map_mul (w : List ℕ) (n : ℕ) :
    wordProperCuts (w.map (fun x => x * n)) =
      (wordProperCuts w).image (fun x => x * n) := by
  ext x
  rw [wordProperCuts_mem_partial]
  simp only [Finset.mem_image, wordProperCuts_mem_partial, List.length_map]
  constructor
  · rintro ⟨i, hi0, hil, hs⟩
    refine ⟨(w.take i).sum, ⟨i, hi0, hil, rfl⟩, ?_⟩
    rw [← List.map_take, sum_map_mul_right] at hs
    exact hs
  · rintro ⟨y, ⟨i, hi0, hil, hs⟩, he⟩
    refine ⟨i, hi0, hil, ?_⟩
    rw [← List.map_take, sum_map_mul_right, hs, he]

/-- A scaled positive part, with its actual positivity proof. -/
def scalePositivePart (n : ℕ) (hn : 0 < n) (a : ℕ+) : ℕ+ :=
  ⟨a.val * n, Nat.mul_pos a.pos hn⟩

/-- Positive-part scaling and natural-word scaling have the same actual values. -/
theorem scalePositivePart_values (l : List ℕ+) (n : ℕ) (hn : 0 < n) :
    (l.map (scalePositivePart n hn)).map PNat.val =
      (l.map PNat.val).map (fun x => x * n) := by
  simp only [List.map_map, Function.comp_def, scalePositivePart]
  rfl

/-- Every order of a scaled partition is a scaled order of the original partition. -/
theorem partitionOrders_scale (l : List ℕ+) (n : ℕ) (hn : 0 < n) :
    partitionOrders (l.map (scalePositivePart n hn)) =
      (partitionOrders l).image (fun w => w.map (fun x => x * n)) := by
  rw [partitionOrders, scalePositivePart_values, ← List.map_permutations]
  ext w
  simp only [partitionOrders, List.mem_toFinset, List.mem_map, Finset.mem_image]

/-- Sampling the actual whole-inner cut coordinates preserves precisely the scaled word cuts. -/
theorem scaled_word_cuts_subset_iff {M N : ℕ} (θ : Composition (M * N))
    (w : List ℕ) (hsum : w.sum = M)
    (hpos : ∀ a ∈ w, 0 < a) :
    wordProperCuts (w.map (fun x => x * N)) ⊆ properCuts θ ↔
      wordProperCuts w ⊆ properCuts (periodicOuter θ) := by
  rw [wordProperCuts_map_mul]
  constructor
  · intro hs x hx
    have hb := wordProperCuts_bounds w hpos x hx
    have hxM : x < M := by simpa only [hsum] using hb.2
    have hc := hs (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    rw [periodicOuter, compositionFromCuts_internal _ _ x hb.1 hxM]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hb.1, hxM⟩, hc⟩
  · intro hs x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hc := hs hy
    have hb := properCuts_bounds (periodicOuter θ) y hc
    rw [periodicOuter, compositionFromCuts_internal _ _ y hb.1 hb.2] at hc
    exact (Finset.mem_filter.mp hc).2

end SkewClassInflation
