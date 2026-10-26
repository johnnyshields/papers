/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkMaximal
import SkewClassInflation.ThinMarkHats
import SkewClassInflation.ThinMarkRemovals

/-!
# Legal literal inflation marks below the exact threshold

Hypotheses I--IV and the case-(a) well-formed chart in
`lem:subthreshold-transport` of
`shields-2026-skew-class-inflation.tex`.  The positive marks and the
horizontal empty-mark convention are both assembled from actual cell
sets and their proved geometric properties.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- The southwest and northeast cells are the literal extreme endpoints of the inner. -/
theorem innerCells_extremes (t : ℕ) :
    sw (B.innerCells t) = (1, 0) ∧
      ne (B.innerCells t) = (0, (B.boundary.q : ℤ) + t - 2) := by
  have hq := B.boundary_q_eq
  have ha := B.c_lt_a
  have hb := B.a_lt_b
  have hc := B.c_pos
  have hsw : (1, 0) ∈ B.innerCells t := by
    rw [B.mem_innerCells]
    right
    exact ⟨rfl, le_rfl, by omega⟩
  have hne : (0, (B.boundary.q : ℤ) + t - 2) ∈ B.innerCells t := by
    rw [B.mem_innerCells]
    left
    exact ⟨rfl, by omega, by omega⟩
  have hmin : minContent (B.innerCells t) = -1 := by
    apply minContent_eq_of
    · simpa [content] using content_mem_contents hsw
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      rw [B.mem_innerCells] at hi
      rcases hi with hi | hi <;> omega
  have hmax : maxContent (B.innerCells t) = (B.boundary.q : ℤ) + t - 2 := by
    apply maxContent_eq_of
    · simpa only [content, sub_zero] using content_mem_contents hne
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      rw [B.mem_innerCells] at hi
      rcases hi with hi | hi <;> omega
  have hdmin : diagLo (B.innerCells t) (-1) = 1 := by
    apply diagLo_eq_of
    · simpa using hsw
    · intro i hi
      rw [B.mem_innerCells] at hi
      rcases hi with hi | hi <;> omega
  have hdmax : diagLo (B.innerCells t) ((B.boundary.q : ℤ) + t - 2) = 0 := by
    apply diagLo_eq_of
    · simpa only [zero_add] using hne
    · intro i hi
      rw [B.mem_innerCells] at hi
      rcases hi with hi | hi <;> omega
  constructor
  · rw [sw, hmin, hdmin]
    norm_num
  · rw [ne, hmax, hdmax, zero_add]

/-- Both specified nonempty placements and their actual horizontal attachments are well formed. -/
theorem inflationMark_nonempty (t : ℕ) (ht : 0 < t) (htp : t < B.boundary.p) :
    (B.inflationMark t).IsNonemptyMark := by
  refine ⟨?_, lowerMark_connected t ht, (B.inflationMark_subsets t).1,
    (B.inflationMark_subsets t).2, ?_, ?_, ?_⟩
  · refine ⟨(1, 0), ?_⟩
    change (1, 0) ∈ lowerMark t
    rw [mem_lowerMark]
    exact ⟨rfl, le_rfl, by omega⟩
  · change sw (B.innerCells t) ∈ lowerMark t
    rw [(B.innerCells_extremes t).1, mem_lowerMark]
    exact ⟨rfl, le_rfl, by omega⟩
  · change ne (B.innerCells t) ∈ (B.inflationMark t).upper
    rw [(B.innerCells_extremes t).2, B.mem_upperMark]
    exact ⟨rfl, by omega, by omega⟩
  · refine ⟨fun _ => ⟨B.inflationMark_lowerH t ht htp, B.inflationMark_upperH t ht htp⟩,
      ?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- At zero width the specified displacement is the horizontal empty-overlap displacement. -/
theorem inflationMark_empty : (B.inflationMark 0).IsEmptyMark := by
  refine ⟨?_, ?_, rfl⟩
  · change translate (1, 0) (rowCells 0 (0 : ℕ)) = ∅
    simp only [rowCells, Nat.cast_zero, Finset.Ico_self, Finset.image_empty]
    change (∅ : Finset (ℤ × ℤ)).image (fun x => x + (1, 0)) = ∅
    simp only [Finset.image_empty]
  · change (-1, (B.boundary.q : ℤ) - 1) = vH (B.innerCells 0)
    rw [vH, (B.innerCells_extremes 0).1, (B.innerCells_extremes 0).2]
    ext <;> simp
    ring

/-- Every strict subthreshold literal marked inner is well formed, including width zero. -/
theorem inflationMark_wellformed (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).IsWellFormed := by
  refine ⟨B.innerCells_connected t, ?_⟩
  by_cases ht0 : t = 0
  · subst t
    exact Or.inl B.inflationMark_empty
  · exact Or.inr (B.inflationMark_nonempty t (by omega) ht)

/-- The actual chart satisfies all four legality hypotheses below the exact threshold. -/
theorem inflationMark_legal (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).IsLegal :=
  ⟨B.inflationMark_wellformed t ht, B.inflationMark_maximal t ht,
    B.inflationMark_narrow t ht, B.inflationMark_removals_connected t ht,
    B.inflationMark_noHatAdjacency t ht⟩

end SkewClassInflation.ThinParameters
