/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkedCells

/-!
# Geometry of the actual two-row marks and middle

The mark-width, separation, and middle-strip inputs to
`lem:subthreshold-transport` in
`shields-2026-skew-class-inflation.tex`.  Every set is the literal
cell realization, not an assumed legal chart.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- The lower mark has exactly its actual horizontal width, including the empty mark. -/
theorem lowerMark_span (t : ℕ) : span (lowerMark t) = t := by
  rw [lowerMark, span_translate, span_rowCells, sub_zero, Int.toNat_natCast]

/-- The actual mark width is the specified integer inflation parameter. -/
theorem inflationMark_width (t : ℕ) : (B.inflationMark t).width = t := lowerMark_span t

/-- The actual translation has period `q`, independently of the mark width. -/
theorem inflationMark_period (t : ℕ) : (B.inflationMark t).period = B.boundary.q := by
  simp [MarkedInner.period, inflationMark, content]

/-- Both literal marked placements are subsets of the actual inner cell set. -/
theorem inflationMark_subsets (t : ℕ) :
    (B.inflationMark t).W ⊆ (B.inflationMark t).E ∧
      (B.inflationMark t).upper ⊆ (B.inflationMark t).E := by
  have hq := B.boundary_q_eq
  have ha := B.c_lt_a
  have hb := B.a_lt_b
  have hc := B.c_pos
  constructor
  · rintro ⟨i, j⟩ hx
    change (i, j) ∈ lowerMark t at hx
    change (i, j) ∈ B.innerCells t
    rw [mem_lowerMark] at hx
    apply (B.mem_innerCells t i j).mpr
    right
    exact ⟨hx.1, hx.2.1, by omega⟩
  · rintro ⟨i, j⟩ hx
    rw [B.mem_upperMark] at hx
    change (i, j) ∈ B.innerCells t
    apply (B.mem_innerCells t i j).mpr
    left
    exact ⟨hx.1, by omega, hx.2.2⟩

/-- A positive lower mark is a genuine connected skew row, with its actual placement retained. -/
theorem lowerMark_connected (t : ℕ) (ht : 0 < t) : IsConnectedSkew (lowerMark t) := by
  exact isConnectedSkew_translate _ (isConnectedSkew_rowCells (by omega))

/-- Hypothesis II holds below the exact boundary. -/
theorem inflationMark_narrow (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).IsNarrow := by
  rw [MarkedInner.IsNarrow, B.inflationMark_width, B.inflationMark_period]
  have hq := B.boundary.ap_lt_q
  omega

/-- Removing both literal marks leaves exactly these two row intervals. -/
theorem mem_inflation_middle (t : ℕ) (i j : ℤ) :
    (i, j) ∈ (B.inflationMark t).middle ↔
      (i = 0 ∧ (B.b : ℤ) - B.c - 1 ≤ j ∧ j < (B.boundary.q : ℤ) - 1) ∨
      (i = 1 ∧ (t : ℤ) ≤ j ∧ j < (B.b : ℤ) + t) := by
  have hq := B.boundary_q_eq
  have hc := B.c_lt_a
  have hb := B.a_lt_b
  simp only [MarkedInner.middle, Finset.mem_sdiff, Finset.mem_union]
  change ((i, j) ∈ B.innerCells t ∧
    ¬ ((i, j) ∈ lowerMark t ∨ (i, j) ∈ (B.inflationMark t).upper)) ↔ _
  rw [B.mem_innerCells, mem_lowerMark, B.mem_upperMark]
  omega

/-- The southwest middle cell has its sole marked horizontal predecessor. -/
theorem inflationMark_lowerH (t : ℕ) (ht : 0 < t) (htp : t < B.boundary.p) :
    (B.inflationMark t).LowerH := by
  have hq := B.boundary_q_eq
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    have := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hab := B.a_lt_b
  have hc := B.c_pos
  have hx : (1, (t : ℤ)) ∈ (B.inflationMark t).middle := by
    rw [B.mem_inflation_middle]
    right
    exact ⟨rfl, le_rfl, by omega⟩
  have hm : minContent (B.inflationMark t).middle = (t : ℤ) - 1 := by
    apply minContent_eq_of
    · exact mem_contents_iff.mpr ⟨1, by simpa only [add_sub_cancel] using hx⟩
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      rw [B.mem_inflation_middle] at hi
      rcases hi with hi | hi <;> omega
  refine ⟨(1, (t : ℤ)), hx, ?_, ?_⟩
  · rw [hm]
    rfl
  · change (1, (t : ℤ) - 1) ∈ lowerMark t
    rw [mem_lowerMark]
    exact ⟨rfl, by omega, by omega⟩

/-- The northeast middle cell has its sole marked horizontal successor. -/
theorem inflationMark_upperH (t : ℕ) (ht : 0 < t) (htp : t < B.boundary.p) :
    (B.inflationMark t).UpperH := by
  have hq := B.boundary_q_eq
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    have := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hab := B.a_lt_b
  have hc := B.c_pos
  have hx : (0, (B.boundary.q : ℤ) - 2) ∈ (B.inflationMark t).middle := by
    rw [B.mem_inflation_middle]
    left
    exact ⟨rfl, by omega, by omega⟩
  have hm : maxContent (B.inflationMark t).middle = (B.boundary.q : ℤ) - 2 := by
    apply maxContent_eq_of
    · exact mem_contents_iff.mpr ⟨0, by simpa only [zero_add] using hx⟩
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      rw [B.mem_inflation_middle] at hi
      rcases hi with hi | hi <;> omega
  refine ⟨(0, (B.boundary.q : ℤ) - 2), hx, ?_, ?_⟩
  · rw [hm]
    simp [content]
  · rw [B.mem_upperMark]
    exact ⟨rfl, by omega, by omega⟩

end SkewClassInflation.ThinParameters
