/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkBasics

/-!
# Connected skew complements after either literal mark is removed

Hypothesis III for the chart in `lem:subthreshold-transport` of
`shields-2026-skew-class-inflation.tex`.  Each complement is identified
with the cells of an explicitly valid two-row profile, at its actual
translation.  The strict boundary inequality supplies its overlap
validity.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

/-- Removing the lower mark shortens only the lower row. -/
def removedLowerProfile (t : ℕ) (ht : t < B.boundary.p) : Profile 1 where
  r := ![B.a + t, B.b]
  g _ := B.c + t
  r_pos i := by
    have := B.c_pos
    have := B.c_lt_a
    have := B.a_lt_b
    fin_cases i <;> dsimp <;> omega
  g_lt_castSucc j := by
    have := B.c_lt_a
    fin_cases j
    change B.c + t < B.a + t
    omega
  g_lt_succ j := by
    have := B.c_lt_a
    have := B.a_lt_b
    change t < B.a - B.c at ht
    fin_cases j
    change B.c + t < B.b
    omega

/-- Removing the upper mark shortens only the upper row. -/
def removedUpperProfile (t : ℕ) (ht : t < B.boundary.p) : Profile 1 where
  r := ![B.a, B.b + t]
  g _ := B.c + t
  r_pos i := by
    have := B.c_pos
    have := B.c_lt_a
    have := B.a_lt_b
    fin_cases i <;> dsimp <;> omega
  g_lt_castSucc j := by
    have := B.c_lt_a
    change t < B.a - B.c at ht
    fin_cases j
    change B.c + t < B.a
    omega
  g_lt_succ j := by
    have := B.c_lt_a
    have := B.a_lt_b
    fin_cases j
    change B.c + t < B.b + t
    omega

/-- The lower-mark complement is exactly a translated valid shortened-row diagram. -/
theorem lower_mark_removal_cells (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).E \ (B.inflationMark t).W =
      translate (0, (t : ℤ) - 1) (profileCells (B.removedLowerProfile t ht)) := by
  have hq := B.boundary_q_eq
  ext ⟨i, j⟩
  rw [Finset.mem_sdiff]
  change ((i, j) ∈ B.innerCells t ∧ (i, j) ∉ lowerMark t) ↔ _
  rw [B.mem_innerCells, mem_lowerMark, mem_translate]
  have he : (i, j) - (0, (t : ℤ) - 1) = (i, j - ((t : ℤ) - 1)) := by ext <;> simp
  rw [he, mem_twoRow_profileCells]
  dsimp only [removedLowerProfile]
  push_cast
  omega

/-- The upper-mark complement is exactly a translated valid shortened-row diagram. -/
theorem upper_mark_removal_cells (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).E \ (B.inflationMark t).upper =
      translate (0, -1) (profileCells (B.removedUpperProfile t ht)) := by
  have hq := B.boundary_q_eq
  ext ⟨i, j⟩
  rw [Finset.mem_sdiff]
  change ((i, j) ∈ B.innerCells t ∧ (i, j) ∉ (B.inflationMark t).upper) ↔ _
  rw [B.mem_innerCells, B.mem_upperMark, mem_translate]
  have he : (i, j) - (0, -1) = (i, j + 1) := by ext <;> simp
  rw [he, mem_twoRow_profileCells]
  dsimp only [removedUpperProfile]
  push_cast
  omega

/-- Hypothesis III holds for both actual complements throughout the strict subthreshold domain. -/
theorem inflationMark_removals_connected (t : ℕ) (ht : t < B.boundary.p) :
    (B.inflationMark t).RemovalsConnected := by
  constructor
  · rw [B.lower_mark_removal_cells t ht]
    exact isConnectedSkew_translate _ (profileCells_connected _)
  · rw [B.upper_mark_removal_cells t ht]
    exact isConnectedSkew_translate _ (profileCells_connected _)

end SkewClassInflation.ThinParameters
