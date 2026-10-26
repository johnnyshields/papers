/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMarkLegality

/-!
# Unique cells attaching the literal marks to the middle

Hypothesis V for the chart in `lem:subthreshold-transport` of
`shields-2026-skew-class-inflation.tex`.  The finite sets of marked
cells adjacent to the actual middle are computed exactly, not merely
shown nonempty.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing

namespace ThinParameters

variable (B : ThinParameters)

/-- Exactly the last southwest marked cell touches the middle. -/
theorem lower_attachmentCells (t : ℕ) (ht : 0 < t) (htp : t < B.boundary.p) :
    attachmentCells (B.inflationMark t).W (B.inflationMark t).middle =
      {(1, (t : ℤ) - 1)} := by
  have hq := B.boundary_q_eq
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    have := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hab := B.a_lt_b
  have hc := B.c_pos
  ext ⟨i, j⟩
  rw [attachmentCells, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  change ((i, j) ∈ lowerMark t ∧ ∃ y ∈ (B.inflationMark t).middle, CellAdj (i, j) y) ↔ _
  rw [mem_lowerMark]
  constructor
  · rintro ⟨hW, ⟨⟨r, s⟩, hM, hadj⟩⟩
    rw [B.mem_inflation_middle] at hM
    rw [cellAdj_iff] at hadj
    rcases hM with hM | hM <;> omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨rfl, by omega, by omega⟩, (1, (t : ℤ)), ?_, ?_⟩
    · rw [B.mem_inflation_middle]
      right
      exact ⟨rfl, le_rfl, by omega⟩
    · rw [cellAdj_iff]
      left
      exact ⟨rfl, Or.inr (by dsimp; omega)⟩

/-- Exactly the first northeast marked cell touches the middle. -/
theorem upper_attachmentCells (t : ℕ) (ht : 0 < t) (htp : t < B.boundary.p) :
    attachmentCells (B.inflationMark t).upper (B.inflationMark t).middle =
      {(0, (B.boundary.q : ℤ) - 1)} := by
  have hq := B.boundary_q_eq
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    have := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hab := B.a_lt_b
  have hc := B.c_pos
  ext ⟨i, j⟩
  rw [attachmentCells, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq,
    B.mem_upperMark]
  constructor
  · rintro ⟨hW, ⟨⟨r, s⟩, hM, hadj⟩⟩
    rw [B.mem_inflation_middle] at hM
    rw [cellAdj_iff] at hadj
    rcases hM with hM | hM <;> omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨rfl, le_rfl, by omega⟩, (0, (B.boundary.q : ℤ) - 2), ?_, ?_⟩
    · rw [B.mem_inflation_middle]
      left
      exact ⟨rfl, by omega, by omega⟩
    · rw [cellAdj_iff]
      left
      exact ⟨rfl, Or.inl (by dsimp; omega)⟩

/-- Hypothesis V counts exactly one attaching cell in each literal marked placement. -/
theorem inflationMark_hypothesisV (t : ℕ) (ht : 0 < t) (htp : t < B.boundary.p) :
    (attachmentCells (B.inflationMark t).W (B.inflationMark t).middle).card = 1 ∧
      (attachmentCells (B.inflationMark t).upper (B.inflationMark t).middle).card = 1 := by
  rw [B.lower_attachmentCells t ht htp, B.upper_attachmentCells t ht htp,
    Finset.card_singleton]
  exact ⟨rfl, rfl⟩

end ThinParameters
end SkewClassInflation
