/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CellProfiles

/-!
# Horizontal marked cell intervals

The horizontal marks in `eq:saturation-marks` and `eq:inflation-marks`
of `shields-2026-skew-class-inflation.tex`.  Row intervals, their contents,
and their actual skew connectivity are retained.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing

-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/RowInner.lean, row-interval interface;
-- adapted only to the SkewClassInflation namespace.
/-- The row of cells `(0, j)`, `s ≤ j < e`. -/
def rowCells (s e : ℤ) : Diagram := (Finset.Ico s e).image fun j => ((0 : ℤ), j)

theorem mem_rowCells {s e a b : ℤ} : (a, b) ∈ rowCells s e ↔ a = 0 ∧ s ≤ b ∧ b < e := by
  simp only [rowCells, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨rfl, hj⟩
  · rintro ⟨rfl, hb⟩; exact ⟨b, hb, rfl, rfl⟩

theorem contents_rowCells (s e : ℤ) : contents (rowCells s e) = Finset.Ico s e := by
  ext k
  rw [mem_contents_iff, Finset.mem_Ico]
  simp only [mem_rowCells]
  constructor
  · rintro ⟨i, rfl, h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨0, rfl, by omega, by omega⟩

theorem span_rowCells (s e : ℤ) : span (rowCells s e) = (e - s).toNat := by
  unfold span
  rw [contents_rowCells, Int.card_Ico]

theorem rowCells_nonempty {s e : ℤ} (h : s < e) : (rowCells s e).Nonempty :=
  ⟨(0, s), mem_rowCells.mpr ⟨rfl, le_refl _, h⟩⟩

theorem minContent_rowCells {s e : ℤ} (h : s < e) : minContent (rowCells s e) = s := by
  apply minContent_eq_of
  · rw [contents_rowCells]; exact Finset.mem_Ico.mpr ⟨le_refl _, h⟩
  · intro k hk
    rw [contents_rowCells, Finset.mem_Ico] at hk
    exact hk.1

theorem maxContent_rowCells {s e : ℤ} (h : s < e) : maxContent (rowCells s e) = e - 1 := by
  apply maxContent_eq_of
  · rw [contents_rowCells]; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk
    rw [contents_rowCells, Finset.mem_Ico] at hk
    omega

theorem diagLo_rowCells {s e k : ℤ} (hk : s ≤ k) (hk' : k < e) : diagLo (rowCells s e) k = 0 := by
  apply diagLo_eq_of (l := 0)
  · rw [zero_add]; exact mem_rowCells.mpr ⟨rfl, hk, hk'⟩
  · intro i hi
    have := (mem_rowCells.mp hi).1
    omega

theorem sw_rowCells {s e : ℤ} (h : s < e) : sw (rowCells s e) = (0, s) := by
  unfold sw
  rw [minContent_rowCells h, diagLo_rowCells (le_refl _) h]
  simp

theorem ne_rowCells {s e : ℤ} (h : s < e) : ne (rowCells s e) = (0, e - 1) := by
  unfold ne
  rw [maxContent_rowCells h, diagLo_rowCells (by omega) (by omega)]
  simp

theorem isConnectedSkew_rowCells {s e : ℤ} (h : s < e) : IsConnectedSkew (rowCells s e) := by
  have hs : IsSkew (rowCells s e) := by
    intro x hx y hy h1 h2 i hi j hj
    obtain ⟨a, b⟩ := x
    obtain ⟨c, d⟩ := y
    obtain ⟨ha, hb1, hb2⟩ := mem_rowCells.mp hx
    obtain ⟨hc, hd1, hd2⟩ := mem_rowCells.mp hy
    simp only [Finset.mem_Icc] at hi hj
    exact mem_rowCells.mpr ⟨by omega, by omega, by omega⟩
  refine ⟨hs, isEdgeConnected_of_reach (c₀ := (0, s)) (mem_rowCells.mpr ⟨rfl, le_refl _, h⟩) ?_⟩
  intro x hx
  obtain ⟨a, b⟩ := x
  obtain ⟨ha, hb1, hb2⟩ := mem_rowCells.mp hx
  subst ha
  exact hs.reach_row (mem_rowCells.mpr ⟨rfl, le_refl _, h⟩) hx

end SkewClassInflation
