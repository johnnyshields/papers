/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowErosion

/-!
# Horizontal row composition

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:erosion-union`).  A normalized horizontal row has one cell
on each diagonal and no supplemental copies in any attachment case.

Sorry-free.
-/

namespace SkewGluing

/-- The normalized horizontal row with `m` cells. -/
def horizontalRow (m : ℕ) : Diagram :=
  (Finset.Ico (0 : ℤ) m).image fun j => (0, j)

/-- Membership in the actual normalized horizontal row. -/
theorem mem_horizontalRow {m : ℕ} {x : ℤ × ℤ} :
    x ∈ horizontalRow m ↔ x.1 = 0 ∧ 0 ≤ x.2 ∧ x.2 < m := by
  simp only [horizontalRow, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨rfl, hj⟩
  · rintro ⟨h0, hl, hu⟩
    exact ⟨x.2, ⟨hl, hu⟩, by ext <;> simp [h0]⟩

theorem horizontalRow_nonempty {m : ℕ} (hm : 1 ≤ m) : (horizontalRow m).Nonempty :=
  ⟨(0, 0), mem_horizontalRow.mpr ⟨rfl, le_refl _, by omega⟩⟩

/-- The row has exactly one cell on each occupied diagonal. -/
theorem horizontalRow_diagLo {m : ℕ} {k : ℤ} (hl : 0 ≤ k) (hu : k < m) :
    diagLo (horizontalRow m) k = 0 := by
  apply diagLo_eq_of
  · simpa only [zero_add] using
      (mem_horizontalRow.mpr ⟨rfl, hl, hu⟩ : (0, k) ∈ horizontalRow m)
  · intro i hi
    have := (mem_horizontalRow.mp hi).1
    omega

theorem horizontalRow_diagHi {m : ℕ} {k : ℤ} (hl : 0 ≤ k) (hu : k < m) :
    diagHi (horizontalRow m) k = 0 := by
  apply diagHi_eq_of
  · simpa only [zero_add] using
      (mem_horizontalRow.mpr ⟨rfl, hl, hu⟩ : (0, k) ∈ horizontalRow m)
  · intro i hi
    have := (mem_horizontalRow.mp hi).1
    omega

namespace MarkedInner

variable (ω : MarkedInner)

/-- Every row cell is placed at its content times the period vector. -/
theorem origin_horizontalRow {m : ℕ} {x : ℤ × ℤ} (hx : x ∈ horizontalRow m) :
    ω.origin (horizontalRow m) x = content x • ω.v := by
  obtain ⟨h0, hl, hu⟩ := mem_horizontalRow.mp hx
  have hc : content x = x.2 := by simp only [content, h0, sub_zero]
  have hlo := horizontalRow_diagLo hl hu
  have hhi := horizontalRow_diagHi hl hu
  unfold origin
  cases ω.case <;> simp only [h0, hc, hlo, hhi, sub_self, zero_smul, add_zero, sub_zero]

/-- No horizontal row has a north neighbor, so no supplemental copy is inserted. -/
theorem not_sameRibbon_horizontalRow {m : ℕ} {x : ℤ × ℤ}
    (hx : x ∈ horizontalRow m) : ¬ ω.SameRibbon (horizontalRow m) x := by
  intro hh
  have h0 := (mem_horizontalRow.mp hx).1
  have hn := (mem_horizontalRow.mp hh.1).1
  omega

/-- The finite row union is the actual composition, in all four attachment cases. -/
theorem compose_horizontalRow {m : ℕ} (hm : 1 ≤ m) :
    ω.compose (horizontalRow m) = ω.rowCopies m := by
  ext x
  rw [mem_compose (horizontalRow_nonempty hm)]
  simp only [rowCopies, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hr, _⟩)
    · obtain ⟨h0, hl, hu⟩ := mem_horizontalRow.mp hd
      refine ⟨d.2.toNat, by omega, ?_⟩
      rw [ω.origin_horizontalRow hd] at hx
      have hc : content d = (d.2.toNat : ℤ) := by
        simp only [content, h0, sub_zero, Int.toNat_of_nonneg hl]
      rwa [hc] at hx
    · exact (ω.not_sameRibbon_horizontalRow hd hr).elim
  · rintro ⟨j, hj, hx⟩
    have hd : (0, (j : ℤ)) ∈ horizontalRow m :=
      mem_horizontalRow.mpr ⟨rfl, by omega, by omega⟩
    refine Or.inl ⟨(0, (j : ℤ)), hd, ?_⟩
    rw [ω.origin_horizontalRow hd]
    simpa only [content, sub_zero] using hx

/-- The paper's erosion formula for its actual horizontal-row composition. -/
theorem IsLegal.interior_compose_horizontalRow (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) :
    diagramInterior (ω.compose (horizontalRow m)) =
      (Finset.range m).biUnion fun j => translate ((j : ℤ) • ω.v) (diagramInterior ω.E) := by
  rw [ω.compose_horizontalRow hm]
  exact h.interior_rowCopies hW m

end MarkedInner
end SkewGluing
