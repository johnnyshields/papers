/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.EmptyRowErosion

/-!
# Finite-cap regrouping of row interiors

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:row-cofactor`).  End caps occur only at the two ends;
internal junctions contain the full hatted-mark union, including its overlap.

Sorry-free.
-/

namespace SkewGluing

/-- Translation distributes over a finite union. -/
theorem translate_union (t : ℤ × ℤ) (A B : Diagram) :
    translate t (A ∪ B) = translate t A ∪ translate t B := by
  ext x
  simp only [mem_translate, Finset.mem_union]

namespace MarkedInner

variable {ω : MarkedInner}

/-- The actual shifted hatted mark combines neighboring caps, not two disjoint copies. -/
theorem IsLegal.translatedHat_eq (h : ω.IsLegal) (hW : ω.W.Nonempty) (j : ℤ) :
    translate (j • ω.v) ω.hatMarkWindow =
      translate (j • ω.v) ω.lowerCap ∪ translate ((j - 1) • ω.v) ω.upperCap := by
  rw [h.hatMarkWindow_eq_caps hW, translate_union, translate_translate]
  congr 2
  module

/-- The finite row-interior pieces before taking their skew functions. -/
def rowInteriorPieces (ω : MarkedInner) (m : ℕ) : Diagram :=
  ω.lowerCap ∪ translate (((m - 1 : ℕ) : ℤ) • ω.v) ω.upperCap ∪
    (Finset.range m).biUnion (fun j => translate ((j : ℤ) • ω.v) (diagramInterior ω.middle)) ∪
    (Finset.Ico 1 m).biUnion (fun j => translate ((j : ℤ) • ω.v) ω.hatMarkWindow)

/-- Regrouping the eroded row union into two end caps, middle copies, and internal hatted marks. -/
theorem IsLegal.interior_rowCopies_eq_pieces (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) : diagramInterior (ω.rowCopies m) = ω.rowInteriorPieces m := by
  rw [h.interior_rowCopies_all]
  ext x
  simp only [rowInteriorPieces, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_Ico]
  have member (j : ℕ) :
      x ∈ translate ((j : ℤ) • ω.v) (diagramInterior ω.E) ↔
        (x ∈ translate ((j : ℤ) • ω.v) ω.lowerCap ∨
          x ∈ translate ((j : ℤ) • ω.v) (diagramInterior ω.middle)) ∨
        x ∈ translate ((j : ℤ) • ω.v) ω.upperCap := by
    rw [h.interior_eq_caps hW, translate_union, translate_union]
    simp only [Finset.mem_union]
  have hatMember (j : ℕ) :
      x ∈ translate ((j : ℤ) • ω.v) ω.hatMarkWindow ↔
        x ∈ translate ((j : ℤ) • ω.v) ω.lowerCap ∨
          x ∈ translate (((j : ℤ) - 1) • ω.v) ω.upperCap := by
    rw [h.translatedHat_eq hW]
    exact Finset.mem_union
  constructor
  · rintro ⟨j, hj, hx⟩
    rw [member] at hx
    rcases hx with (hx | hx) | hx
    · by_cases hj0 : j = 0
      · subst hj0
        exact Or.inl (Or.inl (Or.inl (by simpa only [Nat.cast_zero, zero_smul,
          translate_zero] using hx)))
      · exact Or.inr ⟨j, ⟨by omega, hj⟩, (hatMember j).mpr (Or.inl hx)⟩
    · exact Or.inl (Or.inr ⟨j, hj, hx⟩)
    · by_cases hjlast : j = m - 1
      · subst hjlast
        exact Or.inl (Or.inl (Or.inr hx))
      · refine Or.inr ⟨j + 1, ⟨by omega, by omega⟩, (hatMember (j + 1)).mpr (Or.inr ?_)⟩
        simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hx
  · rintro (((hx | hx) | ⟨j, hj, hx⟩) | ⟨j, hj, hx⟩)
    · refine ⟨0, by omega, (member 0).mpr (Or.inl (Or.inl ?_))⟩
      simpa only [Nat.cast_zero, zero_smul, translate_zero] using hx
    · exact ⟨m - 1, by omega, (member _).mpr (Or.inr hx)⟩
    · exact ⟨j, hj, (member j).mpr (Or.inl (Or.inr hx))⟩
    · rw [hatMember] at hx
      rcases hx with hx | hx
      · exact ⟨j, hj.2, (member j).mpr (Or.inl (Or.inl hx))⟩
      · refine ⟨j - 1, by omega, (member _).mpr (Or.inr ?_)⟩
        have hc : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        simpa only [hc] using hx

end MarkedInner
end SkewGluing
