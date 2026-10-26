/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowConnected
import SkewGluing.CapSchur
import SkewGluing.FiniteSchurProduct

/-!
# Indexed finite row factors

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:row-cofactor`).  The index distinguishes the two end caps,
every middle copy, and every internal hatted-mark junction.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

/-- Indices for two end caps, `m` middle copies, and `m - 1` internal junctions. -/
abbrev RowPieceIndex (m : ℕ) := Bool ⊕ (Fin m ⊕ Fin (m - 1))

/-- Actual cell diagrams of the row factors. -/
def rowPiece (ω : MarkedInner) (m : ℕ) : RowPieceIndex m → Diagram
  | .inl false => ω.lowerCap
  | .inl true => translate (((m - 1 : ℕ) : ℤ) • ω.v) ω.upperCap
  | .inr (.inl j) => translate ((j.val : ℤ) • ω.v) (diagramInterior ω.middle)
  | .inr (.inr j) => translate (((j.val + 1 : ℕ) : ℤ) • ω.v) ω.hatMarkWindow

variable {ω : MarkedInner}

/-- Every member of the row factor family is a genuine skew diagram. -/
theorem IsLegal.isSkew_rowPiece (h : ω.IsLegal) (hW : ω.W.Nonempty) (m : ℕ)
    (i : RowPieceIndex m) : IsSkew (ω.rowPiece m i) := by
  rcases i with b | j | j
  · cases b
    · exact h.isSkew_lowerCap hW
    · exact isSkew_translate _ (h.isSkew_upperCap hW)
  · exact isSkew_translate _ (h.middle_connected hW).1.interior
  · exact isSkew_translate _ (h.isSkew_hatMarkWindow hW)

/-- The indexed row factors have exactly the actual regrouped cell union. -/
theorem rowPiece_union {m : ℕ} (hm : 1 ≤ m) :
    Finset.univ.biUnion (ω.rowPiece m) = ω.rowInteriorPieces m := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, rowInteriorPieces,
    Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hx⟩
    rcases i with b | j | j
    · cases b
      · exact Or.inl (Or.inl (Or.inl hx))
      · exact Or.inl (Or.inl (Or.inr hx))
    · exact Or.inl (Or.inr ⟨j.val, j.isLt, hx⟩)
    · exact Or.inr ⟨j.val + 1, ⟨by omega, by omega⟩, hx⟩
  · rintro (((hx | hx) | ⟨j, hj, hx⟩) | ⟨j, hj, hx⟩)
    · exact ⟨.inl false, hx⟩
    · exact ⟨.inl true, hx⟩
    · exact ⟨.inr (.inl ⟨j, hj⟩), hx⟩
    · refine ⟨.inr (.inr ⟨j - 1, by omega⟩), ?_⟩
      change x ∈ translate (((j - 1 + 1 : ℕ) : ℤ) • ω.v) ω.hatMarkWindow
      have hj' : j - 1 + 1 = j := by omega
      simpa only [hj'] using hx

/-- The family union is the actual eroded row, rather than an assumed cofactor factorization. -/
theorem IsLegal.rowPiece_union_eq_interior (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) :
    Finset.univ.biUnion (ω.rowPiece m) = diagramInterior (ω.rowCopies m) := by
  rw [rowPiece_union hm]
  exact (h.interior_rowCopies_eq_pieces hW hm).symm

/-- The family union is skew by the connected actual row and its erosion. -/
theorem IsLegal.isSkew_rowPiece_union (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) : IsSkew (Finset.univ.biUnion (ω.rowPiece m)) := by
  rw [h.rowPiece_union_eq_interior hW hm]
  exact (h.isConnectedSkew_rowCopies hW m hm).1.interior

end SkewGluing.MarkedInner
