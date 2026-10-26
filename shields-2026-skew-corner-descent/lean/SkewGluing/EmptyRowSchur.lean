/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowAllShapes
import SkewGluing.RowBands

/-!
# Empty-mark row cofactor

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:row-cofactor`).  Actual eroded copies have separated
content bands, so the finite component-product theorem supplies their Schur product.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
variable {ω : MarkedInner}

/-- Empty-mark eroded copies lie strictly between consecutive singleton endpoint diagonals. -/
theorem IsLegal.empty_interiorCopy_bounds (h : ω.IsLegal) (hW : ω.W = ∅)
    {j : ℤ} {x : ℤ × ℤ} (hx : x ∈ translate (j • ω.v) (diagramInterior ω.E)) :
    minContent ω.E + j * ω.period + 1 ≤ content x ∧
      content x ≤ minContent ω.E + (j + 1) * ω.period - 2 := by
  have hb := interior_content_strict h.1.1 (mem_translate.mp hx)
  have hm : maxContent ω.E = minContent ω.E + ω.period - 1 := by
    have hs := span_eq_of_isConnectedSkew h.1.1
    have hp := IsLegalEmpty.span_eq ⟨h, hW⟩
    omega
  rw [content_sub, content_smul, hm] at hb
  change minContent ω.E < content x - j * ω.period ∧
    content x - j * ω.period < minContent ω.E + ω.period - 1 at hb
  constructor <;> nlinarith

/-- Distinct eroded empty-mark copies have a missing diagonal between them. -/
theorem IsLegal.empty_interiorCopy_separated (h : ω.IsLegal) (hW : ω.W = ∅)
    {i j : ℕ} (hij : i ≠ j) {x y : ℤ × ℤ}
    (hx : x ∈ translate ((i : ℤ) • ω.v) (diagramInterior ω.E))
    (hy : y ∈ translate ((j : ℤ) • ω.v) (diagramInterior ω.E)) :
    content x + 1 < content y ∨ content y + 1 < content x := by
  have hp := IsLegalEmpty.period_pos ⟨h, hW⟩
  have hxB := h.empty_interiorCopy_bounds hW hx
  have hyB := h.empty_interiorCopy_bounds hW hy
  exact separated_content_bands ω.period 0 (minContent ω.E) i j (content x) (content y)
    true true (le_refl _) hp (Or.inl (by exact_mod_cast hij)) (by simpa using hxB)
    (by simpa using hyB)

/-- The actual empty-mark row cofactor is the power of the single-inner cofactor. -/
theorem IsLegal.interiorSchur_rowCopies_empty (h : ω.IsLegal) (hW : ω.W = ∅)
    {m : ℕ} (hm : 1 ≤ m) :
    cellSchur (diagramInterior (ω.rowCopies m)) (h.isConnectedSkew_rowCopies_all hm).1.interior =
      cellSchur (diagramInterior ω.E) h.1.1.1.interior ^ m := by
  classical
  let D (j : ℕ) := translate ((j : ℤ) • ω.v) (diagramInterior ω.E)
  have hs (j : ℕ) : IsSkew (D j) := isSkew_translate _ h.1.1.1.interior
  have hu : IsSkew ((Finset.range m).biUnion D) := by
    rw [← h.interior_rowCopies_all m]
    exact (h.isConnectedSkew_rowCopies_all hm).1.interior
  have hp := cellSchur_biUnion (Finset.range m) D hs hu (by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hx hy
    have hh := h.empty_interiorCopy_separated hW hij hx hy
    omega) (by
    intro i _ j _ hij x hx y hy ha
    have hh := h.empty_interiorCopy_separated hW hij hx hy
    rw [cellAdj_iff] at ha
    simp only [content] at hh
    omega)
  rw [cellSchur_congr (h.interior_rowCopies_all m).symm _
    (h.isConnectedSkew_rowCopies_all hm).1.interior] at hp
  simp only [D] at hp
  simp_rw [cellSchur_translate (diagramInterior ω.E) h.1.1.1.interior] at hp
  simpa only [Finset.prod_const, Finset.card_range] using hp

end SkewGluing.MarkedInner
