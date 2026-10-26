/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.WindowShape
import SkewGluing.WindowErosion
import SkewGluing.PolynomialSupport

/-!
# Hatted-mark normalization

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`eq:normalization`, `eq:normalization-bounds`, `eq:cap-hat`).

The two private singleton diagonals give missing diagonals in the eroded overlap window.
Their absence makes the actual hatted mark skew and bounds its generator span.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- Both boundaries of the marked band are absent from the eroded two-copy window. -/
theorem IsLegal.windowInterior_gaps (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {x : ℤ × ℤ} (hx : x ∈ diagramInterior ω.windowCells) :
    content x ≠ minContent ω.E - 1 ∧ content x ≠ minContent ω.E + ω.width := by
  have hn := h.isNonemptyMark hW
  have hq := h.2.2.1.2
  have hm := hn.maxContent_E h.1.1
  rw [h.interior_windowCells hW, Finset.mem_union] at hx
  rcases hx with hx | hx
  · have hl := (interior_content_strict h.1.1 hx).1
    exact ⟨by omega, (h.interior_private_gaps hW hx).1⟩
  · have hy : x + ω.v ∈ diagramInterior ω.E := by
      simpa only [mem_translate, sub_neg_eq_add] using hx
    have hcy : content (x + ω.v) = content x + ω.period := content_add x ω.v
    have hu := (interior_content_strict h.1.1 hy).2
    have hg := (h.interior_private_gaps hW hy).2
    exact ⟨by omega, by omega⟩

/-- The actual hatted mark is skew, not merely a union of two abstract cap polynomials. -/
theorem IsLegal.isSkew_hatMarkWindow (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    IsSkew ω.hatMarkWindow := by
  have hwin : IsSkew ω.windowCells := IsLegalNonempty.isSkew_amalgam ⟨h, hW⟩
  have hcut := hwin.interior.filter_content_lt_of_gap (minContent ω.E + ω.width)
    (fun _ hx => (h.windowInterior_gaps hW hx).2)
  have hcut' := hcut.filter_content_gt_of_gap (minContent ω.E - 1)
    (fun _ hx => (h.windowInterior_gaps hW (Finset.mem_filter.mp hx).1).1)
  rw [h.hatMarkWindow_eq_band hW]
  convert hcut' using 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hl, hu⟩
    exact ⟨⟨hx, by omega⟩, by omega⟩
  · rintro ⟨⟨hx, hu⟩, hl⟩
    exact ⟨hx, by omega, by omega⟩

/-- The hatted mark occupies at most the original mark's number of content diagonals. -/
theorem IsLegal.hatMarkWindow_span_le (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    span ω.hatMarkWindow ≤ ω.width := by
  have hb := span_le_of_content_Ioo (D := ω.hatMarkWindow)
    (minContent ω.E - 1) (minContent ω.E + ω.width) (by
      intro x hx
      rw [h.hatMarkWindow_eq_band hW, Finset.mem_filter] at hx
      omega)
  omega

/-- The original mark's skewness follows from the standing marked-inner data. -/
theorem IsLegal.isSkew_mark (h : ω.IsLegal) (hW : ω.W.Nonempty) : IsSkew ω.W :=
  (h.isNonemptyMark hW).2.1.1

/-- The factor `A` is the actual skew function of the mark. -/
noncomputable def markA (ω : MarkedInner) (h : ω.IsLegal) (hW : ω.W.Nonempty) :=
  cellSchur ω.W (h.isSkew_mark hW)

/-- The factor `B` is the actual skew function of the finite hatted mark. -/
noncomputable def hatMarkB (ω : MarkedInner) (h : ω.IsLegal) (hW : ω.W.Nonempty) :=
  cellSchur ω.hatMarkWindow (h.isSkew_hatMarkWindow hW)

/-- The generators appearing in `A` are bounded by the mark width. -/
theorem IsLegal.markA_span_le (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    SkewCornerDescent.Matrix.polynomialSpan (ω.markA h hW) ≤ ω.width :=
  polynomialSpan_cellSchur_le _ _

/-- The generators appearing in `B` are bounded by the mark width. -/
theorem IsLegal.hatMarkB_span_le (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    SkewCornerDescent.Matrix.polynomialSpan (ω.hatMarkB h hW) ≤ ω.width :=
  (polynomialSpan_cellSchur_le _ _).trans (h.hatMarkWindow_span_le hW)

end SkewGluing.MarkedInner
