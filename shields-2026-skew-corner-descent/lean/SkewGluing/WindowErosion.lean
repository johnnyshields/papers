/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.DiagonalErosion
import SkewGluing.FiniteCaps
import SkewGluing.InteriorProfile

/-!
# Erosion in a legal overlap window

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`sec:marks`, `eq:erosion-union`, `eq:cap-hat`).

The full intersection identifies the overlap. The two copies overlap on every common
diagonal, so every eroded pair in their union lies in one copy.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- The neighboring-copy intersection is the actual lower marked copy. -/
theorem IsLegal.window_intersection (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω.E ∩ translate (-ω.v) ω.E = ω.W := by
  rw [h.W_eq_fullIntersection hW]
  ext x
  simp only [Finset.mem_inter, mem_translate, fullIntersection, Finset.mem_filter,
    sub_neg_eq_add]

/-- Every diagonal occupied by both neighboring copies is occupied by their intersection. -/
theorem IsLegal.window_diagonal_overlap (h : ω.IsLegal) (hW : ω.W.Nonempty) (k : ℤ)
    (hkE : k ∈ contents ω.E) (hkT : k ∈ contents (translate (-ω.v) ω.E)) :
    k ∈ contents (ω.E ∩ translate (-ω.v) ω.E) := by
  have hn := h.isNonemptyMark hW
  have hr := hn.W_range h.1.1
  have hm := hn.maxContent_E h.1.1
  have hkT' := mem_contents_translate.mp hkT
  have hlo := minContent_le hkE
  have hhi := le_maxContent hkT'
  have hv : content (-ω.v) = -ω.period := by
    simp [period, content]
    ring
  rw [hv] at hhi
  rw [h.window_intersection hW]
  exact (isConnectedSkew_iff_diagonal.mp hn.2.1).mem_contents_iff.mpr ⟨by omega, by omega⟩

/-- Erosion commutes with the union of the two copies in the finite overlap window. -/
theorem IsLegal.interior_windowCells (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    diagramInterior ω.windowCells =
      diagramInterior ω.E ∪ translate (-ω.v) (diagramInterior ω.E) := by
  change diagramInterior (ω.E ∪ translate (-ω.v) ω.E) = _
  rw [interior_union_of_overlap h.1.1.1 (isSkew_translate (-ω.v) h.1.1.1)
    (h.window_diagonal_overlap hW), interior_translate]

/-- An eroded pair on a marked diagonal meets one of the two marked copies. -/
theorem IsLegal.interior_pair_meets_mark (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {x : ℤ × ℤ} (hx : x ∈ diagramInterior ω.E)
    (hc : content x ≤ minContent ω.E + ω.width - 1 ∨ minContent ω.E + ω.period ≤ content x) :
    x ∈ ω.W ∨ x + eCell ∈ ω.W ∨ x ∈ ω.upper ∨ x + eCell ∈ ω.upper := by
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨hxE, hxeE⟩ := Finset.mem_filter.mp hx
  have hxO : x ∈ ω.middle := mem_middle.mpr ⟨hxE, hn.1, hn.2.2.1⟩
  have hxeO : x + eCell ∈ ω.middle := mem_middle.mpr ⟨hxeE, hn.2.1, hn.2.2.2⟩
  have he := h.middle_subsingleton hW hxO hxeO (content_eCell_add x).symm hc
  have := congrArg Prod.fst he
  simp only [eCell, Prod.fst_add] at this
  omega

/-- The finite hatted mark is exactly the eroded overlap-window band. -/
theorem IsLegal.hatMarkWindow_eq_band (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω.hatMarkWindow = (diagramInterior ω.windowCells).filter
      (fun x => minContent ω.E ≤ content x ∧ content x ≤ minContent ω.E + ω.width - 1) := by
  have hn := h.isNonemptyMark hW
  have hwq := h.2.2.1.2
  have hWwin : ω.W ⊆ ω.windowCells := fun _ hx =>
    Finset.mem_union_left _ (hn.2.2.1 hx)
  ext x
  constructor
  · intro hx
    simp only [hatMarkWindow, Finset.mem_union, Finset.mem_filter] at hx
    apply Finset.mem_filter.mpr
    rcases hx with ⟨hxwin, hxeW⟩ | ⟨hxW, hxewin⟩
    · refine ⟨Finset.mem_filter.mpr ⟨hxwin, hWwin hxeW⟩, ?_⟩
      simpa only [content_eCell_add] using hn.content_W h.1.1 hxeW
    · exact ⟨Finset.mem_filter.mpr ⟨hWwin hxW, hxewin⟩, hn.content_W h.1.1 hxW⟩
  · intro hx
    obtain ⟨hxI, hc⟩ := Finset.mem_filter.mp hx
    have hp := Finset.mem_filter.mp hxI
    have hor : x ∈ ω.W ∨ x + eCell ∈ ω.W := by
      rw [h.interior_windowCells hW, Finset.mem_union] at hxI
      rcases hxI with hxI | hxI
      · have hm := h.interior_pair_meets_mark hW hxI (Or.inl hc.2)
        have hnotU : ∀ z, content z = content x → z ∉ ω.upper := by
          intro z hz hzU
          have := (hn.content_upper h.1.1 hzU).1
          omega
        rcases hm with hxW | hxeW | hxU | hxeU
        · exact Or.inl hxW
        · exact Or.inr hxeW
        · exact (hnotU x rfl hxU).elim
        · exact (hnotU _ (content_eCell_add x) hxeU).elim
      · have hyI : x + ω.v ∈ diagramInterior ω.E := by
          simpa only [mem_translate, sub_neg_eq_add] using hxI
        have hcy : content (x + ω.v) = content x + ω.period := content_add x ω.v
        have hm := h.interior_pair_meets_mark hW hyI (Or.inr (by omega))
        have hnotW : ∀ z, content z = content (x + ω.v) → z ∉ ω.W := by
          intro z hz hzW
          have := (hn.content_W h.1.1 hzW).2
          omega
        rcases hm with hyW | hyeW | hyU | hyeU
        · exact (hnotW _ rfl hyW).elim
        · exact (hnotW _ (content_eCell_add _) hyeW).elim
        · exact Or.inl (by
            have := mem_upper.mp hyU
            simpa only [add_sub_cancel_right] using this)
        · exact Or.inr (by
            have := mem_upper.mp hyeU
            convert this using 1
            abel)
    simp only [hatMarkWindow, Finset.mem_union, Finset.mem_filter]
    rcases hor with hxW | hxeW
    · exact Or.inr ⟨hxW, hp.2⟩
    · exact Or.inl ⟨hp.1, hxeW⟩

/-- The hatted mark is the union of the lower cap and the shifted upper cap,
with overlap allowed. -/
theorem IsLegal.hatMarkWindow_eq_caps (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω.hatMarkWindow = ω.lowerCap ∪ translate (-ω.v) ω.upperCap := by
  have hn := h.isNonemptyMark hW
  have hm := hn.maxContent_E h.1.1
  rw [h.hatMarkWindow_eq_band hW, h.interior_windowCells hW]
  ext x
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hc⟩
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx, by omega⟩)
    · apply Or.inr
      rw [mem_translate, sub_neg_eq_add]
      have hyI : x + ω.v ∈ diagramInterior ω.E := by
        simpa only [mem_translate, sub_neg_eq_add] using hx
      refine Finset.mem_filter.mpr ⟨hyI, ?_⟩
      have hcy : content (x + ω.v) = content x + ω.period := content_add x ω.v
      omega
  · rintro (hx | hx)
    · obtain ⟨hxI, hxk⟩ := Finset.mem_filter.mp hx
      have hl := (interior_content_strict h.1.1 hxI).1
      exact ⟨Or.inl hxI, by omega⟩
    · rw [mem_translate, sub_neg_eq_add] at hx
      obtain ⟨hyI, hyk⟩ := Finset.mem_filter.mp hx
      have hcy : content (x + ω.v) = content x + ω.period := content_add x ω.v
      have hu := (interior_content_strict h.1.1 hyI).2
      refine ⟨Or.inr (by simpa only [mem_translate, sub_neg_eq_add] using hyI), ?_⟩
      omega

end SkewGluing.MarkedInner
