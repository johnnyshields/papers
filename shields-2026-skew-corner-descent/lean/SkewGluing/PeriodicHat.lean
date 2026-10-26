/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.HatNormalization

/-!
# Finite realization of the periodic hatted mark

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`eq:hatted-sets`, `eq:cap-hat`).  The periodic definition and the finite overlap-window
realization coincide on the marked band.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- Only the current and preceding copies meet the marked content band. -/
theorem IsLegal.periodicUnion_iff_window (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {x : ℤ × ℤ} (hc : minContent ω.E ≤ content x ∧
      content x ≤ minContent ω.E + ω.width - 1) :
    x ∈ ω.periodicUnion ↔ x ∈ ω.windowCells := by
  have hn := h.isNonemptyMark hW
  have hm := hn.maxContent_E h.1.1
  have hq := h.2.2.1.2
  have hqp : 0 < ω.period := by omega
  constructor
  · rintro ⟨k, hk⟩
    have hlo := minContent_le (content_mem_contents hk)
    have hhi := le_maxContent (content_mem_contents hk)
    rw [content_sub, content_smul] at hlo hhi
    change minContent ω.E ≤ content x - k * ω.period at hlo
    change content x - k * ω.period ≤ maxContent ω.E at hhi
    have hk0 : k ≤ 0 := by
      by_contra hh
      have hk1 : 1 ≤ k := by omega
      have hmul := mul_le_mul_of_nonneg_right hk1 (le_of_lt hqp)
      nlinarith
    have hk1 : -1 ≤ k := by
      by_contra hh
      have hk2 : k ≤ -2 := by omega
      have hmul := mul_le_mul_of_nonneg_right hk2 (le_of_lt hqp)
      nlinarith
    have hcases : k = 0 ∨ k = -1 := by omega
    simp only [windowCells, Finset.mem_union]
    rcases hcases with rfl | rfl
    · exact Or.inl (by simpa only [zero_smul, sub_zero] using hk)
    · exact Or.inr (by simpa only [mem_translate, neg_one_smul] using hk)
  · simp only [windowCells, Finset.mem_union, mem_translate, sub_neg_eq_add]
    rintro (hx | hx)
    · exact ⟨0, by simpa only [zero_smul, sub_zero] using hx⟩
    · exact ⟨-1, by simpa only [neg_one_smul, sub_neg_eq_add] using hx⟩

/-- The finite hatted mark is exactly the paper's periodic set, not a substitute for it. -/
theorem IsLegal.mem_hatMark_iff_window (h : ω.IsLegal) (hW : ω.W.Nonempty) {x : ℤ × ℤ} :
    x ∈ ω.hatMark ω.W ↔ x ∈ ω.hatMarkWindow := by
  have hn := h.isNonemptyMark hW
  simp only [hatMark, Set.mem_union, Set.mem_ofPred_eq, hatMarkWindow,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hx, hxeW⟩ | ⟨hxW, hxe⟩)
    · have hc := hn.content_W h.1.1 hxeW
      rw [content_eCell_add] at hc
      exact Or.inl ⟨(h.periodicUnion_iff_window hW hc).mp hx, hxeW⟩
    · have hc := hn.content_W h.1.1 hxW
      have hce : minContent ω.E ≤ content (x + eCell) ∧
          content (x + eCell) ≤ minContent ω.E + ω.width - 1 := by
        simpa only [content_eCell_add] using hc
      exact Or.inr ⟨hxW, (h.periodicUnion_iff_window hW hce).mp hxe⟩
  · rintro (⟨hx, hxeW⟩ | ⟨hxW, hxe⟩)
    · have hc := hn.content_W h.1.1 hxeW
      rw [content_eCell_add] at hc
      exact Or.inl ⟨(h.periodicUnion_iff_window hW hc).mpr hx, hxeW⟩
    · have hc := hn.content_W h.1.1 hxW
      have hce : minContent ω.E ≤ content (x + eCell) ∧
          content (x + eCell) ≤ minContent ω.E + ω.width - 1 := by
        simpa only [content_eCell_add] using hc
      exact Or.inr ⟨hxW, (h.periodicUnion_iff_window hW hce).mpr hxe⟩

/-- The paper's actual periodic hatted mark is the cap union, with overlap retained. -/
theorem IsLegal.hatMark_eq_caps (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω.hatMark ω.W = (ω.lowerCap ∪ translate (-ω.v) ω.upperCap : Set (ℤ × ℤ)) := by
  ext x
  rw [h.mem_hatMark_iff_window hW, h.hatMarkWindow_eq_caps hW]
  simp only [Finset.mem_union, Set.mem_union, Finset.mem_coe]

end SkewGluing.MarkedInner
