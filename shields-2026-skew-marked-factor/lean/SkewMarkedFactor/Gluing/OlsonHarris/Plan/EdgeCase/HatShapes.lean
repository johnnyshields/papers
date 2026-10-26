/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/HatShapes.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Defs

/-!
# The hat shapes of a mark

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`): thesis §5.3.1 and Remark 5.3.7
(`OlsonHarris2024HopfApplications`).

The hatted mark `hatMarkFin ω` is computed with the periodic window of the copies `-2 ≤ k ≤ 2`;
for a well-formed narrow mark only the copies `E` and `E - v` meet the cells next to `W₋`, so it
equals the window form `hatMarkWindow ω` of `SkewMarkedFactor.Gluing.Mark`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace MarkedInner

open SkewMarkedFactor.Gluing.MarkedInner

theorem mem_periodicWindow {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ periodicWindow ω ↔ ∃ k ∈ Finset.Icc (-2 : ℤ) 2, x - k • ω.v ∈ ω.E := by
  unfold periodicWindow
  simp only [Finset.mem_biUnion, mem_translate]

/-- For a cell whose content lies in the range of `W₋`, membership in the periodic window is
membership in `E ∪ (E - v)`. -/
theorem mem_periodicWindow_iff {ω : MarkedInner} (hwf : ω.IsWellFormed) (hII : ω.IsNarrow)
    (hnon : ω.IsNonemptyMark) {x : ℤ × ℤ}
    (hc : minContent ω.E ≤ content x ∧ content x ≤ minContent ω.E + ω.width - 1) :
    x ∈ periodicWindow ω ↔ x ∈ ω.E ∨ x + ω.v ∈ ω.E := by
  have hb := hnon.content_bounds hwf.1
  obtain ⟨hw0, hwq⟩ := hII
  rw [mem_periodicWindow]
  constructor
  · rintro ⟨k, hk, hx⟩
    have h1 := (hb.2 _ hx)
    rw [content_sub, content_smul] at h1
    rw [Finset.mem_Icc] at hk
    have hq : content ω.v = ω.period := rfl
    rw [hq] at h1
    have hk' : k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl
    · exfalso; nlinarith [h1.1, h1.2]
    · right
      have : x - (-1 : ℤ) • ω.v = x + ω.v := by simp
      rwa [this] at hx
    · left; simpa using hx
    · exfalso; nlinarith [h1.1, h1.2]
    · exfalso; nlinarith [h1.1, h1.2]
  · rintro (h | h)
    · exact ⟨0, by simp, by simpa using h⟩
    · refine ⟨-1, by simp, ?_⟩
      have : x - (-1 : ℤ) • ω.v = x + ω.v := by simp
      rwa [this]

theorem mem_hatMarkFin {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ hatMarkFin ω ↔ (x + eCell ∈ ω.W ∧ x ∈ periodicWindow ω) ∨
      (x ∈ ω.W ∧ x + eCell ∈ periodicWindow ω) := by
  unfold hatMarkFin
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨⟨x + eCell, h1, by abel⟩, h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

theorem mem_hatMiddleFin {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ hatMiddleFin ω ↔ x ∈ ω.middle ∧ x + eCell ∈ ω.middle := by
  unfold hatMiddleFin
  rw [Finset.mem_filter]

theorem mem_hatMarkWindow {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ hatMarkWindow ω ↔ (x ∈ ω.windowCells ∧ x + eCell ∈ ω.W) ∨
      (x ∈ ω.W ∧ x + eCell ∈ ω.windowCells) := by
  unfold hatMarkWindow
  simp only [Finset.mem_union, Finset.mem_filter]

theorem mem_windowCells {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ ω.windowCells ↔ x ∈ ω.E ∨ x + ω.v ∈ ω.E := by
  unfold windowCells
  simp only [Finset.mem_union, mem_translate, sub_neg_eq_add]

/-- **The finite periodic window computes the hatted mark.** -/
theorem hatMarkFin_eq_hatMarkWindow {ω : MarkedInner} (hwf : ω.IsWellFormed)
    (hII : ω.IsNarrow) : hatMarkFin ω = hatMarkWindow ω := by
  rcases hwf.2 with hemp | hnon
  · have hW := hemp.1
    simp [hatMarkFin, hatMarkWindow, hW]
  · have hb := hnon.content_bounds hwf.1
    have hbW := hb.1
    have key : ∀ z : ℤ × ℤ, z ∈ ω.W → (z + eCell ∈ periodicWindow ω ↔
        z + eCell ∈ ω.E ∨ z + eCell + ω.v ∈ ω.E) := by
      intro z hz
      have := hbW z hz
      rw [← content_eCell_add] at this
      exact mem_periodicWindow_iff hwf hII hnon this
    have key' : ∀ z : ℤ × ℤ, z + eCell ∈ ω.W →
        (z ∈ periodicWindow ω ↔ z ∈ ω.E ∨ z + ω.v ∈ ω.E) := by
      intro z hz
      have := hbW _ hz
      rw [content_eCell_add] at this
      exact mem_periodicWindow_iff hwf hII hnon this
    ext x
    rw [mem_hatMarkFin, mem_hatMarkWindow, mem_windowCells, mem_windowCells]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨(key' x h1).mp h2, h1⟩
      · exact Or.inr ⟨h1, (key x h1).mp h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, (key' x h2).mpr h1⟩
      · exact Or.inr ⟨h1, (key x h1).mpr h2⟩

end MarkedInner

end Plan

end SkewMarkedFactor.Gluing
