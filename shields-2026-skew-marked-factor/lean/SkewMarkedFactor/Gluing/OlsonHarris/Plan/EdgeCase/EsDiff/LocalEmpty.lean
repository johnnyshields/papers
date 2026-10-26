/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/EsDiff/LocalEmpty.lean
import SkewMarkedFactor.Gluing.EqualPeriods
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EsDiff.Local

/-!
# The pieces of one copy of `E`, for the empty mark

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.4.3
(`OlsonHarris2024HopfApplications`) for `W = ∅`.

For the empty mark the middle is all of `E`, the key ribbon is the whole northwest border, `W`
and `\overline W` are empty and `\overline O` is `E` without its northwest border.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace EsDiff

open scoped Classical

open SkewMarkedFactor.Gluing.MarkedInner

variable {ω : MarkedInner}

theorem hatMarkFin_empty (hW : ω.W = ∅) : hatMarkFin ω = ∅ := by
  simp [hatMarkFin, hW]

theorem pieceE_empty (hW : ω.W = ∅) : pieceE ω = ∅ := by
  simp [pieceE, hW, translate]

theorem pieceS_empty (hW : ω.W = ∅) : pieceS ω = ∅ := by
  simp [pieceS, hatMarkFin_empty hW, translate]

theorem middle_empty (hW : ω.W = ∅) : ω.middle = ω.E := by
  simp [MarkedInner.middle, MarkedInner.upper, hW, translate]

theorem content_sub_eCell (z : ℤ × ℤ) : content (z - eCell) = content z := by
  simp [content, eCell]

theorem mem_pieceSE_empty (hW : ω.W = ∅) {z : ℤ × ℤ} :
    z ∈ pieceSE ω ↔ z ∈ ω.E ∧ z - eCell ∈ ω.E := by
  rw [mem_pieceSE, Plan.MarkedInner.mem_hatMiddleFin, middle_empty hW]
  simp only [sub_add_cancel]
  tauto

theorem edgeLocal_empty (h : ω.IsLegal) (hW : ω.W = ∅) : EdgeLocal ω := by
  have hE := h.1.1
  have hEne : ω.E.Nonempty := hE.2.1
  have hq := h.period_pos
  have hw0 : ω.width = 0 := MarkedInner.width_eq_zero_of_eq_empty hW
  have hcE := h.1.contents_eq
  rw [hw0] at hcE
  set c0 := minContent ω.E with hc0
  have hrange : ∀ z ∈ ω.E, c0 ≤ content z ∧ content z ≤ c0 + ω.period - 1 := by
    intro z hz
    have := content_mem_contents hz
    rw [hcE, Finset.mem_Icc] at this
    push_cast at this
    omega
  have hmax : maxContent ω.E = c0 + ω.period - 1 := by
    refine maxContent_eq_of ?_ fun k hk => ?_
    · rw [hcE, Finset.mem_Icc]; push_cast; omega
    · rw [hcE, Finset.mem_Icc] at hk; push_cast at hk; omega
  have hkey : ∀ z, z ∈ keyRibbon ω ↔ z ∈ ω.E ∧ z - eCell ∉ ω.E := by
    intro z
    rw [mem_keyRibbon, middle_empty hW, hmax]
    constructor
    · rintro ⟨h1, -⟩; exact h1
    · intro h1
      have := hrange z h1.1
      exact ⟨h1, by omega, by omega⟩
  have hPE := pieceE_empty hW
  have hPS := pieceS_empty hW
  have hv : content ω.v = ω.period := rfl
  have hcs : ∀ s : ℤ, content (s • eCell) = 0 := by intro s; simp [content, eCell]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; exact ((hkey z).mp hz).1
  · intro z hz; simp [hPE] at hz
  · intro z hz; simp [hPS] at hz
  · intro z hz; exact ((mem_pieceSE_empty hW).mp hz).1
  · intro z hz
    by_cases hz' : z - eCell ∈ ω.E
    · exact Or.inr (Or.inr (Or.inr ((mem_pieceSE_empty hW).mpr ⟨hz, hz'⟩)))
    · exact Or.inl ((hkey z).mpr ⟨hz, hz'⟩)
  · intro z hz
    have := (hkey z).mp hz
    refine ⟨by simp [hPE], by simp [hPS], fun hh => this.2 ((mem_pieceSE_empty hW).mp hh).2⟩
  · intro s _ z hz
    have := hrange z ((hkey z).mp hz).1
    intro hmem
    have := hrange _ hmem
    rw [content_sub, content_add, hv, hcs] at this
    omega
  · intro s hs z hz
    obtain ⟨hzE, hze⟩ := (hkey z).mp hz
    intro hmem
    apply hze
    have hsk := hE.1
    obtain ⟨a, b⟩ := z
    simp only [Prod.smul_mk, smul_eq_mul, eCell, mul_one, Prod.mk_sub_mk] at hmem ⊢
    exact hsk.mem (a := a - s) (b := b - s) (c := a) (d := b) hmem hzE (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · intro s hs z hz
    have := hrange z ((hkey z).mp hz).1
    intro hmem
    have := hrange _ hmem
    rw [sub_add_eq_sub_sub, sub_neg_eq_add, content_sub, content_add, hv, hcs] at this
    omega
  · intro z hz; simp [hPE] at hz
  · intro z hz; simp [hPS] at hz
  · intro z hz; exact ((mem_pieceSE_empty hW).mp hz).2
  · intro z hz; simp [hPS] at hz
  · intro z hz
    obtain ⟨hz1, hz2⟩ := (mem_pieceSE_empty hW).mp hz
    have r1 := hrange z hz1
    have r2 := hrange _ hz2
    rw [content_sub_eCell] at r2
    rw [hw0]
    have hne : ∀ y : ℤ × ℤ, y = y - eCell → False := by
      intro y hy
      have := congrArg Prod.fst hy
      simp [eCell] at this
      omega
    refine ⟨?_, ?_⟩
    · by_contra hcon
      have e1 : z = sw ω.E := eq_sw_of_content hE hz1 (by omega)
      have e2 : z - eCell = sw ω.E :=
        eq_sw_of_content hE hz2 (by rw [content_sub_eCell]; omega)
      exact hne z (e1.trans e2.symm)
    · by_contra hcon
      have e1 : z = ne ω.E := eq_ne_of_content hE hz1 (by rw [hmax]; omega)
      have e2 : z - eCell = ne ω.E :=
        eq_ne_of_content hE hz2 (by rw [content_sub_eCell, hmax]; omega)
      exact hne z (e1.trans e2.symm)
  · intro z hz; simp [hPE] at hz

/-- **The facts about one copy of `E`** for every legal mark of case (a). -/
theorem edgeLocal (h : ω.IsLegal) (hc : ω.case = .a) : EdgeLocal ω := by
  by_cases hW : ω.W = ∅
  · exact edgeLocal_empty h hW
  · exact edgeLocal_nonempty ⟨h, Finset.nonempty_iff_ne_empty.mpr hW⟩ hc

end EsDiff

end Plan

end SkewMarkedFactor.Gluing
