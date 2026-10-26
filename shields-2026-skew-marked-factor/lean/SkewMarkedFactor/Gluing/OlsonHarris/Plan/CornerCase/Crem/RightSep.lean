/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/RightSep.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem.RightCells
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem.Ranges

/-!
# The pieces of the remainder after removing a right ribbon lie on separated diagonals

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the edge-disjointness of the union in thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), for a ribbon `windowRibbon D j₀ m` removable on the right.

The cells of `(D \ A) ∘_ω E`, the copies of `\overline O`, those of `W` and those of
`\overline W` lie on diagonals at distance at least `2` from one another (`right_sep_*`), so
`s` of the remainder is the product of their functions (`cellSchur_right_remainder`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

namespace Rem

set_option linter.unusedSectionVars false

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner} {D : Diagram} {j0 : ℤ} {m : ℕ}

theorem right_decomp (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) (hw : RightWindow D j0 m) :
    ω.compose D \ cornerLift ω D m s (windowRibbon D j0 m) =
      Fp ω (D \ windowRibbon D j0 m) ∪ rPieceO ω D j0 m ∪ rPieceW ω D j0 m ∪
        rPieceN ω D j0 m := by
  have hq0 : 0 < ω.period := by
    have := h.width_lt_period
    have := h.width_pos
    omega
  ext x
  obtain ⟨J, a, r, ha0, haq, rfl⟩ := exists_block ω hq0 x
  rw [right_cell_iff h hc hph hw ha0 haq]
  simp only [Finset.mem_union]
  tauto

/-! ### Local facts on the single-cell diagonals of the window -/

theorem rLoneW_pred_not_mem (hw : RightWindow D j0 m) {j : ℤ} (hj : j ∈ rLoneW D j0 m) :
    j - 1 ∉ contents (D \ windowRibbon D j0 m) := by
  obtain ⟨hmem, hhl, hbl, hbh, hend⟩ := outer_facts hw.conn
  rw [mem_rLoneW hw.conn.1, mem_rLone, hmem] at hj
  rw [contents_X hw, hmem]
  have hw0 := (hmem j0).mp hw.start
  have hw1 := (hmem (j0 + (m : ℤ) - 1)).mp hw.stop
  have hS := hw.startEnd
  rw [hmem] at hS
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj
  rintro ⟨hC, hnot⟩
  obtain ⟨b1a, b1b⟩ := hbl j hC.1 (by omega)
  obtain ⟨b2a, b2b⟩ := hbh j hC.1 (by omega)
  have hl1 := hhl (j - 1) hC.1 hC.2
  have hl0 := hhl j (by omega) (by omega)
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · omega
  · omega

theorem rLoneN_succ_not_mem (hw : RightWindow D j0 m) {j : ℤ} (hj : j ∈ rLoneN D j0 m) :
    j + 1 ∉ contents (D \ windowRibbon D j0 m) := by
  obtain ⟨hmem, hhl, hbl, hbh, hend⟩ := outer_facts hw.conn
  rw [mem_rLoneN hw.conn.1, mem_rLone, hmem] at hj
  rw [contents_X hw, hmem]
  have hw0 := (hmem j0).mp hw.start
  have hw1 := (hmem (j0 + (m : ℤ) - 1)).mp hw.stop
  have hT := hw.stopEnd
  rw [hmem] at hT
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj
  rintro ⟨hC, hnot⟩
  obtain ⟨b1a, b1b⟩ := hbl (j + 1) (by omega) hC.2
  obtain ⟨b2a, b2b⟩ := hbh (j + 1) (by omega) hC.2
  have hl1 := hhl (j + 1) hC.1 hC.2
  have hl0 := hhl j (by omega) (by omega)
  simp only [add_sub_cancel_right] at b1a b1b b2a b2b hT
  rcases eq_or_lt_of_le (show j + 1 ≤ j0 + (m : ℤ) by omega) with he | hlt
  · rw [← he] at hT
    simp only [add_sub_cancel_right] at hT
    omega
  · omega

theorem not_rLoneW_and_pred_rLoneN (hw : RightWindow D j0 m) {j : ℤ} (hj : j ∈ rLoneW D j0 m)
    (hj' : j - 1 ∈ rLoneN D j0 m) : False := by
  obtain ⟨hmem, hhl, hbl, hbh, hend⟩ := outer_facts hw.conn
  rw [mem_rLoneW hw.conn.1, mem_rLone, hmem] at hj
  rw [mem_rLoneN hw.conn.1, mem_rLone, sub_add_cancel, hmem] at hj'
  have hw0 := (hmem j0).mp hw.start
  have hw1 := (hmem (j0 + (m : ℤ) - 1)).mp hw.stop
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj
  obtain ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩ := hj'
  obtain ⟨b1a, b1b⟩ := hbl j (by omega) (by omega)
  obtain ⟨b2a, b2b⟩ := hbh j (by omega) (by omega)
  have hl1 := hhl (j - 1) (by omega) (by omega)
  have hl0 := hhl j (by omega) (by omega)
  omega

theorem lone_flat {j : ℤ} (h : (j0 ≤ j ∧ j < j0 + (m : ℤ)) ∧ diagLo D j = diagHi D j) :
    j0 ≤ j ∧ j < j0 + (m : ℤ) ∧ diagLo D j = diagHi D j := ⟨h.1.1, h.1.2, h.2⟩

theorem fp_block (h : ω.IsLegalNonempty) {X : Diagram} {x : ℤ × ℤ} (hx : x ∈ Fp ω X) :
    ∃ j ∈ contents X, minContent ω.E + j * ω.period ≤ content x ∧
      content x ≤ minContent ω.E + j * ω.period + ω.period + ω.widthZ - 1 := by
  unfold Fp at hx
  by_cases hXe : X = ∅
  · simp [hXe] at hx
  · simp only [hXe, ↓reduceIte] at hx
    exact content_compose_block h (Finset.nonempty_iff_ne_empty.mpr hXe) hx

theorem sep_fp (h : ω.IsLegalNonempty) {X S : Diagram} {lo hi : ℤ} (hS : CIn S lo hi)
    (hfar : ∀ j ∈ contents X, minContent ω.E + j * ω.period + ω.period + ω.widthZ - 1 + 2 ≤ lo ∨
      hi + 2 ≤ minContent ω.E + j * ω.period) : Sep (Fp ω X) S := by
  intro x hx y hy
  obtain ⟨j, hj, h1, h2⟩ := fp_block h hx
  have := hS y hy
  rcases hfar j hj with h3 | h3
  · rw [abs_of_nonpos (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]; omega

section RightSepPieces

variable (h : ω.IsLegalNonempty) (hw : RightWindow D j0 m)

include h hw

theorem right_sep_FpO : Sep (Fp ω (D \ windowRibbon D j0 m)) (rPieceO ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceO
  refine sep_biUnion_right fun j hj => ?_
  refine sep_fp h (cin_translate_smul (cin_hatMiddleFin h) j) fun j' hj' => ?_
  have hne : j' ≠ j := by
    rintro rfl
    rw [contents_X hw] at hj'
    exact hj'.2 (lone_flat (mem_rLone.mp hj))
  obtain ⟨f1, f2, f3, f4⟩ := far_facts hq0 j j'
  rcases lt_or_gt_of_ne hne with hl | hg
  · have := f1 hl; left; omega
  · have := f2 hg; right; omega

theorem right_sep_FpW : Sep (Fp ω (D \ windowRibbon D j0 m)) (rPieceW ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceW
  refine sep_biUnion_right fun j hj => ?_
  refine sep_fp h (cin_translate_smul (cin_W h) j) fun j' hj' => ?_
  have hne : j' ≠ j := by
    rintro rfl
    rw [contents_X hw] at hj'
    exact hj'.2 (lone_flat (mem_rLone.mp (Finset.mem_filter.mp hj).1))
  have hne1 : j' ≠ j - 1 := by
    rintro rfl
    exact rLoneW_pred_not_mem hw hj hj'
  obtain ⟨f1, f2, f3, f4⟩ := far_facts hq0 j j'
  rcases lt_or_gt_of_ne hne with hl | hg
  · have : j' + 1 < j := by omega
    have := f3 this; left; omega
  · have := f2 hg; right; omega

theorem right_sep_FpN (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) :
    Sep (Fp ω (D \ windowRibbon D j0 m)) (rPieceN ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceN
  refine sep_biUnion_right fun j hj => ?_
  refine sep_fp h (cin_translate_smul (cin_hatMarkFin h hc hph) (j + 1)) fun j' hj' => ?_
  have hne : j' ≠ j := by
    rintro rfl
    rw [contents_X hw] at hj'
    exact hj'.2 (lone_flat (mem_rLone.mp (Finset.mem_filter.mp hj).1))
  have hne1 : j' ≠ j + 1 := by
    rintro rfl
    exact rLoneN_succ_not_mem hw hj hj'
  obtain ⟨f1, f2, f3, f4⟩ := far_facts hq0 j j'
  have e : (j + 1) * ω.period = j * ω.period + ω.period := by ring
  rcases lt_or_gt_of_ne hne with hl | hg
  · have := f1 hl; left; omega
  · have : j + 1 < j' := by omega
    have := f4 this; right; omega

end RightSepPieces


section RightProduct

variable (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
  (hw : RightWindow D j0 m)

include h hc hph hw

theorem right_sep_OW : Sep (rPieceO ω D j0 m) (rPieceW ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceO rPieceW
  refine sep_biUnion_biUnion fun j _ j' _ => ?_
  exact sep_blocks (q := ω.period) hq0 (cin_translate_smul (cin_hatMiddleFin h) j)
    (cin_translate_smul (cin_W h) j') (α := ω.widthZ + 1) (β := ω.period - 2) (α' := 0)
    (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j) (j' := j') (by ring) (by ring) (by ring)
    (by ring) (by omega) (by omega) (fun _ => Or.inr (by omega))

theorem right_sep_ON : Sep (rPieceO ω D j0 m) (rPieceN ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceO rPieceN
  refine sep_biUnion_biUnion fun j _ j' _ => ?_
  exact sep_blocks (q := ω.period) hq0 (cin_translate_smul (cin_hatMiddleFin h) j)
    (cin_translate_smul (cin_hatMarkFin h hc hph) (j' + 1)) (α := ω.widthZ + 1)
    (β := ω.period - 2) (α' := 0) (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j)
    (j' := j' + 1) (by ring) (by ring) (by ring) (by ring) (by omega) (by omega)
    (fun _ => Or.inr (by omega))

theorem right_sep_WN : Sep (rPieceW ω D j0 m) (rPieceN ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceW rPieceN
  refine sep_biUnion_biUnion fun j hj j' hj' => ?_
  refine sep_blocks (q := ω.period) hq0 (cin_translate_smul (cin_W h) j)
    (cin_translate_smul (cin_hatMarkFin h hc hph) (j' + 1)) (α := 0) (β := ω.widthZ - 1)
    (α' := 0) (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j) (j' := j' + 1) (by ring)
    (by ring) (by ring) (by ring) (by omega) (by omega) (fun he => ?_)
  exfalso
  have : j' = j - 1 := by omega
  subst this
  exact not_rLoneW_and_pred_rLoneN hw hj hj'

theorem right_sep_OO : ∀ j ∈ rLone D j0 m, ∀ j' ∈ rLone D j0 m, j ≠ j' →
    Sep (translate (j • ω.v) (hatMiddleFin ω)) (translate (j' • ω.v) (hatMiddleFin ω)) := by
  intro j _ j' _ hne
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  exact sep_blocks (q := ω.period) (by omega) (cin_translate_smul (cin_hatMiddleFin h) j)
    (cin_translate_smul (cin_hatMiddleFin h) j') (α := ω.widthZ + 1) (β := ω.period - 2)
    (α' := ω.widthZ + 1) (β' := ω.period - 2) (c0 := minContent ω.E) (j := j) (j' := j')
    (by ring) (by ring) (by ring) (by ring) (by omega) (by omega) (fun e => absurd e hne)

theorem right_sep_WW : ∀ j ∈ rLoneW D j0 m, ∀ j' ∈ rLoneW D j0 m, j ≠ j' →
    Sep (translate (j • ω.v) ω.W) (translate (j' • ω.v) ω.W) := by
  intro j _ j' _ hne
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  exact sep_blocks (q := ω.period) (by omega) (cin_translate_smul (cin_W h) j)
    (cin_translate_smul (cin_W h) j') (α := 0) (β := ω.widthZ - 1) (α' := 0)
    (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j) (j' := j') (by ring) (by ring)
    (by ring) (by ring) (by omega) (by omega) (fun e => absurd e hne)

theorem right_sep_NN : ∀ j ∈ rLoneN D j0 m, ∀ j' ∈ rLoneN D j0 m, j ≠ j' →
    Sep (translate ((j + 1) • ω.v) (hatMarkFin ω)) (translate ((j' + 1) • ω.v) (hatMarkFin ω)) := by
  intro j _ j' _ hne
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  exact sep_blocks (q := ω.period) (by omega) (cin_translate_smul (cin_hatMarkFin h hc hph) (j + 1))
    (cin_translate_smul (cin_hatMarkFin h hc hph) (j' + 1)) (α := 0) (β := ω.widthZ - 1)
    (α' := 0) (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j + 1) (j' := j' + 1)
    (by ring) (by ring) (by ring) (by ring) (by omega) (by omega)
    (fun e => absurd (by omega) hne)

/-- **`s` of the remainder after removing the lift of a right ribbon**: the product of `s` of the
composite of `D \ A`, and of the powers of `s_{\overline O}`, `s_W`, `s_{\overline W}`. -/
theorem cellSchur_right_remainder :
    cellSchur (ω.compose D \ cornerLift ω D m s (windowRibbon D j0 m)) =
      cellSchur (Fp ω (D \ windowRibbon D j0 m)) *
        cellSchur (hatMiddleFin ω) ^ (rLone D j0 m).card * cellSchur ω.W ^ (rLoneW D j0 m).card *
          cellSchur (hatMarkFin ω) ^ (rLoneN D j0 m).card := by
  rw [right_decomp h hc hph hw]
  have sFO := right_sep_FpO h hw
  have sFW := right_sep_FpW h hw
  have sFN := right_sep_FpN h hw hc hph
  have sOW := right_sep_OW h hc hph hw
  have sON := right_sep_ON h hc hph hw
  have sWN := right_sep_WN h hc hph hw
  rw [cellSchur_union_of_sep (Sep.union_left (Sep.union_left sFN sON) sWN),
    cellSchur_union_of_sep (Sep.union_left sFW sOW), cellSchur_union_of_sep sFO]
  have eO : cellSchur (rPieceO ω D j0 m) = cellSchur (hatMiddleFin ω) ^ (rLone D j0 m).card := by
    unfold rPieceO
    rw [cellSchur_biUnion_sep _ _ (right_sep_OO h hc hph hw)]
    rw [Finset.prod_congr rfl (fun j _ => cellSchur_translate _ _), Finset.prod_const]
  have eW : cellSchur (rPieceW ω D j0 m) = cellSchur ω.W ^ (rLoneW D j0 m).card := by
    unfold rPieceW
    rw [cellSchur_biUnion_sep _ _ (right_sep_WW h hc hph hw)]
    rw [Finset.prod_congr rfl (fun j _ => cellSchur_translate _ _), Finset.prod_const]
  have eN : cellSchur (rPieceN ω D j0 m) = cellSchur (hatMarkFin ω) ^ (rLoneN D j0 m).card := by
    unfold rPieceN
    rw [cellSchur_biUnion_sep _ _ (right_sep_NN h hc hph hw)]
    rw [Finset.prod_congr rfl (fun j _ => cellSchur_translate _ _), Finset.prod_const]
  rw [eO, eW, eN]

end RightProduct


end Rem

end Corner

end Plan

end SkewMarkedFactor.Gluing
