-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/LeftSep.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.LeftCells
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.RightSep

/-!
# The pieces of the remainder after removing a left ribbon lie on separated diagonals

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the edge-disjointness of the union in thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), for a ribbon `leftStrip D j₀ m` removable on the left.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem

set_option linter.unusedSectionVars false

open MarkedInner

attribute [local instance 10] Classical.propDecidable

variable {ω : MarkedInner} {D : Diagram} {j0 : ℤ} {m : ℕ}

theorem left_decomp (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) (hw : LeftWindow D j0 m) :
    ω.compose D \ cornerLift ω D m t (leftStrip D j0 m) =
      Fp ω (D \ leftStrip D j0 m) ∪ rPieceO ω D j0 m ∪ lPieceU ω D j0 m ∪
        lPieceS ω D j0 m := by
  have hq0 : 0 < ω.period := by
    have := h.width_lt_period
    have := h.width_pos
    omega
  ext x
  obtain ⟨J, a, r, ha0, haq, rfl⟩ := exists_block ω hq0 x
  rw [left_cell_iff h hc hph hw ha0 haq]
  simp only [Finset.mem_union]
  tauto

theorem lLoneE_succ_not_mem (hw : LeftWindow D j0 m) {j : ℤ} (hj : j ∈ lLoneE D j0 m) :
    j + 1 ∉ contents (D \ leftStrip D j0 m) := by
  obtain ⟨hmem, hhl, hbl, hbh, hend⟩ := outer_facts hw.conn
  rw [mem_lLoneE hw.conn.1, mem_rLone, hmem] at hj
  rw [contents_XL hw, hmem]
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
  simp only [add_sub_cancel_right] at b1a b1b b2a b2b
  rcases eq_or_lt_of_le (show j + 1 ≤ j0 + (m : ℤ) by omega) with he | hlt
  · rw [← he] at hT
    simp only [add_sub_cancel_right] at hT
    omega
  · omega

theorem lLoneS_pred_not_mem (hw : LeftWindow D j0 m) {j : ℤ} (hj : j ∈ lLoneS D j0 m) :
    j - 1 ∉ contents (D \ leftStrip D j0 m) := by
  obtain ⟨hmem, hhl, hbl, hbh, hend⟩ := outer_facts hw.conn
  rw [mem_lLoneS hw.conn.1, mem_rLone, hmem] at hj
  rw [contents_XL hw, hmem]
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

theorem not_lLoneE_and_succ_lLoneS (hw : LeftWindow D j0 m) {j : ℤ} (hj : j ∈ lLoneE D j0 m)
    (hj' : j + 1 ∈ lLoneS D j0 m) : False := by
  obtain ⟨hmem, hhl, hbl, hbh, hend⟩ := outer_facts hw.conn
  rw [mem_lLoneE hw.conn.1, mem_rLone, hmem] at hj
  rw [mem_lLoneS hw.conn.1, mem_rLone, add_sub_cancel_right, hmem] at hj'
  have hw0 := (hmem j0).mp hw.start
  have hw1 := (hmem (j0 + (m : ℤ) - 1)).mp hw.stop
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj
  obtain ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩ := hj'
  obtain ⟨b1a, b1b⟩ := hbl (j + 1) (by omega) (by omega)
  obtain ⟨b2a, b2b⟩ := hbh (j + 1) (by omega) (by omega)
  have hl1 := hhl j (by omega) (by omega)
  have hl0 := hhl (j + 1) (by omega) (by omega)
  simp only [add_sub_cancel_right] at b1a b1b b2a b2b
  omega

section LeftProduct

variable (h : ω.IsLegalNonempty) (hw : LeftWindow D j0 m)

include h hw

theorem left_sep_FpO : Sep (Fp ω (D \ leftStrip D j0 m)) (rPieceO ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceO
  refine sep_biUnion_right fun j hj => ?_
  refine sep_fp h (cin_translate_smul (cin_hatMiddleFin h) j) fun j' hj' => ?_
  have hne : j' ≠ j := by
    rintro rfl
    rw [contents_XL hw] at hj'
    exact hj'.2 (lone_flat (mem_rLone.mp hj))
  obtain ⟨f1, f2, f3, f4⟩ := far_facts hq0 j j'
  rcases lt_or_gt_of_ne hne with hl | hg
  · have := f1 hl; left; omega
  · have := f2 hg; right; omega

theorem left_sep_FpU : Sep (Fp ω (D \ leftStrip D j0 m)) (lPieceU ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold lPieceU
  refine sep_biUnion_right fun j hj => ?_
  refine sep_fp h (cin_translate_smul (cin_W h) (j + 1)) fun j' hj' => ?_
  have hne : j' ≠ j := by
    rintro rfl
    rw [contents_XL hw] at hj'
    exact hj'.2 (lone_flat (mem_rLone.mp (Finset.mem_filter.mp hj).1))
  have hne1 : j' ≠ j + 1 := by
    rintro rfl
    exact lLoneE_succ_not_mem hw hj hj'
  obtain ⟨f1, f2, f3, f4⟩ := far_facts hq0 j j'
  have e : (j + 1) * ω.period = j * ω.period + ω.period := by ring
  rcases lt_or_gt_of_ne hne with hl | hg
  · have := f1 hl; left; omega
  · have : j + 1 < j' := by omega
    have := f4 this; right; omega

theorem left_sep_FpS (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) :
    Sep (Fp ω (D \ leftStrip D j0 m)) (lPieceS ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold lPieceS
  refine sep_biUnion_right fun j hj => ?_
  refine sep_fp h (cin_translate_smul (cin_hatMarkFin h hc hph) j) fun j' hj' => ?_
  have hne : j' ≠ j := by
    rintro rfl
    rw [contents_XL hw] at hj'
    exact hj'.2 (lone_flat (mem_rLone.mp (Finset.mem_filter.mp hj).1))
  have hne1 : j' ≠ j - 1 := by
    rintro rfl
    exact lLoneS_pred_not_mem hw hj hj'
  obtain ⟨f1, f2, f3, f4⟩ := far_facts hq0 j j'
  rcases lt_or_gt_of_ne hne with hl | hg
  · have : j' + 1 < j := by omega
    have := f3 this; left; omega
  · have := f2 hg; right; omega

end LeftProduct

section LeftProduct2

variable (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
  (hw : LeftWindow D j0 m)

include h hc hph hw

theorem left_sep_OU : Sep (rPieceO ω D j0 m) (lPieceU ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceO lPieceU
  refine sep_biUnion_biUnion fun j _ j' _ => ?_
  exact sep_blocks (q := ω.period) hq0 (cin_translate_smul (cin_hatMiddleFin h) j)
    (cin_translate_smul (cin_W h) (j' + 1)) (α := ω.widthZ + 1) (β := ω.period - 2) (α' := 0)
    (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j) (j' := j' + 1) (by ring) (by ring)
    (by ring) (by ring) (by omega) (by omega) (fun _ => Or.inr (by omega))

theorem left_sep_OS : Sep (rPieceO ω D j0 m) (lPieceS ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold rPieceO lPieceS
  refine sep_biUnion_biUnion fun j _ j' _ => ?_
  exact sep_blocks (q := ω.period) hq0 (cin_translate_smul (cin_hatMiddleFin h) j)
    (cin_translate_smul (cin_hatMarkFin h hc hph) j') (α := ω.widthZ + 1) (β := ω.period - 2)
    (α' := 0) (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j) (j' := j') (by ring)
    (by ring) (by ring) (by ring) (by omega) (by omega) (fun _ => Or.inr (by omega))

theorem left_sep_US : Sep (lPieceU ω D j0 m) (lPieceS ω D j0 m) := by
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  have hq0 : 0 < ω.period := by omega
  unfold lPieceU lPieceS
  refine sep_biUnion_biUnion fun j hj j' hj' => ?_
  refine sep_blocks (q := ω.period) hq0 (cin_translate_smul (cin_W h) (j + 1))
    (cin_translate_smul (cin_hatMarkFin h hc hph) j') (α := 0) (β := ω.widthZ - 1)
    (α' := 0) (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j + 1) (j' := j') (by ring)
    (by ring) (by ring) (by ring) (by omega) (by omega) (fun he => ?_)
  exfalso
  subst he
  exact not_lLoneE_and_succ_lLoneS hw hj hj'

theorem left_sep_UU : ∀ j ∈ lLoneE D j0 m, ∀ j' ∈ lLoneE D j0 m, j ≠ j' →
    Sep (translate ((j + 1) • ω.v) ω.W) (translate ((j' + 1) • ω.v) ω.W) := by
  intro j _ j' _ hne
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  exact sep_blocks (q := ω.period) (by omega) (cin_translate_smul (cin_W h) (j + 1))
    (cin_translate_smul (cin_W h) (j' + 1)) (α := 0) (β := ω.widthZ - 1) (α' := 0)
    (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j + 1) (j' := j' + 1) (by ring) (by ring)
    (by ring) (by ring) (by omega) (by omega) (fun e => absurd (by omega) hne)

theorem left_sep_SS : ∀ j ∈ lLoneS D j0 m, ∀ j' ∈ lLoneS D j0 m, j ≠ j' →
    Sep (translate (j • ω.v) (hatMarkFin ω)) (translate (j' • ω.v) (hatMarkFin ω)) := by
  intro j _ j' _ hne
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  exact sep_blocks (q := ω.period) (by omega) (cin_translate_smul (cin_hatMarkFin h hc hph) j)
    (cin_translate_smul (cin_hatMarkFin h hc hph) j') (α := 0) (β := ω.widthZ - 1) (α' := 0)
    (β' := ω.widthZ - 1) (c0 := minContent ω.E) (j := j) (j' := j') (by ring) (by ring)
    (by ring) (by ring) (by omega) (by omega) (fun e => absurd e hne)

theorem left_sep_OO : ∀ j ∈ rLone D j0 m, ∀ j' ∈ rLone D j0 m, j ≠ j' →
    Sep (translate (j • ω.v) (hatMiddleFin ω)) (translate (j' • ω.v) (hatMiddleFin ω)) := by
  intro j _ j' _ hne
  have hq := h.width_lt_period
  have hw1 := h.width_pos
  exact sep_blocks (q := ω.period) (by omega) (cin_translate_smul (cin_hatMiddleFin h) j)
    (cin_translate_smul (cin_hatMiddleFin h) j') (α := ω.widthZ + 1) (β := ω.period - 2)
    (α' := ω.widthZ + 1) (β' := ω.period - 2) (c0 := minContent ω.E) (j := j) (j' := j')
    (by ring) (by ring) (by ring) (by ring) (by omega) (by omega) (fun e => absurd e hne)

/-- **`s` of the remainder after removing the lift of a left ribbon**: the product of `s` of the
composite of `D \ A`, and of the powers of `s_{\overline O}`, `s_W`, `s_{\overline W}`. -/
theorem cellSchur_left_remainder :
    cellSchur (ω.compose D \ cornerLift ω D m t (leftStrip D j0 m)) =
      cellSchur (Fp ω (D \ leftStrip D j0 m)) *
        cellSchur (hatMiddleFin ω) ^ (rLone D j0 m).card * cellSchur ω.W ^ (lLoneE D j0 m).card *
          cellSchur (hatMarkFin ω) ^ (lLoneS D j0 m).card := by
  rw [left_decomp h hc hph hw]
  have sFO := left_sep_FpO h hw
  have sFU := left_sep_FpU h hw
  have sFS := left_sep_FpS h hw hc hph
  have sOU := left_sep_OU h hc hph hw
  have sOS := left_sep_OS h hc hph hw
  have sUS := left_sep_US h hc hph hw
  rw [cellSchur_union_of_sep (Sep.union_left (Sep.union_left sFS sOS) sUS),
    cellSchur_union_of_sep (Sep.union_left sFU sOU), cellSchur_union_of_sep sFO]
  have eO : cellSchur (rPieceO ω D j0 m) = cellSchur (hatMiddleFin ω) ^ (rLone D j0 m).card := by
    unfold rPieceO
    rw [cellSchur_biUnion_sep _ _ (left_sep_OO h hc hph hw)]
    rw [Finset.prod_congr rfl (fun j _ => cellSchur_translate _ _), Finset.prod_const]
  have eU : cellSchur (lPieceU ω D j0 m) = cellSchur ω.W ^ (lLoneE D j0 m).card := by
    unfold lPieceU
    rw [cellSchur_biUnion_sep _ _ (left_sep_UU h hc hph hw)]
    rw [Finset.prod_congr rfl (fun j _ => cellSchur_translate _ _), Finset.prod_const]
  have eS : cellSchur (lPieceS ω D j0 m) = cellSchur (hatMarkFin ω) ^ (lLoneS D j0 m).card := by
    unfold lPieceS
    rw [cellSchur_biUnion_sep _ _ (left_sep_SS h hc hph hw)]
    rw [Finset.prod_congr rfl (fun j _ => cellSchur_translate _ _), Finset.prod_const]
  rw [eO, eU, eS]

end LeftProduct2

end Rem

end Corner

end Plan

end GluingCore
