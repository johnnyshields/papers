/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalV
import SkewClassInflation.InflateLegalA
import SkewClassInflation.InflateLegalAnti
import SkewGluing.Antitranspose

/-!
# Vertical inflation of a legal case-(a) mark, and inflation of a case-(b) mark

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, case (b),
\(0<w<q-1\).  Under the two private pinches, the vertical inflation of a legal case-(a) mark is
a legal case-(a) mark of width \(w+1\) and phases \((\sigma,\tau+1)\).  Antitransposition carries
the east inflation of a case-(b) mark to this vertical inflation.  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

/-- Vertical inflation of the inner and the mark, keeping the displacement and the case. -/
def vInflateMarked (ω : MarkedInner) : MarkedInner where
  E := vInflateCells ω.E
  W := vInflateCells ω.W
  v := ω.v
  case := ω.case

theorem vInflateCells_translate (v : ℤ × ℤ) (D : Diagram) :
    vInflateCells (SkewGluing.translate v D) = SkewGluing.translate v (vInflateCells D) := by
  unfold vInflateCells SkewGluing.translate
  rw [Finset.image_union, Finset.image_image, Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro x _
  simp only [Function.comp]
  exact add_right_comm _ _ _

theorem vInflateMarked_translate (u : ℤ × ℤ) (ω : MarkedInner) :
    vInflateMarked (ω.translate u) = (vInflateMarked ω).translate u := by
  refine MarkedInner.mk.injEq .. |>.mpr ⟨?_, ?_, rfl, rfl⟩
  · exact vInflateCells_translate u ω.E
  · exact vInflateCells_translate u ω.W

theorem vInflateMarked_W_nonempty (h : ω.W.Nonempty) : (vInflateMarked ω).W.Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, Finset.mem_union_left _ hx⟩

/-- The extra cap equalities of a legal case-(a) mark used by the vertical inflation. -/
theorem vcaps_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) :
    ω.lo (ω.period - 1) = ω.lo 0 + ω.rowShift ∧
      ω.hi (ω.period + ω.widthZ - 1) = ω.hi ω.widthZ + ω.rowShift := by
  have hpa := h.attach.1 hc
  have cu := (h.upper_caps_H hpa.2).2.2
  have cl := (h.lower_caps_H hpa.1).2.2
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold dLo at cu
  unfold dHi at cl
  simp only [zero_add] at cu
  refine ⟨by omega, ?_⟩
  rw [show ω.period + ω.widthZ - 1 = ω.widthZ - 1 + ω.period by ring]
  omega

/-- The vertical inflation of the normalized legal case-(a) mark is the slot mark of the
vertically inflated data. -/
theorem vInflateMarked_translate_eq_mark (h : ω.IsLegalNonempty) (hc : ω.case = .a)
    {s t : ℤ} (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (hc1 : ω.lo (ω.widthZ - 1) = ω.lo ω.widthZ)
    (Y2 : ω.hi (ω.period + ω.widthZ - 1) = ω.hi ω.widthZ + ω.rowShift) :
    vInflateMarked (ω.translate (0, -minContent ω.E)) =
      SlotGeom.mark (vInflateCells (SkewGluing.translate (0, -minContent ω.E) ω.E))
        ω.period (ω.widthZ + 1) s ω.rowShift (hiV (ω.period + ω.widthZ - 1) ω.hi) := by
  have hs := slotGeom_a_of_legal h hc hp
  have hsh := hs.shape
  have hG := diagSet_E_of_legal h
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have hiw : ω.hi (ω.widthZ - 1) - (if s ≤ ω.widthZ - 1 then 1 else 0) = ω.hi ω.widthZ := by
    by_cases hsw : s ≤ ω.widthZ - 1
    · have := hs.ehi_ge (ω.widthZ - 1) hsw (by omega)
      rw [show ω.period + (ω.widthZ - 1) = ω.period + ω.widthZ - 1 by ring] at this
      simp only [hsw, ite_true]
      omega
    · have := hs.ehi_lt (ω.widthZ - 1) (by omega) (by omega)
      rw [show ω.period + (ω.widthZ - 1) = ω.period + ω.widthZ - 1 by ring] at this
      simp only [hsw, ite_false]
      omega
  refine MarkedInner.mk.injEq .. |>.mpr ⟨rfl, ?_, ?_, hc⟩
  · ext ⟨i, j⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by ring⟩
    change (i, i + k) ∈ vInflateCells (SkewGluing.translate (0, -minContent ω.E) ω.W) ↔
      (i, i + k) ∈ SkewGluing.SlotGeom.lowerCopy _ _ _ _
    unfold SlotGeom.lowerCopy
    have e : (i + 1, i + k) = (i + 1, i + 1 + (k - 1)) := by rw [show i + 1 + (k - 1) = i + k by ring]
    rw [Finset.mem_filter, mem_vInflateCells, e, translate_cell_mem, translate_cell_mem,
      mem_W_a h hc hp, mem_W_a h hc hp, diagSet_vinflate hG hsh i k]
    simp only [content, add_sub_cancel_left]
    have hne := hsh.ne
    have p1 := hs.pos
    by_cases hk0 : k < 0
    · constructor <;> intro hh <;> omega
    by_cases hk2 : ω.widthZ < k
    · constructor <;> intro hh <;> omega
    by_cases hk : k = 0
    · subst hk
      rw [loV_zero, hiV_of_le (by omega)]
      have := hne 0 le_rfl (by omega)
      simp only [show ¬ (s ≤ 0) by omega, ite_false] at *
      constructor
      · rintro (hh | hh)
        · exact ⟨⟨by omega, by omega, hh.2.2.1, by omega⟩, by omega, by omega⟩
        · omega
      · rintro ⟨⟨_, _, h3, h4⟩, _, h6⟩
        left
        exact ⟨le_rfl, by omega, h3, by omega⟩
    · have a1 := hsh.stepLo k (by omega) (by omega)
      have a2 := hsh.stepHi k (by omega) (by omega)
      have a3 := hne k (by omega) (by omega)
      have a4 := hne (k - 1) (by omega) (by omega)
      have a5 := p1 (k - 1) (by omega) (by omega)
      rw [loV_of_pos (by omega), hiV_of_le (by omega)]
      by_cases hkw : k = ω.widthZ
      · subst hkw
        constructor
        · rintro (hh | hh)
          · omega
          · refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, ?_⟩
            split_ifs at hh hiw ⊢ <;> omega
        · rintro ⟨⟨_, _, h3, h4⟩, _, h6⟩
          right
          refine ⟨by omega, by omega, by omega, ?_⟩
          split_ifs at h6 hiw ⊢ <;> omega
      · have a7 := p1 k (by omega) (by omega)
        have cB : k = s → ω.hi (k - 1) = ω.hi k := by
          rintro rfl
          exact hs.capB (by omega)
        constructor
        · rintro (hh | hh)
          · refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, ?_⟩
            split_ifs at hh ⊢ <;> omega
          · refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, ?_⟩
            split_ifs at hh a5 a7 ⊢ <;> omega
        · rintro ⟨⟨_, _, h3, h4⟩, _, h6⟩
          by_cases hi' : ω.lo k ≤ i
          · left
            refine ⟨by omega, by omega, hi', ?_⟩
            split_ifs at h6 ⊢ <;> omega
          · right
            refine ⟨by omega, by omega, by omega, ?_⟩
            split_ifs at h6 a5 a7 ⊢ <;> omega
  · exact ω.v_eq

/-- **Vertical inflation of a legal case-(a) mark.**  If the two private pinches hold and
\(w+1<q\), the vertically inflated mark is a legal case-(a) mark of the same period, width
\(w+1\) and middle phases \((\sigma,\tau+1)\). -/
theorem vInflate_isLegal_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) {s t : ℤ}
    (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (P1 : ω.hi (ω.widthZ + 1) = ω.hi ω.widthZ - 1)
    (P2 : ω.lo (ω.period - 2) = ω.lo (ω.period - 1) + 1) :
    (vInflateMarked ω).IsLegal ∧ (vInflateMarked ω).IsPhases s (t + 1) ∧
      (vInflateMarked ω).widthZ = ω.widthZ + 1 ∧ (vInflateMarked ω).period = ω.period ∧
      (vInflateMarked ω).case = .a := by
  have hs := slotGeom_a_of_legal h hc hp
  have hG := diagSet_E_of_legal h
  have hc1 := (caps_a h hc).1
  have hv := vcaps_a h hc
  have hs' := slotGeom_vinflate hs hw1 hv.1 hv.2 hc1 P1 P2
  have hG' : DiagSet (vInflateCells (SkewGluing.translate (0, -minContent ω.E) ω.E)) 0
      (ω.period + (ω.widthZ + 1) - 1) (loV ω.lo) (hiV (ω.period + ω.widthZ - 1) ω.hi) := by
    have := diagSet_vinflate hG hs.shape
    rwa [show ω.period + ω.widthZ - 1 + 1 = ω.period + (ω.widthZ + 1) - 1 by ring] at this
  have heq := vInflateMarked_translate_eq_mark h hc hp hw1 hc1 hv.2
  rw [vInflateMarked_translate] at heq
  have hleg := SlotGeom.mark_isLegal hG' hs'
  rw [← heq] at hleg
  have hleg' : (vInflateMarked ω).IsLegal := (isLegal_translate_iff _).mp hleg
  have hne : (vInflateMarked ω).IsLegalNonempty := ⟨hleg', vInflateMarked_W_nonempty h.2⟩
  refine ⟨hleg', ?_, ?_, rfl, hc⟩
  · rw [← isPhases_translate_iff hne (0, -minContent ω.E), heq]
    exact SlotGeom.mark_phases hG' hs'
  · have := SlotGeom.mark_width hG' hs'
    rw [← heq] at this
    unfold MarkedInner.widthZ
    rw [← width_translate (0, -minContent ω.E) (vInflateMarked ω)]
    exact this

theorem antitranspose_vInflateCells (D : Diagram) :
    antitranspose (vInflateCells (antitranspose D)) = inflateCells D := by
  ext ⟨a, b⟩
  rw [mem_antitranspose, mem_vInflateCells, mem_antitranspose, mem_antitranspose, mem_inflateCells]
  constructor
  · rintro (h | h)
    · left; simpa using h
    · right
      convert h using 2 <;> simp <;> ring
  · rintro (h | h)
    · left; simpa using h
    · right
      convert h using 2 <;> simp <;> ring

theorem inflateMarked_eq_anti (ω : MarkedInner) :
    inflateMarked ω = (vInflateMarked ω.anti).anti := by
  refine MarkedInner.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
  · change inflateCells ω.E = antitranspose (vInflateCells (antitranspose ω.E))
    rw [antitranspose_vInflateCells]
  · change inflateCells ω.W = antitranspose (vInflateCells (antitranspose ω.W))
    rw [antitranspose_vInflateCells]
  · change ω.v = atVec (atVec ω.v)
    rw [atVec_atVec]
  · change ω.case = ω.case.anti.anti
    rw [AttachCase.anti_anti]

/-- **Inflation of a legal case-(b) mark.**  If the two private pinches hold and \(w+1<q\), the
inflated mark is a legal case-(b) mark of the same period, width \(w+1\) and middle phases
\((\sigma,\tau+1)\). -/
theorem inflate_isLegal_b (h : ω.IsLegalNonempty) (hc : ω.case = .b) {s t : ℤ}
    (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (h1 : ω.lo (ω.widthZ + 1) = ω.lo ω.widthZ)
    (h2 : ω.hi (ω.period - 2) = ω.hi (ω.period - 1)) :
    (inflateMarked ω).IsLegal ∧ (inflateMarked ω).IsPhases s (t + 1) ∧
      (inflateMarked ω).widthZ = ω.widthZ + 1 ∧ (inflateMarked ω).period = ω.period ∧
      (inflateMarked ω).case = .b := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hα : ω.anti.IsLegalNonempty :=
    ⟨isLegal_anti h.1 h.2, antitranspose_nonempty_iff.mpr h.2⟩
  have hcα : ω.anti.case = .a := by
    rw [anti_case, hc]; rfl
  have hpα : ω.anti.IsPhases s t := (isPhases_anti h).mpr hp
  have hw1α : ω.anti.widthZ + 1 < ω.anti.period := by
    rw [widthZ_anti, period_anti]; exact hw1
  have P1 : ω.anti.hi (ω.anti.widthZ + 1) = ω.anti.hi ω.anti.widthZ - 1 := by
    rw [widthZ_anti, anti_hi h (by omega) (by omega), anti_hi h (by omega) (by omega)]
    omega
  have P2 : ω.anti.lo (ω.anti.period - 2) = ω.anti.lo (ω.anti.period - 1) + 1 := by
    rw [period_anti, anti_lo h (by omega) (by omega), anti_lo h (by omega) (by omega)]
    omega
  obtain ⟨leg, ph, wd, -, -⟩ := vInflate_isLegal_a hα hcα hpα hw1α P1 P2
  have hneβ : (vInflateMarked ω.anti).IsLegalNonempty :=
    ⟨leg, vInflateMarked_W_nonempty hα.2⟩
  have heq := inflateMarked_eq_anti ω
  refine ⟨?_, ?_, ?_, rfl, hc⟩
  · rw [heq]
    exact isLegal_anti leg hneβ.2
  · rw [heq]
    exact (isPhases_anti hneβ).mpr ph
  · rw [heq, widthZ_anti, wd, widthZ_anti]

end SkewClassInflation
