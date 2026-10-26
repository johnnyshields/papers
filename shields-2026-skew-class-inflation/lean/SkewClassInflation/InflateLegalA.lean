/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalSlot
import SkewClassInflation.InflateLegalTranslate
import SkewClassInflation.InflateLegalPhases
import SkewClassInflation.InflateLegalExtractA
import SkewClassInflation.CellInflation

/-!
# Inflation of a legal case-(a) mark

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, case (a),
\(0<w<q-1\).  Under the two private pinches, the inflated mark of a legal case-(a) mark is again
legal, of the same period, width \(w+1\) and phases \((\tau,\sigma+1)\).  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

theorem translate_cell_mem (ω : MarkedInner) (S : Diagram) (k i : ℤ) :
    (i, i + k) ∈ translate (0, -minContent ω.E) S ↔ ω.cell k i ∈ S := by
  rw [mem_translate]
  have e : (i, i + k) - (0, -minContent ω.E) = ω.cell k i := by
    ext <;> simp [cell]
    ring
  rw [e]

/-- Membership in the lower copy of a legal case-(a) mark, from the slot data. -/
theorem mem_W_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) {s t : ℤ} (hp : ω.IsPhases s t)
    {a i : ℤ} : ω.cell a i ∈ ω.W ↔ 0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.lo a ≤ i ∧
      i ≤ ω.hi a - (if s ≤ a then 1 else 0) := by
  have hs := slotGeom_a_of_legal h hc hp
  rw [h.mem_W]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    refine ⟨h0, h1, h2, ?_⟩
    by_cases hs' : s ≤ a
    · have := hs.ehi_ge a hs' (by omega)
      rw [add_comm a ω.period] at h5
      simp only [hs', ite_true]; omega
    · have := hs.ehi_lt a h0 (by omega)
      rw [add_comm a ω.period] at h5
      simp only [hs', ite_false]; omega
  · rintro ⟨h0, h1, h2, h3⟩
    have hp' := hs.pos a h0 (by omega)
    refine ⟨h0, h1, h2, by split_ifs at h3 <;> omega, ?_, ?_⟩
    · rw [add_comm a ω.period]
      by_cases ht : a < t
      · have := hs.elo_lt a h0 ht; omega
      · have := hs.elo_ge a (by omega) (by omega); omega
    · rw [add_comm a ω.period]
      by_cases hs' : s ≤ a
      · have := hs.ehi_ge a hs' (by omega)
        simp only [hs', ite_true] at h3; omega
      · have := hs.ehi_lt a h0 (by omega)
        simp only [hs', ite_false] at h3; omega

/-- The first and last rows of a legal case-(a) mark satisfy the extra equalities of the
two caps. -/
theorem caps_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) :
    ω.lo (ω.widthZ - 1) = ω.lo ω.widthZ ∧ ω.hi (ω.period - 1) = ω.hi ω.period := by
  have hpa := h.attach.1 hc
  exact ⟨(h.lower_caps_H hpa.1).2.1, (h.upper_caps_H hpa.2).2.1⟩

/-- Inflating the normalized legal case-(a) mark is the slot mark of the inflated data. -/
theorem inflateMarked_translate_eq_mark_a (h : ω.IsLegalNonempty) (hc : ω.case = .a)
    {s t : ℤ} (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (hc1 : ω.lo (ω.widthZ - 1) = ω.lo ω.widthZ) :
    inflateMarked (ω.translate (0, -minContent ω.E)) =
      SlotGeom.mark (inflateCells (translate (0, -minContent ω.E) ω.E))
        ω.period (ω.widthZ + 1) (s + 1) ω.rowShift (hiI ω.hi) := by
  have hs := slotGeom_a_of_legal h hc hp
  have hsh := hs.shape
  have hG := diagSet_E_of_legal h
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  refine MarkedInner.mk.injEq .. |>.mpr ⟨rfl, ?_, ?_, ?_⟩
  · ext ⟨i, j⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by ring⟩
    change (i, i + k) ∈ inflateCells (translate (0, -minContent ω.E) ω.W) ↔
      (i, i + k) ∈ SkewGluing.SlotGeom.lowerCopy _ _ _ _
    unfold SlotGeom.lowerCopy
    rw [Finset.mem_filter, mem_inflateCells, show i + k - 1 = i + (k - 1) by ring,
      translate_cell_mem, translate_cell_mem, mem_W_a h hc hp, mem_W_a h hc hp,
      diagSet_inflate hG hsh i k]
    simp only [content, add_sub_cancel_left]
    have hne := hsh.ne
    have p1 := hs.pos
    by_cases hk0 : k < 0
    · constructor <;> intro hh <;> omega
    by_cases hk2 : ω.widthZ < k
    · constructor <;> intro hh <;> omega
    by_cases hk : k = 0
    · subst hk
      rw [loI_of_le (by omega), hiI_zero]
      have := hne 0 le_rfl (by omega)
      have := p1 0 le_rfl (by omega)
      simp only [show ¬ (s ≤ 0) by omega, show ¬ (s + 1 ≤ 0) by omega, ite_false] at *
      constructor
      · rintro (hh | hh)
        · have h4 := hh.2.2.2
          exact ⟨⟨by omega, by omega, hh.2.2.1, by omega⟩, by omega, by omega⟩
        · omega
      · rintro ⟨⟨_, _, h3, h4⟩, _, h6⟩
        left
        exact ⟨le_rfl, by omega, h3, h6⟩
    · have a1 := hsh.stepLo k (by omega) (by omega)
      have a2 := hsh.stepHi k (by omega) (by omega)
      have a3 := hne k (by omega) (by omega)
      have a4 := hne (k - 1) (by omega) (by omega)
      have a5 := p1 (k - 1) (by omega) (by omega)
      rw [loI_of_le (by omega), hiI_of_pos (by omega)]
      by_cases hkw : k = ω.widthZ
      · subst hkw
        have a6 := p1 (ω.widthZ - 1) (by omega) (by omega)
        constructor
        · rintro (hh | hh)
          · omega
          · refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, ?_⟩
            split_ifs at hh ⊢ <;> omega
        · rintro ⟨⟨_, _, h3, h4⟩, _, h6⟩
          right
          refine ⟨by omega, by omega, by omega, ?_⟩
          split_ifs at h6 ⊢ <;> omega
      · have a7 := p1 k (by omega) (by omega)
        constructor
        · rintro (hh | hh)
          · refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, ?_⟩
            split_ifs at hh a5 a7 ⊢ <;> omega
          · refine ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, ?_⟩
            split_ifs at hh ⊢ <;> omega
        · rintro ⟨⟨_, _, h3, h4⟩, _, h6⟩
          by_cases hi' : i ≤ ω.hi k - (if s ≤ k then 1 else 0)
          · left
            exact ⟨by omega, by omega, by omega, hi'⟩
          · right
            refine ⟨by omega, by omega, by omega, ?_⟩
            split_ifs at hi' h6 a5 a7 ⊢ <;> omega
  · exact ω.v_eq
  · exact hc

theorem inflateMarked_translate (u : ℤ × ℤ) (ω : MarkedInner) :
    inflateMarked (ω.translate u) = (inflateMarked ω).translate u := by
  refine MarkedInner.mk.injEq .. |>.mpr ⟨?_, ?_, rfl, rfl⟩
  · exact inflateCells_translate u ω.E
  · exact inflateCells_translate u ω.W

theorem inflateMarked_W_nonempty (h : ω.W.Nonempty) : (inflateMarked ω).W.Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, Finset.mem_union_left _ hx⟩

/-- **Inflation of a legal case-(a) mark.**  If the two private pinches hold and
\(w+1<q\), the inflated mark is a legal case-(a) mark of the same period, width \(w+1\) and
middle phases \((\sigma+1,\tau)\). -/
theorem inflate_isLegal_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) {s t : ℤ}
    (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (h1 : ω.lo (ω.widthZ + 1) = ω.lo ω.widthZ)
    (h2 : ω.hi (ω.period - 2) = ω.hi (ω.period - 1)) :
    (inflateMarked ω).IsLegal ∧ (inflateMarked ω).IsPhases (s + 1) t ∧
      (inflateMarked ω).widthZ = ω.widthZ + 1 ∧ (inflateMarked ω).period = ω.period ∧
      (inflateMarked ω).case = .a := by
  have hs := slotGeom_a_of_legal h hc hp
  have hG := diagSet_E_of_legal h
  have hc1 := (caps_a h hc).1
  have hc2 := (caps_a h hc).2
  have hs' := slotGeom_inflate hs hw1 hc1 hc2 h1 h2
  have hG' : DiagSet (inflateCells (translate (0, -minContent ω.E) ω.E)) 0
      (ω.period + (ω.widthZ + 1) - 1) (loI (ω.period + ω.widthZ - 1) ω.lo) (hiI ω.hi) := by
    have := diagSet_inflate hG hs.shape
    rwa [show ω.period + ω.widthZ - 1 + 1 = ω.period + (ω.widthZ + 1) - 1 by ring] at this
  have heq := inflateMarked_translate_eq_mark_a h hc hp hw1 hc1
  rw [inflateMarked_translate] at heq
  have hleg := SlotGeom.mark_isLegal hG' hs'
  rw [← heq] at hleg
  have hleg' : (inflateMarked ω).IsLegal := (isLegal_translate_iff _).mp hleg
  have hne : (inflateMarked ω).IsLegalNonempty := ⟨hleg', inflateMarked_W_nonempty h.2⟩
  refine ⟨hleg', ?_, ?_, rfl, hc⟩
  · rw [← isPhases_translate_iff hne (0, -minContent ω.E), heq]
    exact SlotGeom.mark_phases hG' hs'
  · have := SlotGeom.mark_width hG' hs'
    rw [← heq] at this
    unfold MarkedInner.widthZ
    rw [← width_translate (0, -minContent ω.E) (inflateMarked ω)]
    exact this

end SkewClassInflation
