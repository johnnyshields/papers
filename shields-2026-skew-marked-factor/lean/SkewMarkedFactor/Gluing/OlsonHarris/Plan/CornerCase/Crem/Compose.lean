/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/Compose.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.Crem.Data

/-!
# The cells of a case-(c) composite, diagonal by diagonal

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`) and «Diagonal geometry»
(`lem:gluing-local` (3)), for a legal mark of case (c) and an arbitrary nonempty skew outer `X`
(connected or not).

On the diagonal of relative content `J q + a` (`0 ≤ a < q`) the composite `X ∘_ω E` has the cells
of the copies at the diagonal `J` of `X` (rows `J p + [ℓ_a, ν_J - 1 + h_a]`, `ν_J` the number of
cells of the diagonal), of the copies at the diagonal `J - 1` (for `a < w`), and of the
supplemental copies (`mem_compose_c`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

variable {ω : MarkedInner} {X : Diagram}

/-- A skew diagram contains exactly the cells between the first and last cell of each of its
diagonals. -/
theorem mem_skew_iff (hX : IsSkew X) {i j : ℤ} :
    (i, i + j) ∈ X ↔ j ∈ contents X ∧ diagLo X j ≤ i ∧ i ≤ diagHi X j := by
  constructor
  · intro hm
    have hc : content (i, i + j) ∈ contents X := content_mem_contents hm
    have e : content (i, i + j) = j := by simp [content]
    rw [e] at hc
    exact ⟨hc, diagLo_le hm (by simp), le_diagHi hm (by simp)⟩
  · rintro ⟨hj, h1, h2⟩
    have a := diagLo_mem hj
    have b := diagHi_mem hj
    exact hX.mem (a := diagLo X j) (b := diagLo X j + j) (c := diagHi X (j)) (d := diagHi X j + j)
      a b (diagLo_le_diagHi hj) (by have := diagLo_le_diagHi hj; omega) h1 h2 (by omega)
      (by omega)

theorem cell_sub_origin_c (ω : MarkedInner) (X : Diagram) (d : ℤ × ℤ) (k r : ℤ) :
    ω.cell k r - ω.origin X d =
      ω.cell (k - content d * ω.period) (r - (ω.origin X d).1) :=
  cell_sub_origin ω X d k r

theorem exists_row_iff {L H A B r base : ℤ} (hLH : L ≤ H) (hAB : A ≤ B) :
    (∃ i, L ≤ i ∧ i ≤ H ∧ A ≤ r - (base + (i - L)) ∧ r - (base + (i - L)) ≤ B) ↔
      base + A ≤ r ∧ r ≤ base + (H - L) + B := by
  constructor
  · rintro ⟨i, h1, h2, h3, h4⟩; omega
  · intro h
    exact ⟨max L (L + (r - base - B)), by omega, by omega, by omega, by omega⟩

/-- The main copies: cells of the copies `E + L_ω(d)`, `d ∈ X`, on the diagonal of relative content
`k`, in the form of the existence of a diagonal `j` and a row `i` of `X`. -/
theorem mem_main_c (h : ω.IsLegalNonempty) (hc : ω.case = .c) (hX : IsSkew X) {k r : ℤ} :
    (∃ d ∈ X, ω.cell k r ∈ translate (ω.origin X d) ω.E) ↔
      ∃ j i, j ∈ contents X ∧ diagLo X j ≤ i ∧ i ≤ diagHi X j ∧
        0 ≤ k - j * ω.period ∧ k - j * ω.period ≤ ω.period + ω.widthZ - 1 ∧
        ω.lo (k - j * ω.period) ≤ r - (j * ω.rowShift + (i - diagLo X j)) ∧
        r - (j * ω.rowShift + (i - diagLo X j)) ≤ ω.hi (k - j * ω.period) := by
  constructor
  · rintro ⟨d, hd, hx⟩
    obtain ⟨d1, d2⟩ := d
    have hdc : content (d1, d2) = d2 - d1 := rfl
    have hd' : (d1, d1 + (d2 - d1)) ∈ X := by simpa using hd
    rw [mem_skew_iff hX] at hd'
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst] at hx
    simp only [hdc, originRow, hc] at hx
    exact ⟨d2 - d1, d1, hd'.1, hd'.2.1, hd'.2.2, by omega, by omega, by omega, by omega⟩
  · rintro ⟨j, i, h1, h2, h3, h5, h6, h7, h8⟩
    refine ⟨(i, i + j), (mem_skew_iff hX).mpr ⟨h1, h2, h3⟩, ?_⟩
    have hdc : content (i, i + j) = j := by simp [content]
    rw [mem_translate, cell_sub_origin, h.mem_E, origin_fst, hdc]
    simp only [originRow, hc]
    exact ⟨h5, h6, h7, h8⟩

/-- The supplemental copy at a cell `d` of the composite, on the diagonal of relative content
`k`: the lower copy `W` read on the diagonal `k - c(d) q - q`. -/
theorem mem_suppCell_c (h : ω.IsLegalNonempty) (hc : ω.case = .c) (X : Diagram) (d : ℤ × ℤ)
    (k r : ℤ) :
    ω.cell k r ∈ translate (ω.origin X d + ω.supplementalShift) ω.upper ↔
      ω.cell (k - content d * ω.period - ω.period) (r - (ω.origin X d).1 - 1 - ω.rowShift) ∈
        ω.W := by
  rw [mem_translate]
  have hco := content_origin ω X d
  unfold content at hco
  have hs : ω.supplementalShift = eCell := by simp [supplementalShift, hc]
  have e : ω.cell k r - (ω.origin X d + ω.supplementalShift) =
      ω.cell (k - content d * ω.period - ω.period + ω.period) (r - (ω.origin X d).1 - 1) := by
    rw [hs]
    unfold cell eCell
    ext
    · simp only [Prod.fst_sub, Prod.fst_add]; ring
    · simp only [Prod.snd_sub, Prod.snd_add, content] at hco ⊢; omega
  rw [e, h.mem_upper]

/-- The cells of the supplemental copies, as the existence of a diagonal `j` and a row `i`. -/
theorem mem_supp_c' (h : ω.IsLegalNonempty) (hc : ω.case = .c) (hX : IsSkew X) {k r : ℤ} :
    (∃ d ∈ X, ω.SameRibbon X d ∧
      ω.cell k r ∈ translate (ω.origin X d + ω.supplementalShift) ω.upper) ↔
    ∃ j i, j ∈ contents X ∧ diagLo X j ≤ i ∧ i ≤ diagHi X j ∧ (j + 1) ∈ contents X ∧
      diagLo X (j + 1) ≤ i - 1 ∧ i - 1 ≤ diagHi X (j + 1) ∧
      i - diagLo X j = i - 1 - diagLo X (j + 1) ∧
      ω.cell (k - j * ω.period - ω.period)
        (r - (j * ω.rowShift + (i - diagLo X j)) - 1 - ω.rowShift) ∈ ω.W := by
  constructor
  · rintro ⟨⟨d1, d2⟩, hd, hsr, hx⟩
    obtain ⟨j, rfl⟩ : ∃ j, d2 = d1 + j := ⟨d2 - d1, by ring⟩
    have hdc : content (d1, d1 + j) = j := by simp [content]
    simp only [SameRibbon, hc, hdc] at hsr
    rw [mem_suppCell_c h hc, origin_fst, hdc] at hx
    simp only [originRow, hc] at hx
    have hd' := (mem_skew_iff hX).mp (show (d1, d1 + j) ∈ X from hd)
    have hn : (d1 - 1, d1 + j) = (d1 - 1, d1 - 1 + (j + 1)) := Prod.ext rfl (by ring)
    have hn' := (mem_skew_iff hX).mp (show (d1 - 1, d1 - 1 + (j + 1)) ∈ X by
      rw [← hn]; exact hsr.1)
    refine ⟨j, d1, hd'.1, hd'.2.1, hd'.2.2, hn'.1, hn'.2.1, hn'.2.2, hsr.2, ?_⟩
    exact hx
  · rintro ⟨j, i, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨(i, i + j), (mem_skew_iff hX).mpr ⟨h1, h2, h3⟩, ?_, ?_⟩
    · have hdc : content (i, i + j) = j := by simp [content]
      simp only [SameRibbon, hc, hdc]
      refine ⟨?_, h7⟩
      have hn : (i - 1, i + j) = (i - 1, i - 1 + (j + 1)) := Prod.ext rfl (by ring)
      change (i - 1, i + j) ∈ X
      rw [hn]
      exact (mem_skew_iff hX).mpr ⟨h4, h5, h6⟩
    · have hdc : content (i, i + j) = j := by simp [content]
      rw [mem_suppCell_c h hc, origin_fst, hdc]
      simp only [originRow, hc]
      exact h8

theorem height_pos {X : Diagram} {j : ℤ} (hj : j ∈ contents X) : 1 ≤ height X j := by
  have := diagLo_le_diagHi hj
  unfold height
  omega

theorem W_row_bound (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t)
    {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    ω.lo a ≤ ω.hi a - (if s ≤ a then 1 else 0) := by
  obtain ⟨r, hr⟩ := h.exists_W h0 h1
  rw [mem_W_cell h hc hph] at hr
  omega

/-- **The cells of a case-(c) composite on the diagonal of relative content `J q + a`**
(`0 ≤ a < q`), for an arbitrary nonempty skew outer `X`: the rows of the copies at the diagonal
`J` of `X`, of the copies at the diagonal `J - 1` (for `a < w`), and of the supplemental copies. -/
theorem mem_compose_c (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) (hX : IsSkew X) (hXne : X.Nonempty) {J a r : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ ω.compose X ↔
      (J ∈ contents X ∧ J * ω.rowShift + ω.lo a ≤ r ∧
        r ≤ J * ω.rowShift + (height X J - 1) + ω.hi a) ∨
      (a < ω.widthZ ∧ J - 1 ∈ contents X ∧ J * ω.rowShift + ω.lo a ≤ r ∧
        r ≤ J * ω.rowShift + (height X (J - 1) - 1) + ω.hi a +
          (if a < t then 1 else if a < s then 0 else -1)) ∨
      (a < ω.widthZ ∧ J - 1 ∈ contents X ∧ J ∈ contents X ∧
        diagLo X J + 1 = diagLo X (J - 1) ∧ J * ω.rowShift + 1 + ω.lo a ≤ r ∧
        r ≤ J * ω.rowShift + 1 + (ω.hi a - (if s ≤ a then 1 else 0)) +
          min (height X (J - 1) - 1) (height X J - 1)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hlt := h.phases_lt (Or.inl hc) hph
  have hlh : ∀ b, 0 ≤ b → b ≤ ω.period + ω.widthZ - 1 → ω.lo b ≤ ω.hi b :=
    fun b h1 h2 => h.lo_le_hi h1 h2
  rw [mem_compose hXne, mem_main_c h hc hX, mem_supp_c' h hc hX]
  have eJ1 : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have part1 : (∃ j i, j ∈ contents X ∧ diagLo X j ≤ i ∧ i ≤ diagHi X j ∧
        0 ≤ J * ω.period + a - j * ω.period ∧
        J * ω.period + a - j * ω.period ≤ ω.period + ω.widthZ - 1 ∧
        ω.lo (J * ω.period + a - j * ω.period) ≤
          r - (j * ω.rowShift + (i - diagLo X j)) ∧
        r - (j * ω.rowShift + (i - diagLo X j)) ≤ ω.hi (J * ω.period + a - j * ω.period)) ↔
      (J ∈ contents X ∧ J * ω.rowShift + ω.lo a ≤ r ∧
        r ≤ J * ω.rowShift + (height X J - 1) + ω.hi a) ∨
      (a < ω.widthZ ∧ J - 1 ∈ contents X ∧ J * ω.rowShift + ω.lo a ≤ r ∧
        r ≤ J * ω.rowShift + (height X (J - 1) - 1) + ω.hi a +
          (if a < t then 1 else if a < s then 0 else -1)) := by
    constructor
    · rintro ⟨j, i, h1, h2, h3, h5, h6, h7, h8⟩
      rcases MarkedInner.range_j (by omega) hq ha0 haq (by omega) h5 h6 with rfl | ⟨rfl, hl⟩
      · left
        have e : j * ω.period + a - j * ω.period = a := by ring
        rw [e] at h7 h8
        have := (exists_row_iff (L := diagLo X j) (H := diagHi X j) (A := ω.lo a) (B := ω.hi a)
          (r := r) (base := j * ω.rowShift) (diagLo_le_diagHi h1) (hlh a ha0 (by omega))).mp
          ⟨i, h2, h3, h7, h8⟩
        unfold height
        exact ⟨h1, by omega, by omega⟩
      · right
        have e : J * ω.period + a - (J - 1) * ω.period = a + ω.period := by ring
        rw [e] at h7 h8
        have hs := hi_shift h hc hph ha0 (by omega : a ≤ ω.widthZ - 1)
        have hl2 := lo_shift h hc ha0 (by omega : a ≤ ω.widthZ - 1)
        have := (exists_row_iff (L := diagLo X (J - 1)) (H := diagHi X (J - 1))
          (A := ω.lo (a + ω.period)) (B := ω.hi (a + ω.period))
          (r := r) (base := (J - 1) * ω.rowShift) (diagLo_le_diagHi h1)
          (hlh _ (by omega) (by omega))).mp ⟨i, h2, h3, h7, h8⟩
        unfold height
        refine ⟨hl, h1, by omega, by omega⟩
    · rintro (⟨h1, h3, h4⟩ | ⟨hl, h1, h3, h4⟩)
      · obtain ⟨i, hi⟩ := (exists_row_iff (L := diagLo X J) (H := diagHi X J) (A := ω.lo a)
          (B := ω.hi a) (r := r) (base := J * ω.rowShift) (diagLo_le_diagHi h1)
          (hlh a ha0 (by omega))).mpr ⟨h3, by unfold height at h4; omega⟩
        have e : J * ω.period + a - J * ω.period = a := by ring
        refine ⟨J, i, h1, hi.1, hi.2.1, by omega, by omega, ?_, ?_⟩
        · rw [e]; exact hi.2.2.1
        · rw [e]; exact hi.2.2.2
      · have hs := hi_shift h hc hph ha0 (by omega : a ≤ ω.widthZ - 1)
        have hl2 := lo_shift h hc ha0 (by omega : a ≤ ω.widthZ - 1)
        obtain ⟨i, hi⟩ := (exists_row_iff (L := diagLo X (J - 1)) (H := diagHi X (J - 1))
          (A := ω.lo (a + ω.period)) (B := ω.hi (a + ω.period)) (r := r)
          (base := (J - 1) * ω.rowShift) (diagLo_le_diagHi h1)
          (hlh _ (by omega) (by omega))).mpr
          ⟨by omega, by unfold height at h4; omega⟩
        have e : J * ω.period + a - (J - 1) * ω.period = a + ω.period := by ring
        refine ⟨J - 1, i, h1, hi.1, hi.2.1, by rw [e]; omega, by rw [e]; omega, ?_, ?_⟩
        · rw [e]; exact hi.2.2.1
        · rw [e]; exact hi.2.2.2
  have part2 : (∃ j i, j ∈ contents X ∧ diagLo X j ≤ i ∧ i ≤ diagHi X j ∧ (j + 1) ∈ contents X ∧
      diagLo X (j + 1) ≤ i - 1 ∧ i - 1 ≤ diagHi X (j + 1) ∧
      i - diagLo X j = i - 1 - diagLo X (j + 1) ∧
      ω.cell (J * ω.period + a - j * ω.period - ω.period)
        (r - (j * ω.rowShift + (i - diagLo X j)) - 1 - ω.rowShift) ∈ ω.W) ↔
      (a < ω.widthZ ∧ J - 1 ∈ contents X ∧ J ∈ contents X ∧
        diagLo X J + 1 = diagLo X (J - 1) ∧ J * ω.rowShift + 1 + ω.lo a ≤ r ∧
        r ≤ J * ω.rowShift + 1 + (ω.hi a - (if s ≤ a then 1 else 0)) +
          min (height X (J - 1) - 1) (height X J - 1)) := by
    have hWb := W_row_bound h hc hph (a := a)
    constructor
    · rintro ⟨j, i, h1, h2, h3, h4, h5, h6, h7, h8⟩
      rw [mem_W_cell h hc hph] at h8
      obtain ⟨m1, m2, m3, m4⟩ := h8
      have hj : j = J - 1 := MarkedInner.range_j' (by omega) hq ha0 haq (by omega) (by omega)
      subst hj
      have e : J * ω.period + a - (J - 1) * ω.period - ω.period = a := by ring
      rw [e] at m1 m2 m3 m4
      have e2 : J - 1 + 1 = J := by ring
      rw [e2] at h4 h5 h6 h7
      unfold height
      have := hWb (by omega) m2
      refine ⟨by omega, h1, h4, by omega, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨hl, h1, h4, h7, h3, h8⟩
      have hr := hWb (by omega) (by omega)
      have hp1 := height_pos h1
      have hp2 := height_pos h4
      have hd1 := diagLo_le_diagHi h1
      have hd2 := diagLo_le_diagHi h4
      unfold height at hp1 hp2 h8
      refine ⟨J - 1, diagLo X (J - 1) + max 0 (r - J * ω.rowShift - 1 -
        (ω.hi a - (if s ≤ a then 1 else 0))), h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [show J - 1 + 1 = J by ring]; exact h4
      · rw [show J - 1 + 1 = J by ring]; omega
      · rw [show J - 1 + 1 = J by ring]; omega
      · rw [show J - 1 + 1 = J by ring]; omega
      · have e : J * ω.period + a - (J - 1) * ω.period - ω.period = a := by ring
        rw [mem_W_cell h hc hph, e]
        refine ⟨ha0, by omega, ?_, ?_⟩
        · omega
        · omega
  rw [part1, part2, or_assoc]


end Rem

end Corner

end Plan

end SkewMarkedFactor.Gluing
