/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/MarkFacts/HatMark.lean
import SkewMarkedFactor.Gluing.Local.Final
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Defs
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MarkFacts.Band

/-!
# The hatted mark of a legal mark is a skew diagram

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local`) and the
hatted shapes of condition IV (`sec:gluing`): for a legal marked inner with a nonempty copy, the
amalgam `F = E ∪ (E - v)` of two consecutive copies of `E` is a connected skew diagram, and the
hatted mark `Ŵ` is the part of `{x ∈ F : x + e ∈ F}` on the contents of the marked diagonals.
Condition IV says that no cell of the hatted mark is adjacent to a cell of the hatted middle,
which is exactly what keeps this cut of a skew diagram skew.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

open Plan.MarkFacts

namespace MarkedInner

variable {ω : MarkedInner}

/-- The amalgam `E ∪ (E - v)` of two consecutive copies of `E`, overlapping in `W₋`. -/
def amalgam (ω : MarkedInner) : Diagram := ω.E ∪ translate (-ω.v) ω.E

theorem mem_amalgam {x : ℤ × ℤ} : x ∈ ω.amalgam ↔ x ∈ ω.E ∨ x + ω.v ∈ ω.E := by
  unfold amalgam
  rw [Finset.mem_union, mem_translate]
  simp

theorem cell_add_smul (ω : MarkedInner) (k a r : ℤ) :
    ω.cell a r + k • ω.v = ω.cell (a + k * ω.period) (r + k * ω.rowShift) := by
  have := period_eq ω
  unfold cell rowShift
  ext
  · simp
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [show ω.v.2 = ω.v.1 + ω.period by omega]
    ring

theorem cell_sub_smul (ω : MarkedInner) (k a r : ℤ) :
    ω.cell a r - k • ω.v = ω.cell (a - k * ω.period) (r - k * ω.rowShift) := by
  rw [sub_eq_add_neg, ← neg_smul, cell_add_smul]
  simp [sub_eq_add_neg]

/-- On a marked diagonal, the periodic window contains a cell exactly when `E` or the previous
copy `E - v` does. -/
theorem IsLegalNonempty.mem_periodicWindow_band (h : ω.IsLegalNonempty) {a r : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    ω.cell a r ∈ Plan.periodicWindow ω ↔ ω.cell a r ∈ ω.E ∨ ω.cell a r + ω.v ∈ ω.E := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold Plan.periodicWindow
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [Finset.mem_Icc] at hk
    rw [mem_translate] at hx
    have hx0 := hx
    rw [cell_sub_smul, h.mem_E] at hx
    obtain ⟨hk1, hk2⟩ := hk
    have : k = 0 ∨ k = -1 := by
      interval_cases k <;> omega
    rcases this with rfl | rfl
    · left; simpa using hx0
    · right; simpa using hx0
  · rintro (hx | hx)
    · exact ⟨0, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simpa [mem_translate] using hx⟩
    · exact ⟨-1, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simpa [mem_translate] using hx⟩

theorem IsLegalNonempty.mem_amalgam_cell (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ ω.amalgam ↔
      (0 ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a) ∨
      (0 ≤ a + ω.period ∧ a + ω.period ≤ ω.period + ω.widthZ - 1 ∧
        ω.lo (a + ω.period) ≤ r + ω.rowShift ∧ r + ω.rowShift ≤ ω.hi (a + ω.period)) := by
  rw [mem_amalgam, cell_add_v, h.mem_E, h.mem_E]

/-- **Two cells of the amalgam on consecutive rows of a marked diagonal meet `W₋`.**  On a marked
diagonal the cells of `E` outside `W₋` and the cells of `E - v` outside `W₋` are each at most one
(the middle is thin on both marked ends), and the two row intervals overlap in `W₋`. -/
theorem IsLegalNonempty.hat_meets_W (h : ω.IsLegalNonempty) {a r : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) (hx : ω.cell a r ∈ ω.amalgam)
    (hx' : ω.cell a (r + 1) ∈ ω.amalgam) : ω.cell a r ∈ ω.W ∨ ω.cell a (r + 1) ∈ ω.W := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.mem_amalgam_cell] at hx hx'
  rw [h.mem_W, h.mem_W]
  obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row h0 h1
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have hn1' : ¬ (ω.lo a ≤ r ∧ r ≤ ω.hi a ∧ ω.lo (a + ω.period) ≤ r + ω.rowShift ∧
      r + ω.rowShift ≤ ω.hi (a + ω.period)) := fun hh => hn1 ⟨h0, h1, hh⟩
  have hn2' : ¬ (ω.lo a ≤ r + 1 ∧ r + 1 ≤ ω.hi a ∧ ω.lo (a + ω.period) ≤ r + 1 + ω.rowShift ∧
      r + 1 + ω.rowShift ≤ ω.hi (a + ω.period)) := fun hh => hn2 ⟨h0, h1, hh⟩
  -- thin on the lower diagonal
  have A1 : ¬ (ω.lo a ≤ r ∧ r ≤ ω.hi a ∧ ω.lo a ≤ r + 1 ∧ r + 1 ≤ ω.hi a) := by
    rintro ⟨e1, e2, e3, e4⟩
    have m1 : ω.cell a r ∈ ω.middle := by
      rw [h.mem_middle_lt (by omega), h.mem_E, h.mem_W]
      exact ⟨⟨h0, by omega, e1, e2⟩, hn1⟩
    have m2 : ω.cell a (r + 1) ∈ ω.middle := by
      rw [h.mem_middle_lt (by omega), h.mem_E, h.mem_W]
      exact ⟨⟨h0, by omega, e3, e4⟩, hn2⟩
    have := h.middle_thin m1 m2 (by simp [content_cell]) (Or.inl (by rw [content_cell]; omega))
    have := ω.cell_inj this
    omega
  -- thin on the upper diagonal
  have A2 : ¬ (ω.lo (a + ω.period) ≤ r + ω.rowShift ∧ r + ω.rowShift ≤ ω.hi (a + ω.period) ∧
      ω.lo (a + ω.period) ≤ r + 1 + ω.rowShift ∧ r + 1 + ω.rowShift ≤ ω.hi (a + ω.period)) := by
    rintro ⟨e1, e2, e3, e4⟩
    have m1 : ω.cell (a + ω.period) (r + ω.rowShift) ∈ ω.middle := by
      rw [h.mem_middle_upper h0 h1]
      exact ⟨⟨e1, e2⟩, fun hh => hn1' ⟨by omega, by omega, hh.2.2.1, hh.2.2.2⟩⟩
    have m2 : ω.cell (a + ω.period) (r + 1 + ω.rowShift) ∈ ω.middle := by
      rw [h.mem_middle_upper h0 h1]
      exact ⟨⟨e3, e4⟩, fun hh => hn2' ⟨by omega, by omega, hh.2.2.1, hh.2.2.2⟩⟩
    have := h.middle_thin m1 m2 (by simp [content_cell])
      (Or.inr (by rw [content_cell]; omega))
    have := ω.cell_inj this
    omega
  omega

/-- The first row of the diagonal of the amalgam at the relative content `a ∈ [-q, q + w - 1]`. -/
def amalgamLo (ω : MarkedInner) (a : ℤ) : ℤ :=
  if a < 0 then ω.lo (a + ω.period) - ω.rowShift
  else if a < ω.widthZ then min (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift) else ω.lo a

/-- The last row of the diagonal of the amalgam at the relative content `a ∈ [-q, q + w - 1]`. -/
def amalgamHi (ω : MarkedInner) (a : ℤ) : ℤ :=
  if a < 0 then ω.hi (a + ω.period) - ω.rowShift
  else if a < ω.widthZ then max (ω.hi a) (ω.hi (a + ω.period) - ω.rowShift) else ω.hi a

theorem IsLegalNonempty.mem_amalgam_interval (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ ω.amalgam ↔
      (-ω.period ≤ a ∧ a ≤ ω.period + ω.widthZ - 1) ∧ ω.amalgamLo a ≤ r ∧ r ≤ ω.amalgamHi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.mem_amalgam_cell]
  unfold amalgamLo amalgamHi
  by_cases ha0 : a < 0
  · simp only [ha0, ite_true]
    omega
  · by_cases haw : a < ω.widthZ
    · obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row (a := a) (by omega) (by omega)
      simp only [ha0, haw, ite_false, ite_true]
      omega
    · simp only [ha0, haw, ite_false]
      omega

theorem IsLegalNonempty.amalgamLo_step (h : ω.IsLegalNonempty) {b : ℤ} (h1 : 1 - ω.period ≤ b)
    (h2 : b ≤ ω.period + ω.widthZ - 1) :
    ω.amalgamLo (b - 1) - ω.amalgamLo b = 0 ∨ ω.amalgamLo (b - 1) - ω.amalgamLo b = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold amalgamLo
  by_cases hb0 : b < 0
  · have := h.bit_lo (a := b + ω.period) (by omega) (by omega)
    rw [show b - 1 + ω.period = b + ω.period - 1 by ring]
    simp only [hb0, show b - 1 < 0 by omega, ite_true]
    omega
  · by_cases hb1 : b = 0
    · subst hb1
      have h3 := h.bit_lo (a := ω.period) (by omega) (by omega)
      have h4 := h.dLo_zero_le.1
      unfold dLo at h4
      simp only [zero_add] at h4
      rw [show (0 : ℤ) - 1 + ω.period = ω.period - 1 by ring]
      simp only [lt_irrefl, ite_false, show (0 : ℤ) - 1 < 0 by omega, ite_true,
        show (0 : ℤ) < ω.widthZ by omega, zero_add]
      omega
    · by_cases hbw : b < ω.widthZ
      · have h3 := h.bit_lo (a := b) (by omega) (by omega)
        have h4 := h.bit_lo (a := b + ω.period) (by omega) (by omega)
        rw [show b - 1 + ω.period = b + ω.period - 1 by ring]
        simp only [hb0, hbw, show b - 1 < ω.widthZ by omega, show ¬ b - 1 < 0 by omega,
          ite_false, ite_true]
        omega
      · by_cases hbw' : b = ω.widthZ
        · subst hbw'
          have h3 := h.bit_lo (a := ω.widthZ) (by omega) (by omega)
          have h4 := h.last_dLo.1
          unfold dLo at h4
          simp only [hb0, show ¬ ω.widthZ < ω.widthZ by omega,
            show ω.widthZ - 1 < ω.widthZ by omega, show ¬ ω.widthZ - 1 < 0 by omega,
            ite_false, ite_true]
          omega
        · have h3 := h.bit_lo (a := b) (by omega) (by omega)
          simp only [hb0, hbw, show ¬ b - 1 < 0 by omega, show ¬ b - 1 < ω.widthZ by omega,
            ite_false]
          omega

theorem IsLegalNonempty.amalgamHi_step (h : ω.IsLegalNonempty) {b : ℤ} (h1 : 1 - ω.period ≤ b)
    (h2 : b ≤ ω.period + ω.widthZ - 1) :
    ω.amalgamHi (b - 1) - ω.amalgamHi b = 0 ∨ ω.amalgamHi (b - 1) - ω.amalgamHi b = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold amalgamHi
  by_cases hb0 : b < 0
  · have := h.bit_hi (a := b + ω.period) (by omega) (by omega)
    rw [show b - 1 + ω.period = b + ω.period - 1 by ring]
    simp only [hb0, show b - 1 < 0 by omega, ite_true]
    omega
  · by_cases hb1 : b = 0
    · subst hb1
      have h3 := h.bit_hi (a := ω.period) (by omega) (by omega)
      have h4 := h.dLo_zero_le.2
      unfold dHi at h4
      simp only [zero_add] at h4
      rw [show (0 : ℤ) - 1 + ω.period = ω.period - 1 by ring]
      simp only [lt_irrefl, ite_false, show (0 : ℤ) - 1 < 0 by omega, ite_true,
        show (0 : ℤ) < ω.widthZ by omega, zero_add]
      omega
    · by_cases hbw : b < ω.widthZ
      · have h3 := h.bit_hi (a := b) (by omega) (by omega)
        have h4 := h.bit_hi (a := b + ω.period) (by omega) (by omega)
        rw [show b - 1 + ω.period = b + ω.period - 1 by ring]
        simp only [hb0, hbw, show b - 1 < ω.widthZ by omega, show ¬ b - 1 < 0 by omega,
          ite_false, ite_true]
        omega
      · by_cases hbw' : b = ω.widthZ
        · subst hbw'
          have h3 := h.bit_hi (a := ω.widthZ) (by omega) (by omega)
          have h4 := h.last_dLo.2
          unfold dHi at h4
          simp only [hb0, show ¬ ω.widthZ < ω.widthZ by omega,
            show ω.widthZ - 1 < ω.widthZ by omega, show ¬ ω.widthZ - 1 < 0 by omega,
            ite_false, ite_true]
          omega
        · have h3 := h.bit_hi (a := b) (by omega) (by omega)
          simp only [hb0, hbw, show ¬ b - 1 < 0 by omega, show ¬ b - 1 < ω.widthZ by omega,
            ite_false]
          omega

theorem IsLegalNonempty.amalgam_hasDiagonalShape (h : ω.IsLegalNonempty) :
    HasDiagonalShape ω.amalgam := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hn : ((2 * ω.period + ω.widthZ).toNat : ℤ) = 2 * ω.period + ω.widthZ := by
    apply Int.toNat_of_nonneg; omega
  refine hasDiagonalShape_of_intervals (c := minContent ω.E - ω.period)
    (n := (2 * ω.period + ω.widthZ).toNat) (L := fun a => ω.amalgamLo (a - ω.period))
    (R := fun a => ω.amalgamHi (a - ω.period)) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · intro a r
    have e : (r, r + (minContent ω.E - ω.period + a)) = ω.cell (a - ω.period) r := by
      unfold cell; ext
      · rfl
      · simp only; ring
    rw [e, h.mem_amalgam_interval, hn]
    omega
  · intro a ha hb
    rw [hn] at hb
    unfold amalgamLo amalgamHi
    by_cases ha0 : a - ω.period < 0
    · simp only [ha0, ite_true]
      have := h.lo_le_hi (a := a - ω.period + ω.period) (by omega) (by omega)
      omega
    · by_cases haw : a - ω.period < ω.widthZ
      · have := h.lo_le_hi (a := a - ω.period) (by omega) (by omega)
        simp only [ha0, haw, ite_false, ite_true]
        omega
      · simp only [ha0, haw, ite_false]
        exact h.lo_le_hi (a := a - ω.period) (by omega) (by omega)
  · intro a ha hb
    rw [hn] at hb
    have := h.amalgamLo_step (b := a - ω.period) (by omega) (by omega)
    rwa [show a - 1 - ω.period = a - ω.period - 1 by ring]
  · intro a ha hb
    rw [hn] at hb
    have := h.amalgamHi_step (b := a - ω.period) (by omega) (by omega)
    rwa [show a - 1 - ω.period = a - ω.period - 1 by ring]
  · have := h.lo_zero
    unfold amalgamLo amalgamHi
    simp only [zero_sub, neg_lt_zero, show (0 : ℤ) < ω.period by omega, ite_true,
      neg_add_cancel]
    rw [this]
  · have := h.lo_last
    change ω.amalgamLo (((2 * ω.period + ω.widthZ).toNat : ℤ) - 1 - ω.period) =
      ω.amalgamHi (((2 * ω.period + ω.widthZ).toNat : ℤ) - 1 - ω.period)
    rw [hn, show 2 * ω.period + ω.widthZ - 1 - ω.period = ω.period + ω.widthZ - 1 by ring]
    unfold amalgamLo amalgamHi
    simp only [show ¬ ω.period + ω.widthZ - 1 < 0 by omega,
      show ¬ ω.period + ω.widthZ - 1 < ω.widthZ by omega, ite_false]
    exact this

theorem IsLegalNonempty.isSkew_amalgam (h : ω.IsLegalNonempty) : IsSkew ω.amalgam :=
  isSkew_of_hasDiagonalShape h.amalgam_hasDiagonalShape

theorem mem_hatMarkFin {x : ℤ × ℤ} :
    x ∈ Plan.hatMarkFin ω ↔ (x ∈ Plan.periodicWindow ω ∧ x + eCell ∈ ω.W) ∨
      (x ∈ ω.W ∧ x + eCell ∈ Plan.periodicWindow ω) := by
  unfold Plan.hatMarkFin
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro (⟨-, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h3, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨h3, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨⟨x + eCell, h2, by simp⟩, h2, h3⟩
    · exact Or.inr ⟨h1, h2⟩

/-- The hatted mark occupies only diagonals of the mark: `span \overline W ≤ w`. -/
theorem span_hatMarkFin_le (ω : MarkedInner) : span (Plan.hatMarkFin ω) ≤ ω.width := by
  unfold span MarkedInner.width
  apply Finset.card_le_card
  intro k hk
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
  rw [mem_hatMarkFin] at hx
  rcases hx with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact Finset.mem_image.mpr ⟨x + eCell, h2, content_eCell_add x⟩
  · exact Finset.mem_image.mpr ⟨x, h1, rfl⟩

/-- The cells of `F = E ∪ (E - v)` with `x + e ∈ F` on the contents of the marked diagonals. -/
def hatBand (ω : MarkedInner) : Diagram :=
  (ω.amalgam.filter fun x => x + eCell ∈ ω.amalgam).filter fun x =>
    minContent ω.E ≤ content x ∧ content x ≤ minContent ω.E + ω.widthZ - 1

theorem IsLegalNonempty.hatMarkFin_eq (h : ω.IsLegalNonempty) :
    Plan.hatMarkFin ω = ω.hatBand := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hWE : ω.W ⊆ ω.E := h.nonemptyMark.2.2.1
  ext x
  obtain ⟨a, r, rfl⟩ := ω.exists_cell x
  rw [mem_hatMarkFin, hatBand, Finset.mem_filter, Finset.mem_filter, cell_add_e, content_cell]
  constructor
  · rintro (⟨hP, hW⟩ | ⟨hW, hP⟩)
    · have hW' := (h.mem_W).mp hW
      have hP' := (h.mem_periodicWindow_band hW'.1 hW'.2.1).mp hP
      refine ⟨⟨?_, mem_amalgam.mpr (Or.inl (hWE hW))⟩, by omega, by omega⟩
      rw [mem_amalgam]; exact hP'
    · have hW' := (h.mem_W).mp hW
      have hP' := (h.mem_periodicWindow_band hW'.1 hW'.2.1).mp hP
      refine ⟨⟨mem_amalgam.mpr (Or.inl (hWE hW)), ?_⟩, by omega, by omega⟩
      rw [mem_amalgam]; exact hP'
  · rintro ⟨⟨hx, hx'⟩, hb1, hb2⟩
    have hmeet := h.hat_meets_W (a := a) (r := r) (by omega) (by omega) hx hx'
    rcases hmeet with hW | hW
    · refine Or.inr ⟨hW, ?_⟩
      rw [h.mem_periodicWindow_band (by omega) (by omega)]
      rw [mem_amalgam] at hx'
      exact hx'
    · refine Or.inl ⟨?_, hW⟩
      rw [h.mem_periodicWindow_band (by omega) (by omega)]
      rw [mem_amalgam] at hx
      exact hx

theorem mem_periodicUnion_of_amalgam {x : ℤ × ℤ} (hx : x ∈ ω.amalgam) :
    x ∈ ω.periodicUnion := by
  rw [mem_amalgam] at hx
  rcases hx with hx | hx
  · exact ⟨0, by simpa using hx⟩
  · exact ⟨-1, by simpa using hx⟩

/-- **Condition IV keeps the cut skew.**  The hatted mark of a legal mark with a nonempty copy,
cut out of `{x ∈ F : x + e ∈ F}` by the contents of the marked diagonals, is skew: the amalgam
`F` is a connected skew diagram, and an edge of `{x ∈ F : x + e ∈ F}` crossing a boundary of the
band would join a cell of the hatted middle to a cell of the hatted mark. -/
theorem IsLegalNonempty.isSkew_hatBand (h : ω.IsLegalNonempty) : IsSkew ω.hatBand := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hIV := h.1.2.2.2.2
  refine isSkew_filter_band (isSkew_hat h.isSkew_amalgam) (minContent ω.E)
    (minContent ω.E + ω.widthZ - 1) ?_ ?_
  · intro u hu u' hu' hadj hc hc'
    rw [Finset.mem_filter] at hu hu'
    obtain ⟨a, r, rfl⟩ := ω.exists_cell u
    obtain ⟨a', r', rfl⟩ := ω.exists_cell u'
    rw [content_cell] at hc hc'
    rw [cell_add_e] at hu hu'
    have ha : a = ω.widthZ := by omega
    have ha' : a' = ω.widthZ - 1 := by omega
    subst ha ha'
    have hmid : ∀ r'' : ℤ, ω.cell ω.widthZ r'' ∈ ω.amalgam → ω.cell ω.widthZ r'' ∈ ω.middle := by
      intro r'' hr
      rw [h.mem_amalgam_cell] at hr
      rw [h.mem_middle_private le_rfl hq]
      omega
    have hmeet := h.hat_meets_W (a := ω.widthZ - 1) (r := r') (by omega) (by omega) hu'.1 hu'.2
    refine hIV 0 0 (ω.cell ω.widthZ r) ?_ (ω.cell (ω.widthZ - 1) r') ?_ hadj
    · change _ ∧ _
      rw [zero_smul, translate_zero, cell_add_e]
      exact ⟨hmid _ hu.1, hmid _ hu.2⟩
    · rw [zero_smul, translate_zero]
      rcases hmeet with hW | hW
      · exact Or.inr ⟨hW, mem_periodicUnion_of_amalgam (by rw [cell_add_e]; exact hu'.2)⟩
      · exact Or.inl ⟨mem_periodicUnion_of_amalgam hu'.1, by rw [cell_add_e]; exact hW⟩
  · intro u hu u' hu' hadj hc hc'
    rw [Finset.mem_filter] at hu hu'
    obtain ⟨a, r, rfl⟩ := ω.exists_cell u
    obtain ⟨a', r', rfl⟩ := ω.exists_cell u'
    rw [content_cell] at hc hc'
    rw [cell_add_e] at hu hu'
    have ha : a = 0 := by omega
    have ha' : a' = -1 := by omega
    subst ha ha'
    have hmid : ∀ r'' : ℤ, ω.cell (-1) r'' ∈ ω.amalgam →
        ω.cell (-1) r'' + ω.v ∈ ω.middle := by
      intro r'' hr
      rw [h.mem_amalgam_cell] at hr
      rw [cell_add_v, h.mem_middle_private (by omega) (by omega)]
      omega
    have hmeet := h.hat_meets_W (a := 0) (r := r) le_rfl (by omega) hu.1 hu.2
    refine hIV (-1) 0 (ω.cell (-1) r') ?_ (ω.cell 0 r) ?_ hadj.symm'
    · change _ ∧ _
      rw [mem_translate, mem_translate, cell_add_e]
      refine ⟨?_, ?_⟩
      · simpa using hmid _ hu'.1
      · simpa using hmid _ hu'.2
    · rw [zero_smul, translate_zero]
      rcases hmeet with hW | hW
      · exact Or.inr ⟨hW, mem_periodicUnion_of_amalgam (by rw [cell_add_e]; exact hu.2)⟩
      · exact Or.inl ⟨mem_periodicUnion_of_amalgam hu.1, by rw [cell_add_e]; exact hW⟩

/-! ### The three factors are skew diagrams of small span -/

theorem IsLegal.isSkew_W (hω : ω.IsLegal) : IsSkew ω.W := by
  rcases hω.1.2 with hemp | hnon
  · rw [hemp.1]; intro x hx; simp at hx
  · exact hnon.2.1.1

theorem IsLegal.isSkew_middle (hω : ω.IsLegal) : IsSkew ω.middle := by
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hω.2.2.2.1
  intro x hx y hy hxy1 hxy2 i hi j hj
  have hx' := Finset.mem_sdiff.mp hx
  have hy' := Finset.mem_sdiff.mp hy
  simp only [Finset.mem_union, not_or] at hx' hy'
  have a1 := h1 x (Finset.mem_sdiff.mpr ⟨hx'.1, hx'.2.1⟩) y
    (Finset.mem_sdiff.mpr ⟨hy'.1, hy'.2.1⟩) hxy1 hxy2 i hi j hj
  have a2 := h2 x (Finset.mem_sdiff.mpr ⟨hx'.1, hx'.2.2⟩) y
    (Finset.mem_sdiff.mpr ⟨hy'.1, hy'.2.2⟩) hxy1 hxy2 i hi j hj
  obtain ⟨b1, -⟩ := Finset.mem_sdiff.mp a1
  obtain ⟨-, b2⟩ := Finset.mem_sdiff.mp a1
  obtain ⟨-, c2⟩ := Finset.mem_sdiff.mp a2
  exact Finset.mem_sdiff.mpr ⟨b1, by rw [Finset.mem_union, not_or]; exact ⟨b2, c2⟩⟩

theorem IsLegal.isSkew_hatMiddleFin (hω : ω.IsLegal) : IsSkew (Plan.hatMiddleFin ω) :=
  isSkew_hat hω.isSkew_middle

theorem IsLegal.isSkew_hatMarkFin (hω : ω.IsLegal) : IsSkew (Plan.hatMarkFin ω) := by
  by_cases hW : ω.W = ∅
  · have : Plan.hatMarkFin ω = ∅ := by
      ext x
      rw [mem_hatMarkFin, hW]
      simp
    rw [this]; intro x hx; simp at hx
  · have hl : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    rw [hl.hatMarkFin_eq]
    exact hl.isSkew_hatBand

theorem IsLegal.span_W_lt (hω : ω.IsLegal) : span ω.W < ω.period.toNat := by
  have := hω.2.2.1.2
  have h2 : span ω.W = ω.width := rfl
  omega

theorem IsLegal.span_hatMarkFin_lt (hω : ω.IsLegal) :
    span (Plan.hatMarkFin ω) < ω.period.toNat := by
  have hn := hω.2.2.1
  by_cases hW : ω.W = ∅
  · have : Plan.hatMarkFin ω = ∅ := by
      ext x
      rw [mem_hatMarkFin, hW]
      simp
    rw [this]
    have : (0 : ℕ) < ω.period.toNat := by
      have := hn.1; have := hn.2; unfold MarkedInner.width at *; omega
    simpa [span, contents] using this
  · have hl : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have hsub : contents (Plan.hatMarkFin ω) ⊆
        Finset.Icc (minContent ω.E) (minContent ω.E + ω.widthZ - 1) := by
      intro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      rw [hl.hatMarkFin_eq, hatBand, Finset.mem_filter] at hx
      exact Finset.mem_Icc.mpr hx.2
    have h1 := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    have := hω.2.2.1.2
    have h2 : (ω.width : ℤ) = ω.widthZ := rfl
    unfold span
    omega

theorem IsLegal.span_hatMiddleFin_lt (hω : ω.IsLegal) :
    span (Plan.hatMiddleFin ω) < ω.period.toNat := by
  have hn := hω.2.2.1
  have hq : 0 < ω.period := by
    have := hn.1; have := hn.2; unfold MarkedInner.width at *; omega
  have hwf := hω.1
  have hcE := hwf.contents_eq
  have hmem : ∀ x ∈ Plan.hatMiddleFin ω, x ∈ ω.middle ∧ x + eCell ∈ ω.middle := by
    intro x hx
    unfold Plan.hatMiddleFin at hx
    exact Finset.mem_filter.mp hx
  have hEmem : ∀ x ∈ ω.middle, minContent ω.E ≤ content x ∧
      content x ≤ minContent ω.E + ω.period + ω.width - 1 := by
    intro x hx
    have := content_mem_contents (Finset.mem_sdiff.mp hx).1
    rw [hcE, Finset.mem_Icc] at this
    exact this
  by_cases hW : ω.W = ∅
  · have hw0 : ω.width = 0 := by simp [width, hW, span, contents]
    have hE := hwf.1
    have hD := isConnectedSkew_iff_diagonal.mp hE
    have hEne : ω.E.Nonempty := hE.2.1
    have hsub : contents (Plan.hatMiddleFin ω) ⊆
        Finset.Icc (minContent ω.E + 1) (minContent ω.E + ω.period - 1) := by
      intro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hx1, hx2⟩ := hmem x hx
      have b1 := hEmem x hx1
      have b2 := hEmem _ hx2
      rw [content_add] at b2
      have hc : content eCell = 0 := by simp [content, eCell]
      rw [hc] at b2
      rw [Finset.mem_Icc]
      refine ⟨?_, by omega⟩
      by_contra hlt
      have hceq : content x = minContent ω.E := by omega
      have hsing := hD.2.2.2.2 (minContent ω.E) (minContent_mem hEne)
        (Or.inl (fun hm => by have := minContent_le hm; omega))
      have e1 := diagLo_le (D := ω.E) (k := minContent ω.E) (i := x.1) (j := x.2)
        (Finset.mem_sdiff.mp hx1).1 (by simpa [content] using hceq)
      have e2 := le_diagHi (D := ω.E) (k := minContent ω.E) (i := (x + eCell).1)
        (j := (x + eCell).2) (Finset.mem_sdiff.mp hx2).1
        (by simp only [content] at b2 ⊢; simp [eCell]; simp only [content] at hceq; omega)
      simp [eCell] at e2
      omega
    have h1 := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    unfold span
    omega
  · have hl : ω.IsLegalNonempty := ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have hw1 := hl.width_pos
    have hwq := hl.width_lt_period
    have hsub : contents (Plan.hatMiddleFin ω) ⊆
        Finset.Icc (minContent ω.E + ω.widthZ) (minContent ω.E + ω.period - 1) := by
      intro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hx1, hx2⟩ := hmem x hx
      have b1 := hEmem x hx1
      have hc : content (x + eCell) = content x := content_eCell_add x
      have hne : x + eCell ≠ x := by simp [eCell]
      have h2 : ω.width = ω.widthZ := rfl
      rw [Finset.mem_Icc]
      constructor
      · by_contra hlt
        exact hne (hl.middle_thin hx2 hx1 hc (Or.inl (by omega)))
      · by_contra hlt
        exact hne (hl.middle_thin hx2 hx1 hc (Or.inr (by omega)))
    have h1 := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    unfold span
    omega

/-! ### Checks -/

/-- The hatted marks of the worked marks are the band cuts of the amalgam. -/
example : Plan.hatMarkFin chartFigureInner = chartFigureInner.hatBand := by decide +kernel
example : Plan.hatMarkFin gaugeInnerA = gaugeInnerA.hatBand := by decide +kernel
example : Plan.hatMarkFin hookInner = hookInner.hatBand := by decide +kernel

example : IsSkew chartFigureInner.amalgam := by decide +kernel
example : IsSkew gaugeInnerA.amalgam := by decide +kernel
example : IsSkew hookInner.amalgam := by decide +kernel

example : IsSkew (Plan.hatMarkFin chartFigureInner) := by decide +kernel
example : IsSkew (Plan.hatMarkFin gaugeInnerA) := by decide +kernel
example : IsSkew (Plan.hatMarkFin hookInner) := by decide +kernel
example : IsSkew (Plan.hatMiddleFin hookInner) := by decide +kernel

end MarkedInner

end SkewMarkedFactor.Gluing
