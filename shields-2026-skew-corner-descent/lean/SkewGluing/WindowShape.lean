/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Local.Diagonals
import SkewGluing.ContentBand

/-!
# Two consecutive legal windows

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`eq:erosion-union`, `eq:cap-hat`).  The overlapping two-copy window is a connected skew diagram.

TODO-COPIED: interval construction copied from skew-factor-gluing.

Sorry-free.
-/

namespace SkewGluing
open Plan.MarkFacts
namespace MarkedInner
variable {ω : MarkedInner}

/-- `dLo a = ℓ_{a+q} - p - ℓ_a`: the northwest offset of `E_{a+q} - v` against `E_a`. -/
def dLo (ω : MarkedInner) (a : ℤ) : ℤ := ω.lo (a + ω.period) - ω.rowShift - ω.lo a

/-- `dHi a = h_{a+q} - p - h_a`: the southeast offset of `E_{a+q} - v` against `E_a`. -/
def dHi (ω : MarkedInner) (a : ℤ) : ℤ := ω.hi (a + ω.period) - ω.rowShift - ω.hi a

/-- Lower-end condition: the southwest cell of `E` lies in `W₋`. -/
theorem IsLegalNonempty.dLo_zero_le (h : ω.IsLegalNonempty) : ω.dLo 0 ≤ 0 ∧ 0 ≤ ω.dHi 0 := by
  have h1 := h.mem_W.mp h.sw_cell
  have h2 := h.lo_zero
  unfold dLo dHi
  omega

/-- Upper-end condition: the northeast cell of `E` lies in `W₊`. -/
theorem IsLegalNonempty.last_dLo (h : ω.IsLegalNonempty) :
    0 ≤ ω.dLo (ω.widthZ - 1) ∧ ω.dHi (ω.widthZ - 1) ≤ 0 := by
  have h1 := h.mem_W.mp h.ne_cell_W
  have h2 := h.lo_last
  have e : ω.widthZ - 1 + ω.period = ω.period + ω.widthZ - 1 := by ring
  unfold dLo dHi
  rw [e]
  omega

/-- The amalgam `E ∪ (E - v)` of two consecutive copies of `E`, overlapping in `W₋`. -/
def amalgam (ω : MarkedInner) : Diagram := ω.E ∪ translate (-ω.v) ω.E

theorem mem_amalgam {x : ℤ × ℤ} : x ∈ ω.amalgam ↔ x ∈ ω.E ∨ x + ω.v ∈ ω.E := by
  unfold amalgam
  rw [Finset.mem_union, mem_translate]
  simp


theorem IsLegalNonempty.mem_amalgam_cell (h : ω.IsLegalNonempty) {a r : ℤ} :
    ω.cell a r ∈ ω.amalgam ↔
      (0 ≤ a ∧ a ≤ ω.period + ω.widthZ - 1 ∧ ω.lo a ≤ r ∧ r ≤ ω.hi a) ∨
      (0 ≤ a + ω.period ∧ a + ω.period ≤ ω.period + ω.widthZ - 1 ∧
        ω.lo (a + ω.period) ≤ r + ω.rowShift ∧ r + ω.rowShift ≤ ω.hi (a + ω.period)) := by
  rw [mem_amalgam, cell_add_v, h.mem_E, h.mem_E]

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

end MarkedInner
end SkewGluing
