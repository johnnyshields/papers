/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Local/Caps.lean
import SkewMarkedFactor.Gluing.Local.Middle

/-!
# End caps of a legal mark

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-caps`, the bits `B_w = 1`, `B_q = 0` of case (d)) and the endpoint conditions used in
`lem:gluing-local` (3).

The last marked diagonal of the lower copy is a single cell, because `W₋ + v` lies in the singleton
diagonal `N - 1` of `E`.  Together with the private singleton `E_w` this fixes the bits
`A_w = ℓ_{w-1} - ℓ_w` and `B_w = h_{w-1} - h_w` in terms of the lower attachment; the upper end
follows by rotation.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

variable {ω : MarkedInner}

/-- If the last lower marked diagonal has no tail, the lower attachment neighbor of the cell of
the private diagonal `w` lies in `W₋`. -/
theorem IsLegalNonempty.attach_w_cell (h : ω.IsLegalNonempty) (ht : ¬ ω.TailLower (ω.widthZ - 1)) :
    (ω.LowerH → ω.cell (ω.widthZ - 1) (ω.lo ω.widthZ) ∈ ω.W) ∧
    (ω.LowerV → ω.cell (ω.widthZ - 1) (ω.lo ω.widthZ + 1) ∈ ω.W) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hsing := h.lo_w_eq_hi_w
  have hl := h.lo_le_hi (a := ω.widthZ) (by omega) (by omega)
  have hxm : ω.cell ω.widthZ (ω.lo ω.widthZ) ∈ ω.middle :=
    (h.mem_middle_private (le_refl _) hq).mpr ⟨le_refl _, hl⟩
  have hle : minContent ω.middle ≤ minContent ω.E + ω.widthZ := by
    have := minContent_le (content_mem_contents hxm)
    rwa [content_cell] at this
  have key : ∀ x ∈ ω.middle, content x = minContent ω.middle → ∃ r, x = ω.cell ω.widthZ r ∧
      r = ω.lo ω.widthZ := by
    intro x hx hxc
    obtain ⟨a, r, rfl⟩ := ω.exists_cell x
    rw [content_cell] at hxc
    have hE := (h.mem_E).mp (h.mem_middle.mp hx).1
    have haw : a ≤ ω.widthZ := by omega
    by_cases hlt : a < ω.widthZ
    · exfalso
      have hxe : ω.cell a r ∈ ω.E \ ω.W :=
        Finset.mem_sdiff.mpr ⟨(h.mem_middle.mp hx).1, (h.mem_middle.mp hx).2.1⟩
      exact ht (h.tail_mono (by omega) (by omega) (le_refl _)
        (h.tail_of_cell (by omega) (by omega) hxe))
    · have : a = ω.widthZ := by omega
      subst this
      have := (h.mem_middle_private (le_refl _) hq).mp hx
      exact ⟨r, rfl, by omega⟩
  constructor
  · rintro ⟨x, hx, hxc, hxW⟩
    obtain ⟨r, rfl, hr⟩ := key x hx hxc
    have e : ((ω.cell ω.widthZ r).1, (ω.cell ω.widthZ r).2 - 1) = ω.cell (ω.widthZ - 1) r := by
      simp only [cell]; ext
      · rfl
      · simp only; ring
    rw [e] at hxW
    rwa [hr] at hxW
  · rintro ⟨x, hx, hxc, hxW⟩
    obtain ⟨r, rfl, hr⟩ := key x hx hxc
    have e : ((ω.cell ω.widthZ r).1 + 1, (ω.cell ω.widthZ r).2) =
        ω.cell (ω.widthZ - 1) (r + 1) := by
      simp only [cell]; ext
      · rfl
      · simp only; ring
    rw [e] at hxW
    rwa [hr] at hxW

/-- The lower end cap for a horizontal lower attachment (cases (a), (c)). -/
theorem IsLegalNonempty.lower_caps_H (h : ω.IsLegalNonempty) (hH : ω.LowerH) :
    ω.dLo (ω.widthZ - 1) = 0 ∧ ω.lo (ω.widthZ - 1) = ω.lo ω.widthZ ∧
      ω.dHi (ω.widthZ - 1) + (ω.hi (ω.widthZ - 1) - ω.hi ω.widthZ) = 0 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hsing := h.lo_w_eq_hi_w
  obtain ⟨l1, l2⟩ := h.last_dLo
  obtain ⟨t1, t2⟩ := h.thin_lower (ω.widthZ - 1) (by omega) (le_refl _)
  have hlast : ω.lo (ω.widthZ - 1 + ω.period) = ω.hi (ω.widthZ - 1 + ω.period) := by
    have e : ω.widthZ - 1 + ω.period = ω.period + ω.widthZ - 1 := by ring
    rw [e]; exact h.lo_last
  have hd0 := h.lowerH_dLo hH (a := ω.widthZ - 1) (by omega) (le_refl _)
  have bA := h.bit_lo' (a := ω.widthZ - 1) (b := ω.widthZ) (by ring) (by omega) (by omega)
  have bB := h.bit_hi' (a := ω.widthZ - 1) (b := ω.widthZ) (by ring) (by omega) (by omega)
  obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row (a := ω.widthZ - 1) (by omega) (le_refl _)
  unfold dLo dHi at *
  by_cases hT : ω.TailLower (ω.widthZ - 1)
  · unfold TailLower dLo dHi at hT
    refine ⟨by omega, by omega, by omega⟩
  · have := (h.attach_w_cell hT).1 hH
    have hm := h.mem_W.mp this
    unfold TailLower dLo dHi at hT
    omega

/-- The lower end cap for a vertical lower attachment (cases (b), (d)). -/
theorem IsLegalNonempty.lower_caps_V (h : ω.IsLegalNonempty) (hV : ω.LowerV) :
    ω.dHi (ω.widthZ - 1) = 0 ∧ ω.hi (ω.widthZ - 1) - ω.hi ω.widthZ = 1 ∧
      ω.dLo (ω.widthZ - 1) + (ω.lo (ω.widthZ - 1) - ω.lo ω.widthZ) = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hsing := h.lo_w_eq_hi_w
  obtain ⟨l1, l2⟩ := h.last_dLo
  obtain ⟨t1, t2⟩ := h.thin_lower (ω.widthZ - 1) (by omega) (le_refl _)
  have hlast : ω.lo (ω.widthZ - 1 + ω.period) = ω.hi (ω.widthZ - 1 + ω.period) := by
    have e : ω.widthZ - 1 + ω.period = ω.period + ω.widthZ - 1 := by ring
    rw [e]; exact h.lo_last
  have hd0 := h.lowerV_dHi hV (a := ω.widthZ - 1) (by omega) (le_refl _)
  have bA := h.bit_lo' (a := ω.widthZ - 1) (b := ω.widthZ) (by ring) (by omega) (by omega)
  have bB := h.bit_hi' (a := ω.widthZ - 1) (b := ω.widthZ) (by ring) (by omega) (by omega)
  obtain ⟨r0, a0, a1, a2, a3⟩ := h.W_row (a := ω.widthZ - 1) (by omega) (le_refl _)
  unfold dLo dHi at *
  by_cases hT : ω.TailLower (ω.widthZ - 1)
  · unfold TailLower dLo dHi at hT
    refine ⟨by omega, by omega, by omega⟩
  · have := (h.attach_w_cell hT).2 hV
    have hm := h.mem_W.mp this
    unfold TailLower dLo dHi at hT
    omega

/-- The upper end cap for a horizontal upper attachment (cases (a), (d)), by rotation. -/
theorem IsLegalNonempty.upper_caps_H (h : ω.IsLegalNonempty) (hH : ω.UpperH) :
    ω.dHi 0 = 0 ∧ ω.hi (ω.period - 1) = ω.hi ω.period ∧
      ω.dLo 0 + (ω.lo (ω.period - 1) - ω.lo ω.period) = 0 := by
  have := h.rotate.lower_caps_H ((lowerH_rotate ω).mpr hH)
  have e0 := h.dLo_rotate 0
  have e1 := h.dHi_rotate 0
  simp only [sub_zero] at e0 e1
  rw [widthZ_rotate, e0, e1] at this
  simp only [h.lo_rotate, h.hi_rotate] at this
  have f1 : ω.period + ω.widthZ - 1 - (ω.widthZ - 1) = ω.period := by ring
  have f2 : ω.period + ω.widthZ - 1 - ω.widthZ = ω.period - 1 := by ring
  rw [f1, f2] at this
  omega

/-- The upper end cap for a vertical upper attachment (cases (b), (c)), by rotation. -/
theorem IsLegalNonempty.upper_caps_V (h : ω.IsLegalNonempty) (hV : ω.UpperV) :
    ω.dLo 0 = 0 ∧ ω.lo (ω.period - 1) - ω.lo ω.period = 1 ∧
      ω.dHi 0 + (ω.hi (ω.period - 1) - ω.hi ω.period) = 1 := by
  have := h.rotate.lower_caps_V ((lowerV_rotate ω).mpr hV)
  have e0 := h.dLo_rotate 0
  have e1 := h.dHi_rotate 0
  simp only [sub_zero] at e0 e1
  rw [widthZ_rotate, e0, e1] at this
  simp only [h.lo_rotate, h.hi_rotate] at this
  have f1 : ω.period + ω.widthZ - 1 - (ω.widthZ - 1) = ω.period := by ring
  have f2 : ω.period + ω.widthZ - 1 - ω.widthZ = ω.period - 1 := by ring
  rw [f1, f2] at this
  omega

end MarkedInner

end SkewMarkedFactor.Gluing
