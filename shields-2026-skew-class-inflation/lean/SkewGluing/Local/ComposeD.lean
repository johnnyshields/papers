-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/Local/ComposeD.lean
import SkewGluing.Local.ComposeMixed

/-!
# Case-(d) composites are connected skew

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3):
`D ∘_ω E` is a connected skew diagram for a connected outer and a legal case-(d) mark;
`eq:gluing-mixed-profile` and the southeast endpoint `se_E(a) + j v`).

In case (d) both copies are southeast-justified, so every diagonal class `(J, a)` of the composite
has last row `J p + h_a`; its first row is the least first row of the copy `J`, the copy `J - 1`
and the supplemental copy.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The last row of the case-(d) composite on the class `(J, a)`: `se_E(a) + J v`. -/
def mixHi (ω : MarkedInner) (J a : ℤ) : ℤ := J * ω.rowShift + ω.hi a

/-- The first row of the case-(d) composite on the class `(J, a)`: the least first row over the
present pieces (the copy `J`, the copy `J - 1`, the supplemental copy). -/
def mixLo (ω : MarkedInner) (D : Diagram) (J a : ℤ) : ℤ :=
  if minContent D ≤ J ∧ J ≤ maxContent D then
    (if a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D then
      (if a < ω.widthZ ∧ minContent D + 1 ≤ J ∧ J ≤ maxContent D ∧
          diagHi D (J - 1) - diagHi D J = 1 then
        min (ω.oRowLo D J + ω.lo a)
          (min (ω.oRowLo D (J - 1) + ω.lo (a + ω.period))
            (J * ω.rowShift - diagHi D (J - 1) + diagLo D J +
              max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift)))
       else min (ω.oRowLo D J + ω.lo a) (ω.oRowLo D (J - 1) + ω.lo (a + ω.period)))
     else ω.oRowLo D J + ω.lo a)
  else ω.oRowLo D (J - 1) + ω.lo (a + ω.period)

theorem d_E_facts (h : ω.IsLegalNonempty) (hc : ω.case = .d) {s t : ℤ} (hp : ω.IsPhases s t)
    {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ ω.widthZ - 1) :
    ω.dHi a = 0 ∧ -1 ≤ ω.dLo a ∧ ω.dLo a ≤ 1 ∧ (a < t → ω.dLo a < 0) ∧ (t ≤ a → 0 ≤ ω.dLo a) ∧
      (s ≤ a → 0 < ω.dLo a) ∧ (a < s → ω.dLo a ≤ 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hp
  have e1 := h.sides_d hc h0 h1
  have e2 := h.thin_lower a h0 h1
  have e3 := h.thin_upper h0 h1
  have e4 := hS a h0 h1
  have e5 := hT a h0 h1
  unfold TailLower at e4
  unfold TailUpper at e5
  refine ⟨e1, by omega, by omega, fun hh => ?_, fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
  · have := e5.mpr hh; omega
  · by_contra hn
    have := e5.mp (by omega); omega
  · have := e4.mpr hh; omega
  · by_contra hn
    have := e4.mp (by omega); omega

theorem d_caps (h : ω.IsLegalNonempty) (hc : ω.case = .d) :
    (ω.dHi (ω.widthZ - 1) = 0 ∧ ω.hi (ω.widthZ - 1) - ω.hi ω.widthZ = 1 ∧
      ω.dLo (ω.widthZ - 1) + (ω.lo (ω.widthZ - 1) - ω.lo ω.widthZ) = 1) ∧
    (ω.dHi 0 = 0 ∧ ω.hi (ω.period - 1) = ω.hi ω.period ∧
      ω.dLo 0 + (ω.lo (ω.period - 1) - ω.lo ω.period) = 0) := by
  obtain ⟨hl, hu⟩ := h.attach.2.2.2 hc
  exact ⟨h.lower_caps_V hl, h.upper_caps_H hu⟩


theorem mix_rows (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) {J a r : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period) :
    ω.cell (J * ω.period + a) r ∈ ω.compose D ↔
      ValidClass (minContent D) (maxContent D) ω.widthZ J a ∧
        ω.mixLo D J a ≤ r ∧ r ≤ ω.mixHi J a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [h.cell_mem_compose_d hD hc ha0 haq]
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have l1 := h.lo_le_hi (a := a) ha0 (by omega)
  have l2 : a < ω.widthZ → ω.lo (a + ω.period) ≤ ω.hi (a + ω.period) :=
    fun ha => h.lo_le_hi (by omega) (by omega)
  have fa : a < ω.widthZ → ω.dHi a = 0 := fun ha => (d_E_facts h hc hph ha0 (by omega)).1
  have o1 := oRow_le (ω := ω) hD (j := J)
  have o2 := oRow_le (ω := ω) hD (j := J - 1)
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  simp only [dHi] at fa
  unfold ValidClass mixLo mixHi
  simp only [oRowLo, oRowHi, hc, hp] at o1 o2 ⊢
  split_ifs <;> omega

theorem mix_ne (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a) (haq : a < ω.period)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    ω.mixLo D J a ≤ ω.mixHi J a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have l1 := h.lo_le_hi (a := a) ha0 (by omega)
  have l2 : a < ω.widthZ → ω.lo (a + ω.period) ≤ ω.hi (a + ω.period) :=
    fun ha => h.lo_le_hi (by omega) (by omega)
  have fa : a < ω.widthZ → ω.dHi a = 0 := fun ha => (d_E_facts h hc hph ha0 (by omega)).1
  have o1 := oRow_le (ω := ω) hD (j := J)
  have o2 := oRow_le (ω := ω) hD (j := J - 1)
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  simp only [dHi] at fa
  unfold ValidClass at hv
  unfold mixLo mixHi
  simp only [oRowLo, oRowHi, hc, hp] at o1 o2 ⊢
  split_ifs <;> omega



theorem mixLo_P1 {J a : ℤ} (hV1 : minContent D ≤ J ∧ J ≤ maxContent D)
    (hV2 : ¬ (a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D)) :
    ω.mixLo D J a = ω.oRowLo D J + ω.lo a := by
  unfold mixLo; split_ifs; rfl

theorem mixLo_P2 {J a : ℤ} (hV1 : ¬ (minContent D ≤ J ∧ J ≤ maxContent D)) :
    ω.mixLo D J a = ω.oRowLo D (J - 1) + ω.lo (a + ω.period) := by
  unfold mixLo; split_ifs; rfl

theorem mixLo_all0 {J a : ℤ} (hV1 : minContent D ≤ J ∧ J ≤ maxContent D)
    (hV2 : a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D)
    (hV3 : ¬ diagHi D (J - 1) - diagHi D J = 1) :
    ω.mixLo D J a = min (ω.oRowLo D J + ω.lo a) (ω.oRowLo D (J - 1) + ω.lo (a + ω.period)) := by
  unfold mixLo; split_ifs <;> first | rfl | (exfalso; omega)

theorem mixLo_all1 {J a : ℤ} (hV1 : minContent D ≤ J ∧ J ≤ maxContent D)
    (hV2 : a < ω.widthZ ∧ minContent D ≤ J - 1 ∧ J - 1 ≤ maxContent D)
    (hV3 : diagHi D (J - 1) - diagHi D J = 1) :
    ω.mixLo D J a = min (ω.oRowLo D J + ω.lo a)
      (min (ω.oRowLo D (J - 1) + ω.lo (a + ω.period))
        (J * ω.rowShift - diagHi D (J - 1) + diagLo D J +
          max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift))) := by
  unfold mixLo; split_ifs <;> first | rfl | (exfalso; omega)

theorem d_dLo_regions (h : ω.IsLegalNonempty) (hc : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t)
    (hlt : t < s) {a : ℤ} (h1 : 1 ≤ a) (h2 : a ≤ ω.widthZ - 1) :
    (ω.dLo (a - 1) = -1 ∧ ω.dLo a = -1) ∨ (ω.dLo (a - 1) = -1 ∧ ω.dLo a = 0) ∨
    (ω.dLo (a - 1) = 0 ∧ ω.dLo a = 0) ∨ (ω.dLo (a - 1) = 0 ∧ ω.dLo a = 1) ∨
    (ω.dLo (a - 1) = 1 ∧ ω.dLo a = 1) := by
  have fa := d_E_facts h hc hph (a := a) (by omega) (by omega)
  have fa1 := d_E_facts h hc hph (a := a - 1) (by omega) (by omega)
  omega

theorem mix_stepA_lo (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {J a : ℤ} (h1 : 1 ≤ a) (h2 : a < ω.period)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    ω.mixLo D J (a - 1) - ω.mixLo D J a = 0 ∨ ω.mixLo D J (a - 1) - ω.mixLo D J a = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have b1 := h.bit_lo' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  unfold ValidClass at hv
  by_cases hJm : J = minContent D
  · subst hJm
    rw [mixLo_P1 (by omega) (by omega), mixLo_P1 (by omega) (by omega)]
    omega
  by_cases hJM : J = maxContent D + 1
  · subst hJM
    have haw : a < ω.widthZ := by omega
    have b2 := h.bit_lo' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega)
      (by omega)
    rw [mixLo_P2 (by omega), mixLo_P2 (by omega)]
    simp only [add_sub_cancel_right]
    omega
  have hJ : minContent D + 1 ≤ J ∧ J ≤ maxContent D := by omega
  have hb := D_bits hD hJ.1 hJ.2
  have hdl := diagLo_le_diagHi (isConnectedSkew_iff_diagonal.mp hD |>.mem_contents_iff.mpr
    ⟨by omega, hJ.2⟩ : J ∈ contents D)
  by_cases haw : ω.widthZ + 1 ≤ a
  · rw [mixLo_P1 (by omega) (by omega), mixLo_P1 (by omega) (by omega)]
    omega
  by_cases haw' : a = ω.widthZ
  · subst haw'
    have hcp := (d_caps h hc).1
    simp only [dLo, dHi] at hcp
    rw [mixLo_P1 (a := ω.widthZ) (by omega) (by omega)]
    by_cases hB : diagHi D (J - 1) - diagHi D J = 1
    · rw [mixLo_all1 (a := ω.widthZ - 1) (by omega) (by omega) hB]
      simp only [oRowLo, hc, hp]
      omega
    · rw [mixLo_all0 (a := ω.widthZ - 1) (by omega) (by omega) hB]
      simp only [oRowLo, hc, hp]
      omega
  · have haw : a < ω.widthZ := by omega
    have b2 := h.bit_lo' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega)
      (by omega)
    have fa := d_dLo_regions h hc hph hlt (a := a) h1 (by omega)
    have fa0 := (d_E_facts h hc hph (a := a) (by omega) (by omega)).1
    simp only [dLo, dHi] at fa fa0
    by_cases hB : diagHi D (J - 1) - diagHi D J = 1
    · rw [mixLo_all1 (by omega) (by omega) hB, mixLo_all1 (by omega) (by omega) hB]
      simp only [oRowLo, hc, hp]
      omega
    · rw [mixLo_all0 (by omega) (by omega) hB, mixLo_all0 (by omega) (by omega) hB]
      simp only [oRowLo, hc, hp]
      omega

theorem mix_stepA_hi (h : ω.IsLegalNonempty) {J a : ℤ} (h1 : 1 ≤ a) (h2 : a < ω.period) :
    ω.mixHi J (a - 1) - ω.mixHi J a = 0 ∨ ω.mixHi J (a - 1) - ω.mixHi J a = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have b1 := h.bit_hi' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
  unfold mixHi
  omega


theorem mix_stepB_lo (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) {J : ℤ}
    (hv1 : ValidClass (minContent D) (maxContent D) ω.widthZ J (ω.period - 1))
    (hv2 : ValidClass (minContent D) (maxContent D) ω.widthZ (J + 1) 0) :
    ω.mixLo D J (ω.period - 1) - ω.mixLo D (J + 1) 0 = 0 ∨
      ω.mixLo D J (ω.period - 1) - ω.mixLo D (J + 1) 0 = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have b1 := h.bit_lo' (a := ω.period - 1) (b := ω.period) (by ring) (by omega) (by omega)
  have hcp := (d_caps h hc).2
  have f0 := d_E_facts h hc hph (a := 0) (le_refl _) (by omega)
  simp only [dLo, dHi] at hcp f0
  simp only [zero_add] at hcp f0
  unfold ValidClass at hv1 hv2
  have hJ : minContent D ≤ J ∧ J ≤ maxContent D := by omega
  have hp : (J + 1) * ω.rowShift = J * ω.rowShift + ω.rowShift := by ring
  rw [mixLo_P1 (by omega) (by omega)]
  by_cases hJM : J + 1 ≤ maxContent D
  · have hb := D_bits hD (J := J + 1) (by omega) hJM
    simp only [add_sub_cancel_right] at hb
    have hdl := diagLo_le_diagHi (isConnectedSkew_iff_diagonal.mp hD |>.mem_contents_iff.mpr
      ⟨by omega, hJM⟩ : J + 1 ∈ contents D)
    by_cases hB : diagHi D (J + 1 - 1) - diagHi D (J + 1) = 1
    · rw [mixLo_all1 (by omega) (by omega) hB]
      simp only [oRowLo, hc, hp, add_sub_cancel_right, zero_add] at hB ⊢
      omega
    · rw [mixLo_all0 (by omega) (by omega) hB]
      simp only [oRowLo, hc, hp, add_sub_cancel_right, zero_add] at hB ⊢
      omega
  · rw [mixLo_P2 (by omega)]
    simp only [oRowLo, hc, add_sub_cancel_right, zero_add]
    omega

theorem mix_stepB_hi (h : ω.IsLegalNonempty) (hc : ω.case = .d) {J : ℤ} :
    ω.mixHi J (ω.period - 1) - ω.mixHi (J + 1) 0 = 0 ∨
      ω.mixHi J (ω.period - 1) - ω.mixHi (J + 1) 0 = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hcp := (d_caps h hc).2
  simp only [dLo, dHi] at hcp
  simp only [zero_add] at hcp
  have hp : (J + 1) * ω.rowShift = J * ω.rowShift + ω.rowShift := by ring
  unfold mixHi
  omega

theorem mix_first (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d) :
    ω.mixLo D (minContent D) 0 = ω.mixHi (minContent D) 0 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have he := D_ends hD
  have h0 := h.lo_zero
  rw [mixLo_P1 (by omega) (by omega)]
  unfold mixHi
  simp only [oRowLo, hc]
  omega

theorem mix_last (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) :
    ω.mixLo D (maxContent D + 1) (ω.widthZ - 1) = ω.mixHi (maxContent D + 1) (ω.widthZ - 1) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have he := D_ends hD
  have hlast : ω.lo (ω.widthZ - 1 + ω.period) = ω.hi (ω.widthZ - 1 + ω.period) := by
    have e : ω.widthZ - 1 + ω.period = ω.period + ω.widthZ - 1 := by ring
    rw [e]; exact h.lo_last
  have f0 := d_E_facts h hc hph (a := ω.widthZ - 1) (by omega) (le_refl _)
  simp only [dLo, dHi] at f0
  have hp : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by ring
  rw [mixLo_P2 (by omega)]
  unfold mixHi
  simp only [oRowLo, hc, add_sub_cancel_right]
  omega

theorem mix_classRows (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) :
    ClassRows (ω.compose D) (minContent ω.E) ω.period ω.widthZ (minContent D) (maxContent D)
      (ω.mixLo D) (ω.mixHi) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  refine ⟨by omega, by omega, hq, hmM, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J a r h0 h1
    exact mix_rows h hD hc hph h0 h1
  · intro J a h0 h1 hv
    exact mix_ne h hD hc hph h0 h1 hv
  · intro J a h1 h2 hv
    exact ⟨mix_stepA_lo h hD hc hph hlt h1 h2 hv, mix_stepA_hi h h1 h2⟩
  · intro J hv1 hv2
    exact ⟨mix_stepB_lo h hD hc hph hv1 hv2, mix_stepB_hi h hc⟩
  · exact mix_first h hD hc
  · intro _
    exact mix_last h hD hc hph
  · intro h0
    omega

/-- **`lem:gluing-local` (3), connectedness, case (d).**  For a legal case-(d) mark with a
nonempty copy and a connected outer, `D ∘_ω E` is a connected skew diagram. -/
theorem IsLegalNonempty.isConnectedSkew_compose_d (h : ω.IsLegalNonempty)
    (hD : IsConnectedSkew D) (hc : ω.case = .d) : IsConnectedSkew (ω.compose D) := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  exact (mix_classRows h hD hc hph (h.phases_lt (Or.inr hc) hph)).isConnectedSkew

end MarkedInner

end SkewGluing
