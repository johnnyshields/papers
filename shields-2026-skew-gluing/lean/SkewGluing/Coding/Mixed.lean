import SkewGluing.Coding.Ordinary

/-!
# Case-(d) composites: class steps

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`, `eq:gluing-caps`, `eq:gluing-interface`).

In case (d) the last row of the diagonal of `D ∘_ω E` on the class `(J, a)` is `J v₁ + h_a`
(`mixHi`), and the first row has the closed form `mixLo_formula` read off
`eq:gluing-mixed-profile`.  The class steps of the first rows are periodic off the switches `t`, `s`
(`mix_classBitLo_periodic`), read the outer at the switches (`mix_classBitLo_t`,
`mix_classBitLo_s`), and give the caps at the first and last block.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The first row of the case-(d) composite on the class `(J, a)`, minus `J v₁`: on a marked
residue it is the first row of the overlap `W₋` minus the outer height read by the phases
(`eq:gluing-mixed-profile`); on a private residue it is `ℓ_a + 1 - M_J`. -/
def mixGLo (ω : MarkedInner) (D : Diagram) (s t J a : ℤ) : ℤ :=
  if a < ω.widthZ then
    diagLo ω.W (minContent ω.E + a) -
      (if a < t then profM D (J - 1) else if a < s then profS D J - 1 else profM D J)
  else ω.lo a + 1 - profM D J

set_option maxHeartbeats 1600000 in
-- large linear arithmetic goal with many case splits
theorem mixLo_formula (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    ω.mixLo D J a = J * ω.rowShift + ω.mixGLo D s t J a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hb : minContent D + 1 ≤ J → J ≤ maxContent D → _ := fun h1 h2 => D_bits hD h1 h2
  have e1 : J = minContent D ∨ J = maxContent D → diagLo D J = diagHi D J :=
    fun hx => D_end_singleton hD hx
  have e2 : J - 1 = minContent D ∨ J - 1 = maxContent D → diagLo D (J - 1) = diagHi D (J - 1) :=
    fun hx => D_end_singleton hD hx
  have oa : a ≤ ω.widthZ - 1 → _ := fun h2 => d_E_facts h hc hph ha0 h2
  have hW : a ≤ ω.widthZ - 1 → _ := fun h2 => h.diagLo_W ha0 h2
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have hlt := h.phases_lt (Or.inr hc) hph
  unfold ValidClass at hv
  unfold dLo dHi at oa
  unfold mixLo mixGLo profM profS
  simp only [oRowLo, hc, hp]
  split_ifs <;> omega

/-- Off the two switches `t, s`, the class steps of the first rows of a case-(d) composite agree
in consecutive blocks. -/
theorem mix_classBitLo_periodic (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hc : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period) (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a)
    (hv' : ValidClass (minContent D) (maxContent D) ω.widthZ (J + 1) a)
    (hJ : a = 0 → minContent D + 1 ≤ J) (hat : a ≠ t) (has : a ≠ s) :
    classBitLo ω.period (ω.mixLo D) J a = classBitLo ω.period (ω.mixLo D) (J + 1) a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  unfold classBitLo
  by_cases ha : a = 0
  · subst ha
    have hv1 := validClass_prev (ω.period - 1) hv (hJ rfl)
    have hv2 := validClass_prev (ω.period - 1) hv' (by omega)
    simp only [add_sub_cancel_right] at hv2
    simp only [ite_true, add_sub_cancel_right]
    rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (by omega) hv2,
      mixLo_formula h hD hc hph (le_refl _) hv, mixLo_formula h hD hc hph (le_refl _) hv']
    unfold mixGLo
    simp only [add_sub_cancel_right]
    have hp : (J + 1) * ω.rowShift = J * ω.rowShift + ω.rowShift := by ring
    have hp' : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
    split_ifs <;> omega
  · have hv1 := validClass_pred hv
    have hv2 := validClass_pred hv'
    simp only [ha, ite_false]
    rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (by omega) hv2,
      mixLo_formula h hD hc hph ha0 hv, mixLo_formula h hD hc hph ha0 hv']
    unfold mixGLo
    have hp : (J + 1) * ω.rowShift = J * ω.rowShift + ω.rowShift := by ring
    split_ifs <;> omega

/-- The facts about `E` used to compute the class steps at the marked residues `a - 1`, `a`
(`1 ≤ a ≤ w`) of a case-(d) mark: the bits `ℓ_{a-1} - ℓ_a` of `E` and of its upper copy, the offsets
`dLo` read by the phases, the first rows of `W₋`, and the end cap at `a = w`. -/
theorem mix_lo_data (h : ω.IsLegalNonempty) (hc : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t)
    {a : ℤ} (h1 : 1 ≤ a) (h2 : a ≤ ω.widthZ) :
    (ω.lo (a - 1) - ω.lo a = 0 ∨ ω.lo (a - 1) - ω.lo a = 1) ∧
    (a ≤ ω.widthZ - 1 → ω.lo (a - 1 + ω.period) - ω.lo (a + ω.period) = 0 ∨
      ω.lo (a - 1 + ω.period) - ω.lo (a + ω.period) = 1) ∧
    (-1 ≤ ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) ∧
      ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) ≤ 1 ∧
      (a - 1 < t → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) < 0) ∧
      (t ≤ a - 1 → 0 ≤ ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1)) ∧
      (s ≤ a - 1 → 0 < ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1)) ∧
      (a - 1 < s → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) ≤ 0)) ∧
    (a ≤ ω.widthZ - 1 →
      -1 ≤ ω.lo (a + ω.period) - ω.rowShift - ω.lo a ∧
      ω.lo (a + ω.period) - ω.rowShift - ω.lo a ≤ 1 ∧
      (a < t → ω.lo (a + ω.period) - ω.rowShift - ω.lo a < 0) ∧
      (t ≤ a → 0 ≤ ω.lo (a + ω.period) - ω.rowShift - ω.lo a) ∧
      (s ≤ a → 0 < ω.lo (a + ω.period) - ω.rowShift - ω.lo a) ∧
      (a < s → ω.lo (a + ω.period) - ω.rowShift - ω.lo a ≤ 0)) ∧
    (a = ω.widthZ → ω.lo (a - 1 + ω.period) - ω.rowShift - ω.lo (a - 1) + (ω.lo (a - 1) - ω.lo a)
      = 1) ∧
    diagLo ω.W (minContent ω.E + (a - 1)) =
      max (ω.lo (a - 1)) (ω.lo (a - 1 + ω.period) - ω.rowShift) ∧
    (a ≤ ω.widthZ - 1 → diagLo ω.W (minContent ω.E + a) =
      max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift)) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have f0 := d_E_facts h hc hph (a := a - 1) (by omega) (by omega)
  have b1 := h.bit_lo' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
  refine ⟨b1, fun h3 => h.bit_lo' (a := a - 1 + ω.period) (b := a + ω.period) (by ring)
    (by omega) (by omega), ?_, fun h3 => ?_, fun h3 => ?_, h.diagLo_W (by omega) (by omega),
    fun h3 => h.diagLo_W (by omega) h3⟩
  · unfold dLo at f0
    omega
  · have f1 := d_E_facts h hc hph (a := a) (by omega) h3
    unfold dLo at f1
    omega
  · have hcp := (d_caps h hc).1
    simp only [dLo, dHi] at hcp
    subst h3
    omega

/-- The first-row class step at the switch `t` of a case-(d) composite on the block `J` with
`m < J ≤ M` is the bit `A^D_J` of the outer (`eq:gluing-interface`). -/
theorem mix_classBitLo_t (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D) :
    classBitLo ω.period (ω.mixLo D) J t = bitA D J := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hb := D_bits hD hJ1 hJ2
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J t := Or.inl ⟨by omega, hJ2⟩
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  unfold classBitLo
  by_cases ht0 : t = 0
  · subst ht0
    have hv1 := validClass_prev (ω.period - 1) hv hJ1
    simp only [ite_true]
    rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (le_refl _) hv]
    have hcp := (d_caps h hc).2
    have f0 := d_E_facts h hc hph (a := 0) (le_refl _) (by omega)
    have hW0 := h.diagLo_W (a := 0) (le_refl _) (by omega)
    simp only [dLo, dHi, zero_add, add_zero] at hcp f0 hW0
    unfold mixGLo profM profS bitA
    simp only [hp, add_zero]
    split_ifs <;> omega
  · have hv1 := validClass_pred hv
    simp only [ht0, ite_false]
    rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph ht1 hv]
    have F := mix_lo_data h hc hph (a := t) (by omega) (by omega)
    unfold mixGLo profM profS bitA
    split_ifs <;> omega

/-- The first-row class step at the switch `s` of a case-(d) composite on the block `J` with
`m < J ≤ M` is `1 - B^D_J` (`eq:gluing-interface`). -/
theorem mix_classBitLo_s (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D) :
    classBitLo ω.period (ω.mixLo D) J s = 1 - bitB D J := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hb := D_bits hD hJ1 hJ2
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J s := Or.inl ⟨by omega, hJ2⟩
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  unfold classBitLo
  have hv1 := validClass_pred hv
  simp only [show s ≠ 0 by omega, ite_false]
  rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (by omega) hv]
  have F := mix_lo_data h hc hph (a := s) hs1 hs2
  unfold mixGLo profM profS bitB
  split_ifs <;> omega

/-- The first-row class step at the switch `t ≥ 1` of the first block of a case-(d) composite is
one (`eq:gluing-caps`, initial). -/
theorem mix_classBitLo_init_t (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (ht : 1 ≤ t) :
    classBitLo ω.period (ω.mixLo D) (minContent D) t = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) t :=
    Or.inl ⟨le_refl _, hmM⟩
  have he := D_end_singleton hD (x := minContent D) (Or.inl rfl)
  unfold classBitLo
  have hv1 := validClass_pred hv
  simp only [show t ≠ 0 by omega, ite_false]
  rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (by omega) hv]
  have F := mix_lo_data h hc hph (a := t) ht (by omega)
  unfold mixGLo profM profS
  split_ifs <;> omega

/-- The first-row class step at the switch `s` of the first block of a case-(d) composite is one
(`eq:gluing-caps`, initial). -/
theorem mix_classBitLo_init_s (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) :
    classBitLo ω.period (ω.mixLo D) (minContent D) s = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) s :=
    Or.inl ⟨le_refl _, hmM⟩
  have he := D_end_singleton hD (x := minContent D) (Or.inl rfl)
  unfold classBitLo
  have hv1 := validClass_pred hv
  simp only [show s ≠ 0 by omega, ite_false]
  rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (by omega) hv]
  have F := mix_lo_data h hc hph (a := s) hs1 hs2
  unfold mixGLo profM profS
  split_ifs <;> omega

/-- The first-row class step at the switch `t` of the terminal block of a case-(d) composite is
zero (`eq:gluing-caps`, terminal). -/
theorem mix_classBitLo_term_t (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) :
    classBitLo ω.period (ω.mixLo D) (maxContent D + 1) t = 0 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) t :=
    Or.inr ⟨rfl, ht2⟩
  have he := D_end_singleton hD (x := maxContent D) (Or.inr rfl)
  have hp : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by ring
  unfold classBitLo
  by_cases ht0 : t = 0
  · subst ht0
    have hv1 := validClass_prev (ω.period - 1) hv (by omega)
    simp only [ite_true]
    rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (le_refl _) hv]
    have hcp := (d_caps h hc).2
    have f0 := d_E_facts h hc hph (a := 0) (le_refl _) (by omega)
    have hW0 := h.diagLo_W (a := 0) (le_refl _) (by omega)
    simp only [dLo, dHi, zero_add, add_zero] at hcp f0 hW0
    unfold mixGLo profM profS
    simp only [add_sub_cancel_right, hp, add_zero]
    split_ifs <;> omega
  · have hv1 := validClass_pred hv
    simp only [ht0, ite_false]
    rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph ht1 hv]
    have F := mix_lo_data h hc hph (a := t) (by omega) (by omega)
    unfold mixGLo profM profS
    simp only [add_sub_cancel_right]
    split_ifs <;> omega

/-- The first-row class step at the switch `s < w` of the terminal block of a case-(d) composite
is zero (`eq:gluing-caps`, terminal). -/
theorem mix_classBitLo_term_s (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (hs : s < ω.widthZ) :
    classBitLo ω.period (ω.mixLo D) (maxContent D + 1) s = 0 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) s :=
    Or.inr ⟨rfl, hs⟩
  have he := D_end_singleton hD (x := maxContent D) (Or.inr rfl)
  unfold classBitLo
  have hv1 := validClass_pred hv
  simp only [show s ≠ 0 by omega, ite_false]
  rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (by omega) hv]
  have F := mix_lo_data h hc hph (a := s) hs1 hs2
  unfold mixGLo profM profS
  simp only [add_sub_cancel_right]
  split_ifs <;> omega

/-- The southeast word of a case-(d) composite: the class step of the last rows is the bit of `E`,
and `0` at the class boundary (`B_q = 0`), whatever the block. -/
theorem mix_classBitHi (h : ω.IsLegalNonempty) (hc : ω.case = .d) (J a : ℤ) (ha0 : 0 ≤ a)
    (haq : a < ω.period) :
    classBitHi ω.period ω.mixHi J a = if a = 0 then 0 else ω.hi (a - 1) - ω.hi a := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold classBitHi mixHi
  by_cases ha : a = 0
  · subst ha
    have hcp := (d_caps h hc).2
    simp only [dLo, dHi, zero_add] at hcp
    have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
    simp only [ite_true]
    omega
  · simp only [ha, ite_false]
    omega

/-- The bit `B_w = 1` of a case-(d) mark, read on the southeast word of the composite. -/
theorem mix_classBitHi_w (h : ω.IsLegalNonempty) (hc : ω.case = .d) (J : ℤ) :
    classBitHi ω.period ω.mixHi J ω.widthZ = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [mix_classBitHi h hc J ω.widthZ (by omega) hq]
  simp only [show ω.widthZ ≠ 0 by omega, ite_false]
  have hcp := (d_caps h hc).1
  omega

end MarkedInner

end SkewGluing
