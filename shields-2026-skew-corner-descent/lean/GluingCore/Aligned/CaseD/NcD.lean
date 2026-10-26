/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/NcD.lean`. -/
import GluingCore.Aligned.CaseD.NcOrd

/-!
# Aligned marks, case (d): the nested count for a lower mark of case (d)

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-nested-count`, `eq:gluing-mixed-profile`).

For a lower mark `μ` of case (d) the southeast rows of `C ∘_μ V` are `H_i + J θ`
(`eq:gluing-mixed-profile`, southeast endpoint), so the consecutive span of `X = C ∘_μ V` is
`S^X_u = M^X_u + (h^X_{u-1} - h^X_u)`, and the nested count follows from the heights.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {V C : Diagram} {a θ : ℤ}

theorem alD_S_of_M {X : Diagram} (hX : IsConnectedSkew X) {u : ℤ}
    (h : minContent X + 1 ≤ u ∧ u ≤ maxContent X) :
    profS X u = diagHi X (u - 1) - diagHi X u + profM X u := by
  have hs := isConnectedSkew_iff_diagonal.mp hX
  have h1 : minContent X ≤ u ∧ u ≤ maxContent X := ⟨by omega, h.2⟩
  rw [aligned_profS_eq h, aligned_profM_eq h1]
  ring

theorem alD_hiX_d (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J i : ℤ} (h0 : 0 ≤ i) (h1 : i < a)
    (hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i) :
    diagHi ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      alD_H V i + J * θ := by
  have hl := alD_hμ hV hD
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hc) hph
  have hw := alD_μ_widthZ hV hD
  have hv' : ValidClass (minContent C) (maxContent C) (alD_lowerMark V a θ).widthZ J i := by
    rw [hw]; exact hv
  have := (hl.mixed_profile hC hc hph hlt (J := J) (a := i) h0
    (by rw [alD_lowerMark_period]; exact h1) hv').1
  rw [alD_lowerMark_period] at this
  exact this

theorem alD_NCM_d' (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J i : ℤ} (h0 : 0 ≤ i) (h1 : i < (span V : ℤ) - a)
    (hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i) :
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      alD_Om V a θ i + alD_CT C (walkDelta V a (2 * (minContent V + i) + 1)) J := by
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  rw [alD_walk_odd_eq hV h0 hap.le (by omega)]
  exact alD_NCM_d hV hD hC hc h0 h1 hv

theorem alD_NCP_d (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J i : ℤ} (h0 : (span V : ℤ) - a ≤ i) (h1 : i < a)
    (hJ1 : minContent C ≤ J) (hJ2 : J ≤ maxContent C) :
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profM V (minContent V + i) + profM C J - 1 := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hw := alD_μ_widthZ hV hD
  have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i := by
    unfold ValidClass; exact Or.inl ⟨hJ1, hJ2⟩
  have hmem := alD_X_class_mem hV hD hC (by omega) h1 hvc
  rw [alD_profM_eq_height hmem]
  have := alD_mixed_private hl hC hc (J := J) (i := i) (by omega)
    (by rw [alD_lowerMark_period]; exact h1) ⟨hJ1, hJ2⟩
  rw [alD_lowerMark_period] at this
  have e : height (alD_lowerMark V a θ).E (minContent (alD_lowerMark V a θ).E + i) =
      alD_H V i - alD_L V i + 1 := rfl
  rw [e] at this
  change height ((alD_lowerMark V a θ).compose C)
    (minContent (alD_lowerMark V a θ).E + (J * a + i)) = _
  rw [this, alD_profM_V hV (by omega) (by omega)]

theorem alD_NCS_d_mid (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J i : ℤ} (h0 : 1 ≤ i)
    (h1 : i < (span V : ℤ) - a)
    (hv : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) -
        (if walkDelta V a (2 * (minContent V + i)) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + i))) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hX := (alD_lowerMark_isLegal hV hD).isConnectedSkew_compose hC
  have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i := by
    unfold ValidClass
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h1⟩
  have hvp : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J (i - 1) := by
    unfold ValidClass
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega⟩
  have hmem := alD_X_class_mem hV hD hC (by omega) (by omega) hvc
  have hminX := alD_minContent_X hV hD hC
  have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤ minContent V + (J * a + i) ∧
      minContent V + (J * a + i) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
    refine ⟨?_, hmem.2⟩
    have hJ : minContent C ≤ J := by rcases hv with h | h <;> omega
    have := mul_le_mul_of_nonneg_right hJ hap.le
    omega
  rw [alD_S_of_M hX hrange]
  have e1 : minContent V + (J * a + i) - 1 = minContent V + (J * a + (i - 1)) := by ring
  rw [e1, alD_hiX_d hV hD hC hc (by omega) (by omega) hvp, alD_hiX_d hV hD hC hc (by omega)
    (by omega) hvc, alD_NCM_d' hV hD hC hc (by omega) h1 hvc, alD_Om_eq hV hD (by omega) h1,
    alD_walk_odd_eq hV (by omega) hap.le (by omega), alD_walk_even_eq]
  have e2 : minContent V + i + a = minContent V + (i + a) := by ring
  rw [e2, alD_profS_V_eq hV h0 (by omega), alD_profS_V_eq hV (j := i + a) (by omega) (by omega)]
  have hw := alD_μ_widthZ hV hD
  have hs0 := hl.sides_d hc (a := i - 1) (by omega) (by omega)
  have hs1 := hl.sides_d hc (a := i) (by omega) (by omega)
  rw [alD_μ_dHi] at hs0 hs1
  have e3 : i + a - 1 = i - 1 + a := by ring
  have hde : alD_H V (i - 1) - alD_L V i + 1 - (alD_H V (i + a - 1) - alD_L V (i + a) + 1) =
      alD_e V a i := by
    unfold alD_e
    rw [e3]
    omega
  rw [hde]
  omega

theorem alD_NCS_d_zero (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J : ℤ}
    (hv : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + 0)) =
      profS V (minContent V + 0) -
        (if walkDelta V a (2 * (minContent V + 0)) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + 0))) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hX := (alD_lowerMark_isLegal hV hD).isConnectedSkew_compose hC
  have hSa : profS V (minContent V + a) = alD_H V (a - 1) - alD_L V a + 1 :=
    alD_profS_V_eq hV (by omega) (by omega)
  have hS0 : profS V (minContent V + 0) = 1 := by
    apply aligned_profS_eq_one
    omega
  have e0 : minContent V + 0 + a = minContent V + a := by ring
  have hd0 : walkDelta V a (2 * (minContent V + 0)) = 1 - (alD_H V (a - 1) - alD_L V a + 1) := by
    rw [alD_walk_even_eq, e0, hSa, hS0]
  have hsa := hD.singleton_a
  have st := alD_step hV (j := a) (by omega) (by omega)
  have l0 := alD_L_le_H hV (j := a - 1) (by omega) (by omega)
  have l1 := alD_L_le_H hV (j := a) (by omega) (by omega)
  by_cases hJm : J = minContent C
  · have hX1 : profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + 0)) = 1 := by
      apply aligned_profS_eq_one
      rw [alD_minContent_X hV hD hC, hJm]
      omega
    rw [hX1, hS0, hd0]
    have hCm : profM C (J - 1) = 0 := alD_profM_before_min C _ (by omega)
    have hCs : profS C J = 1 := aligned_profS_eq_one (by omega)
    have hCj : profM C J = 1 := by
      rw [aligned_profM_eq ⟨by omega, by omega⟩]
      have := (D_ends hC).1
      rw [hJm]; omega
    unfold alD_CT
    rw [hCm, hCs, hCj]
    split_ifs <;> omega
  · have hJ1 : minContent C + 1 ≤ J := by rcases hv with h | h <;> omega
    have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J 0 := by
      unfold ValidClass
      rcases hv with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hb⟩
    have hvp : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) (J - 1) (a - 1) := by
      unfold ValidClass
      rcases hv with h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
    have hmem := alD_X_class_mem hV hD hC le_rfl hap hvc
    have hminX := alD_minContent_X hV hD hC
    have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤
        minContent V + (J * a + 0) ∧
        minContent V + (J * a + 0) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
      refine ⟨?_, hmem.2⟩
      have := mul_le_mul_of_nonneg_right hJ1 hap.le
      have e : (minContent C + 1) * a = minContent C * a + a := by ring
      omega
    rw [alD_S_of_M hX hrange]
    have e1 : minContent V + (J * a + 0) - 1 = minContent V + ((J - 1) * a + (a - 1)) := by ring
    rw [e1, alD_hiX_d hV hD hC hc (by omega) (by omega) hvp,
      alD_hiX_d hV hD hC hc le_rfl hap hvc, alD_NCM_d' hV hD hC hc le_rfl hb hvc,
      alD_Om_eq hV hD le_rfl hb, alD_walk_odd_eq hV le_rfl hap.le (by omega), hS0, hd0]
    have hcaps := (d_caps hl hc).2
    have hw := alD_μ_widthZ hV hD
    simp only [alD_μ_hi, alD_μ_lo, alD_μ_dHi, alD_μ_dLo, alD_lowerMark_period, zero_add] at hcaps
    have h00 := alD_end0 hV
    have hp : (J - 1) * θ = J * θ - θ := by ring
    have hee : alD_e V a 0 = 1 - (alD_H V (a - 1) - alD_L V a + 1) := by
      unfold alD_e
      simp only [zero_add]
      omega
    rw [hee]
    unfold alD_L alD_H at *
    omega

theorem alD_NCS_d_b (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J : ℤ} (hv : minContent C ≤ J ∧ J ≤ maxContent C) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + ((span V : ℤ) - a))) =
      profS V (minContent V + ((span V : ℤ) - a)) -
        (if walkDelta V a (2 * (minContent V + ((span V : ℤ) - a))) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + ((span V : ℤ) - a)))) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hX := (alD_lowerMark_isLegal hV hD).isConnectedSkew_compose hC
  have hw := alD_μ_widthZ hV hD
  have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J ((span V : ℤ) - a) := by
    unfold ValidClass; exact Or.inl hv
  have hvp : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J
      (((span V : ℤ) - a) - 1) := by
    unfold ValidClass; exact Or.inl hv
  have hmem := alD_X_class_mem hV hD hC (by omega) (by omega) hvc
  have hminX := alD_minContent_X hV hD hC
  have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤
      minContent V + (J * a + ((span V : ℤ) - a)) ∧
      minContent V + (J * a + ((span V : ℤ) - a)) ≤
        maxContent ((alD_lowerMark V a θ).compose C) := by
    refine ⟨?_, hmem.2⟩
    have := mul_le_mul_of_nonneg_right hv.1 hap.le
    omega
  rw [alD_S_of_M hX hrange]
  have e1 : minContent V + (J * a + ((span V : ℤ) - a)) - 1 =
      minContent V + (J * a + (((span V : ℤ) - a) - 1)) := by ring
  have e2 : minContent V + ((span V : ℤ) - a) + a =
      minContent V + (((span V : ℤ) - a) + a) := by ring
  have hbaN : ((span V : ℤ) - a) + a = (span V : ℤ) := by omega
  rw [e1, alD_hiX_d hV hD hC hc (by omega) (by omega) hvp,
    alD_hiX_d hV hD hC hc (by omega) (by omega) hvc,
    alD_NCP_d hV hD hC hc le_rfl (by omega) hv.1 hv.2, alD_walk_even_eq, e2, hbaN,
    alD_profS_V_eq hV (by omega) (by omega), alD_profM_V hV (by omega) (by omega)]
  have hSout : profS V (minContent V + (span V : ℤ)) = 1 := by
    apply aligned_profS_eq_one
    omega
  rw [hSout]
  have hcaps := (d_caps hl hc).1
  simp only [alD_μ_hi, alD_μ_lo, alD_μ_dHi, alD_μ_dLo, hw] at hcaps
  have hsb := hD.singleton_b
  have hCm := aligned_profM_eq hv
  unfold alD_CT
  have hCm' : profM C J = diagHi C J - diagLo C J + 1 := hCm
  unfold alD_L alD_H at *
  split_ifs <;> omega

theorem alD_NCS_d_priv (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J i : ℤ} (h0 : (span V : ℤ) - a < i)
    (h1 : i < a) (hJ1 : minContent C ≤ J) (hJ2 : J ≤ maxContent C) :
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) + profM C J - 1 := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hX := (alD_lowerMark_isLegal hV hD).isConnectedSkew_compose hC
  have hvc : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i := by
    unfold ValidClass; exact Or.inl ⟨hJ1, hJ2⟩
  have hvp : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J (i - 1) := by
    unfold ValidClass; exact Or.inl ⟨hJ1, hJ2⟩
  have hmem := alD_X_class_mem hV hD hC (by omega) h1 hvc
  have hminX := alD_minContent_X hV hD hC
  have hrange : minContent ((alD_lowerMark V a θ).compose C) + 1 ≤ minContent V + (J * a + i) ∧
      minContent V + (J * a + i) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
    refine ⟨?_, hmem.2⟩
    have := mul_le_mul_of_nonneg_right hJ1 hap.le
    omega
  rw [alD_S_of_M hX hrange]
  have e1 : minContent V + (J * a + i) - 1 = minContent V + (J * a + (i - 1)) := by ring
  rw [e1, alD_hiX_d hV hD hC hc (by omega) (by omega) hvp,
    alD_hiX_d hV hD hC hc (by omega) h1 hvc, alD_NCP_d hV hD hC hc (by omega) h1 hJ1 hJ2,
    alD_profS_V_eq hV (by omega) (by omega), alD_profM_V hV (by omega) (by omega)]
  unfold alD_L alD_H
  omega

/-- **`eq:gluing-nested-count`** for a lower mark of case (d). -/
theorem alD_NC_d (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) : alD_NC V a θ C := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  refine ⟨fun J i h0 h1 hv => alD_NCM_d' hV hD hC hc h0 h1 hv,
    fun J i h0 h1 hJ1 hJ2 => alD_NCP_d hV hD hC hc h0 h1 hJ1 hJ2, ?_,
    fun J i h0 h1 hJ1 hJ2 => alD_NCS_d_priv hV hD hC hc h0 h1 hJ1 hJ2⟩
  intro J i h0 h1 hv
  by_cases hi0 : i = 0
  · subst hi0
    exact alD_NCS_d_zero hV hD hC hc hv
  by_cases hib : i = (span V : ℤ) - a
  · subst hib
    rcases hv with hv | hv
    · exact alD_NCS_d_b hV hD hC hc hv
    · have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
      have hX : profS ((alD_lowerMark V a θ).compose C)
          (minContent V + (J * a + ((span V : ℤ) - a))) = 1 := by
        apply aligned_profS_eq_one
        rw [alD_maxContent_X hV hD hC, hv]
        have e : (maxContent C + 1) * a = maxContent C * a + a := by ring
        omega
      have hSb : profS V (minContent V + ((span V : ℤ) - a)) =
          alD_H V ((span V : ℤ) - a - 1) - alD_L V ((span V : ℤ) - a) + 1 :=
        alD_profS_V_eq hV (by omega) (by omega)
      have hSout : profS V (minContent V + ((span V : ℤ) - a) + a) = 1 := by
        apply aligned_profS_eq_one
        omega
      have hlast := hD.d_last
      have hel := alD_e_last hV hD
      unfold alD_e at hlast hel
      have hCm : profM C J = 0 := alD_profM_after_max hC J (by omega)
      have hCs : profS C J = 1 := aligned_profS_eq_one (by omega)
      rw [hX, alD_walk_even_eq, hSout, hSb]
      unfold alD_CT
      rw [hCm, hCs]
      split_ifs <;> omega
  · have hib' : i < (span V : ℤ) - a := by omega
    exact alD_NCS_d_mid hV hD hC hc (by omega) hib' hv

end MarkedInner

end GluingCore
