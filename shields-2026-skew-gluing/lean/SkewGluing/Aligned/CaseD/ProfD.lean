import SkewGluing.Aligned.CaseD.Prof0

/-!
# Aligned marks, case (d): the heights of `C ∘_μ V` when `μ` has case (d)

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-nested-count`, `eq:gluing-mixed-profile`).

If the lower mark `μ` has case (d), then `eq:gluing-mixed-profile` for `μ` and the outer `C` is the
nested count: `profM (C ∘_μ V) (m + (J a + i)) = Ω_i + CT_{e_i}(J)` on the marked diagonals
`i < b`.

Sorry-free.
-/

namespace SkewGluing

theorem alD_profM_eq_height {D : Diagram} {J : ℤ} (h : minContent D ≤ J ∧ J ≤ maxContent D) :
    profM D J = height D J := by
  unfold profM height
  simp only [h.1, h.2, and_self, ite_true]

section ProfD

variable {V C : Diagram} {a θ : ℤ}

theorem alD_minContent_X (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C) :
    minContent ((alD_lowerMark V a θ).compose C) = minContent V + minContent C * a := by
  have := (alD_lowerMark_isLegal hV hD).minContent_compose hC
  rw [this, alD_lowerMark_period]; rfl

theorem alD_maxContent_X (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C) :
    maxContent ((alD_lowerMark V a θ).compose C) =
      minContent V + maxContent C * a + a + ((span V : ℤ) - a) - 1 := by
  have := (alD_lowerMark_isLegal hV hD).maxContent_compose hC
  rw [this, alD_lowerMark_period]
  have hw := alD_width (cs := alD_case V a θ) hV hD
  have : ((alD_lowerMark V a θ).width : ℤ) = (span V : ℤ) - a := hw
  rw [this]
  change minContent V + maxContent C * a + a + ((span V : ℤ) - a) - 1 = _
  ring

theorem alD_X_class_mem (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    {J i : ℤ} (hi0 : 0 ≤ i) (hi1 : i < a)
    (hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i) :
    minContent ((alD_lowerMark V a θ).compose C) ≤ minContent V + (J * a + i) ∧
      minContent V + (J * a + i) ≤ maxContent ((alD_lowerMark V a θ).compose C) := by
  have h1 := alD_minContent_X hV hD hC
  have h2 := alD_maxContent_X hV hD hC
  have ha := hD.ha
  unfold ValidClass at hv
  rw [h1, h2]
  rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
  · have e1 := mul_le_mul_of_nonneg_right hv1 ha.le
    have e2 := mul_le_mul_of_nonneg_right hv2 ha.le
    have hb := hD.hb
    constructor <;> omega
  · subst hv1
    have hb := hD.hb
    have e : (maxContent C + 1) * a = maxContent C * a + a := by ring
    have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
    have e3 := mul_le_mul_of_nonneg_right hmM ha.le
    constructor <;> omega

theorem alD_NCM_d (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .d) {J i : ℤ} (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ) - a)
    (hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i) :
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      alD_Om V a θ i + alD_CT C (alD_e V a i) J := by
  have hl := alD_hμ hV hD
  have hb := hD.hb
  have hba := hD.hba
  have hw := alD_μ_widthZ hV hD
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hc) hph
  have hv' : ValidClass (minContent C) (maxContent C) (alD_lowerMark V a θ).widthZ J i := by
    rw [hw]; exact hv
  have mp := hl.mixed_profile hC hc hph hlt (J := J) (a := i) hi0
    (by rw [alD_lowerMark_period]; omega) hv'
  rw [alD_lowerMark_period] at mp
  have hmem := alD_X_class_mem hV hD hC hi0 (by omega) hv
  rw [alD_profM_eq_height hmem]
  have hf := MarkedInner.d_E_facts hl hc hph hi0 (by omega : i ≤ (alD_lowerMark V a θ).widthZ - 1)
  have hOm := alD_height_W hV hD hi0 hi1
  have he := alD_e_eq (V := V) (a := a) (θ := θ) i
  unfold alD_CT
  have hHi : height ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      height (alD_lowerMark V a θ).W (minContent V + i) +
        (if i < t then profM C (J - 1) else if i < s then profS C J - 1 else profM C J) := by
    have := MarkedInner.mix_height_marked hl hC hc hph hlt (J := J) (a := i) hi0
      (by rw [hw]; omega) (by unfold ValidClass at hv; omega)
    rw [alD_lowerMark_period] at this
    exact this
  rw [hHi]
  have hdl := (MarkedInner.d_E_facts hl hc hph hi0
    (by omega : i ≤ (alD_lowerMark V a θ).widthZ - 1))
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hdl
  change _ = alD_Om V a θ i + _
  rw [← hOm]
  change height _ (minContent V + i) + _ = height _ (minContent V + i) + _
  congr 1
  by_cases h1 : i < t
  · have := f4 h1
    have : alD_e V a i = -1 := by omega
    simp [h1, this]
  · by_cases h2 : i < s
    · have := f5 (by omega)
      have := f7 h2
      have : alD_e V a i = 0 := by omega
      simp [h1, h2, this]
    · have := f6 (by omega)
      have : alD_e V a i = 1 := by omega
      simp [h1, h2, this]

end ProfD

end SkewGluing
