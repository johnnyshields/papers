/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Asm2.lean`. -/
import GluingCore.Aligned.CaseD.Asm1

/-!
# Aligned marks, case (d): comparing the two sides class by class

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-reassociation`, `eq:gluing-nested-count`).

`alD_NCI V a θ C` is the nested count `eq:gluing-nested-count` in interleaved form: the
interleaved profile `f(2n) = S_n - 1`, `f(2n + 1) = M_n` of `X = C ∘_μ V` at the index
`2 (m + J a + i) + κ` equals that of `V` at `2 (m + i) + κ`, corrected by
`-[δ = 1] + CT_δ(J)` on the marked band (`δ = walkDelta V a k`, `k = 2 (m + i) + κ`) and by
`M^C_J - 1` on the private band.
`alD_class_height_eq` shows, from `alD_NCI`, that the heights of the two sides agree on every class.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

/-- The nested count `eq:gluing-nested-count` for the lower mark `μ` and the outer `C`, in the
interleaved form `profIL`. -/
def alD_NCI (V : Diagram) (a θ : ℤ) (C : Diagram) : Prop :=
  ∀ J i κ : ℤ, 0 ≤ i → i < a → -1 ≤ κ → κ ≤ 1 →
    ((minContent C ≤ J ∧ J ≤ maxContent C) ∨
      (J = maxContent C + 1 ∧ 2 * i + κ ≤ 2 * ((span V : ℤ) - a))) →
    profIL ((alD_lowerMark V a θ).compose C) (2 * (minContent V + (J * a + i)) + κ) =
      if 2 * i + κ ≤ 2 * ((span V : ℤ) - a) then
        profIL V (2 * (minContent V + i) + κ) -
          (if walkDelta V a (2 * (minContent V + i) + κ) = 1 then 1 else 0) +
          alD_CT C (walkDelta V a (2 * (minContent V + i) + κ)) J
      else profIL V (2 * (minContent V + i) + κ) + profM C J - 1

variable {ω η : MarkedInner} {V C : Diagram} {a θ : ℤ}

theorem alD_profM_after_max (_hD : IsConnectedSkew C) (J : ℤ) (h : maxContent C < J) :
    profM C J = 0 := by
  unfold profM
  have : ¬ (minContent C ≤ J ∧ J ≤ maxContent C) := by omega
  simp only [this, ite_false]

theorem alD_class_height_eq (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {θ : ℤ} (hD : alD_Data V a θ) (hC : IsConnectedSkew C) (hNCI : alD_NCI V a θ C)
    {J i α : ℤ} (hi0 : 0 ≤ i) (hi1 : i < a) (hα0 : 0 ≤ α) (hα1 : α < ω.period)
    (hv : ValidClass (minContent C) (maxContent C) η.widthZ J (i * ω.period + α)) :
    height (η.compose C) (minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α)) =
      height (ω.compose ((alD_lowerMark V a θ).compose C))
        (minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α)) := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hwη := eta_width_eq hω hV hη hU ha
  have hwη' : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
    have : η.widthZ = (η.width : ℤ) := rfl
    rw [this, hwη]; rfl
  have hper : η.period = a * ω.period := ha
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hd) hph
  have hph' := hph
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph'
  set X := (alD_lowerMark V a θ).compose C with hXdef
  have hμ := alD_lowerMark_isLegal hV hD
  have hX : IsConnectedSkew X := hμ.isConnectedSkew_compose hC
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hminX : minContent X = minContent V + minContent C * a := alD_minContent_X hV hD hC
  have hmaxX : maxContent X = minContent V + maxContent C * a + a + ((span V : ℤ) - a) - 1 :=
    alD_maxContent_X hV hD hC
  have hspX : (span X : ℤ) = (span C : ℤ) * a + ((span V : ℤ) - a) := by
    have := span_compose hC hμ
    rw [alD_lowerMark_period] at this
    have hw := alD_width (cs := alD_case V a θ) hV hD
    have e : ((alD_lowerMark V a θ).width : ℤ) = (span V : ℤ) - a := hw
    rw [e] at this
    exact this
  have hspC := span_eq_of_isConnectedSkew hC
  -- the position `x` in `η`
  set x := i * ω.period + α with hxdef
  have hx0 : 0 ≤ x := add_nonneg (mul_nonneg hi0 hq0.le) hα0
  have hxq : x < η.period := by rw [hper]; nlinarith
  have hdm := aligned_divmod_eq (j := i) hq0 hα0 hα1
  have ek := class_index_eq hω hV hU ha J i α
  -- validity of the class for `η`
  have hvJ : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ (J = maxContent C + 1 ∧ x < η.widthZ) := by
    unfold ValidClass at hv
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hJmin : minContent C ≤ J := by omega
  -- the index `i'` of the diagonal of `X`
  set i' := (J - minContent C) * a + i with hi'
  have hi'0 : 0 ≤ i' := add_nonneg (mul_nonneg (by omega) hap.le) hi0
  have hxw_i : x < η.widthZ → i ≤ (span V : ℤ) - a := by
    intro h
    by_contra hne
    have : (span V : ℤ) - a + 1 ≤ i := by omega
    have := mul_le_mul_of_nonneg_right this hq0.le
    rw [hwη'] at h
    nlinarith
  have hxw_α : x < η.widthZ → i = (span V : ℤ) - a → α < ω.widthZ := by
    intro h he
    rw [hwη'] at h
    rw [he] at hxdef
    nlinarith
  have hNa : (maxContent C - minContent C) * a = (span C : ℤ) * a - a := by rw [hspC]; ring
  have hi'span : i' ≤ (span X : ℤ) ∧ (i' = (span X : ℤ) → α < ω.widthZ) := by
    rcases hvJ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := mul_le_mul_of_nonneg_right (show J - minContent C ≤ maxContent C - minContent C
        by omega) hap.le
      have : i' < (span X : ℤ) := by rw [hspX]; omega
      exact ⟨this.le, fun h => absurd h this.ne⟩
    · have hi : i ≤ (span V : ℤ) - a := hxw_i h2
      have e : (J - minContent C) * a = (span C : ℤ) * a := by
        rw [h1]; rw [hspC]; ring
      exact ⟨by rw [hspX]; omega, fun h => hxw_α h2 (by rw [hspX] at h; omega)⟩
  -- the right-hand side
  have hHX := HU_interleaved hl hd hX hph hlt (i := i') hi'0 hi'span.1 hα0 hα1 hi'span.2
  have hKR : minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α) =
      alignedC0 ω X + (i' * ω.period + α) := by
    unfold alignedC0
    rw [hminX]
    simp only [hi']
    ring
  have hmi' : minContent X + i' = minContent V + (J * a + i) := by
    rw [hminX]; simp only [hi']; ring
  have hFR : height (ω.compose X)
      (minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α)) =
      constU ω α + profIL X (2 * (minContent V + (J * a + i)) + selK s t α) := by
    rw [hKR]
    have : height (ω.compose X) (alignedC0 ω X + (i' * ω.period + α)) =
        HU ω X (i' * ω.period + α) := rfl
    rw [this, hHX, hmi']
  -- the left-hand side
  have hHV := HU_interleaved hl hd hV hph hlt (i := i) (α := α) hi0 (by omega) hα0 hα1
    (by intro h; omega)
  have hbκ := selK_bounds s t α
  set κ := selK s t α with hκ
  have hdl : x < η.widthZ → η.dLo x = walkDelta V a (2 * (minContent V + i) + κ) := by
    intro h
    have := eta_dLo_walk hω hd hV hη hU ha hph hlt hx0 (by omega)
    rw [this]
    unfold sampleIdx
    rw [hdm.1, hdm.2]
  have hwk := walk_signs hω hd hV hη hU ha
  rw [hFR, ← ek]
  have hMb : profIL V (2 * (minContent V + ((span V : ℤ) - a)) + 1) = 1 := by
    rw [profIL_odd, aligned_profM_eq (by omega)]
    have := hD.singleton_b
    unfold alD_L alD_H at this
    omega
  by_cases hxw : x < η.widthZ
  · rw [alD_FL_height_marked hω hd hV hη hU ha hC hx0 hxw hv, hdl hxw, hHV]
    have hib := hxw_i hxw
    by_cases h1a : 2 * i + κ ≤ 2 * ((span V : ℤ) - a)
    · have hN := hNCI J i κ hi0 hi1 hbκ.1 hbκ.2 (by
        rcases hvJ with h | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, h1a⟩)
      simp only [h1a, ite_true] at hN
      rw [hN]; ring
    · have hib' : i = (span V : ℤ) - a := by omega
      have hκ1 : κ = 1 := by omega
      have hk : 2 * (minContent V + i) + κ = 2 * minContent V + 2 * ((span V : ℤ) - a) + 1 := by
        rw [hib', hκ1]; ring
      have hδ : walkDelta V a (2 * (minContent V + i) + κ) = 1 := by rw [hk]; exact hwk.2.2.2
      have hfV : profIL V (2 * (minContent V + i) + κ) = 1 := by
        rw [hib', hκ1]; exact hMb
      rw [hδ, hfV]
      have hCT : alD_CT C 1 J = profM C J := by unfold alD_CT; simp
      have e1 : (if (1 : ℤ) = 1 then (1 : ℤ) else 0) = 1 := by simp
      rw [hCT, e1]
      rcases hvJ with ⟨h2, h3⟩ | ⟨h2, -⟩
      · have hN := hNCI J i κ hi0 hi1 hbκ.1 hbκ.2 (Or.inl ⟨h2, h3⟩)
        simp only [h1a, ite_false] at hN
        rw [hN, hfV]; ring
      · have hP : profIL ((alD_lowerMark V a θ).compose C)
            (2 * (minContent V + (J * a + i)) + κ) = 0 := by
          rw [hκ1, show 2 * (minContent V + (J * a + i)) + 1 =
            2 * (minContent V + (J * a + i)) + 1 from rfl, profIL_odd]
          apply alD_profM_after_max hX
          rw [hmaxX]
          have e : (maxContent C + 1) * a = maxContent C * a + a := by ring
          rw [h2, hib', e]
          omega
        rw [hP, h2]
        have : profM C (maxContent C + 1) = 0 := alD_profM_after_max hC _ (by omega)
        rw [this]; ring
  · have hJ : minContent C ≤ J ∧ J ≤ maxContent C := by
      rcases hvJ with h | h
      · exact h
      · exact absurd h.2 hxw
    rw [alD_FL_height_private hω hd hV hη hU ha hC (by omega) hxq hJ, hHV]
    have hge : ¬ 2 * i + κ ≤ 2 * ((span V : ℤ) - a) := by
      intro h
      have hxge : η.widthZ ≤ x := by omega
      rw [hwη'] at hxge
      by_cases hi2 : i < (span V : ℤ) - a
      · have h5 : (i + 1) * ω.period ≤ ((span V : ℤ) - a) * ω.period :=
          mul_le_mul_of_nonneg_right (by omega) hq0.le
        have h6 : (i + 1) * ω.period = i * ω.period + ω.period := by ring
        have h7 : x = i * ω.period + α := hxdef
        omega
      · have hib : i = (span V : ℤ) - a := by
          by_contra hne
          have : (span V : ℤ) - a < i := by omega
          have : 2 * i + κ ≥ 2 * ((span V : ℤ) - a) + 2 - 1 := by omega
          omega
        have hαw : ω.widthZ ≤ α := by
          have h7 : x = i * ω.period + α := hxdef
          rw [hib] at h7
          omega
        have : κ = 1 := selK_ge hlt (by omega)
        omega
    have hN := hNCI J i κ hi0 hi1 hbκ.1 hbκ.2 (Or.inl hJ)
    simp only [hge, ite_false] at hN
    rw [hN]; ring

end MarkedInner

end GluingCore
