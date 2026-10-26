import SkewGluing.Aligned.CaseD.Eta

/-!
# Aligned marks, case (d): the case `b = 0`

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-mixed-profile`).

For `a = N_V` the lower mark is the horizontal empty mark of `V` and `γ = id`:
`reassoc_empty` proves `C ∘_η U = (C ∘_∅ V) ∘_ω E`.  The identity is obtained by comparing, on
every diagonal class, the southeast row and the height of both sides (`FL_diagHi`, `FL_height`,
`FR_diagHi`, `FR_height`); the profile of the composite of the empty mark is computed in
`emptyH_profM`, `emptyH_profS_pos`, `emptyH_profS_zero`.

Sorry-free.
-/

namespace SkewGluing
namespace MarkedInner

variable {V C : Diagram}

theorem emptyH_legalEmpty (hV : IsConnectedSkew V) : (emptyMarkH V).IsLegalEmpty :=
  ⟨emptyMarkH_isLegal hV, rfl⟩

theorem emptyH_period (hV : IsConnectedSkew V) : (emptyMarkH V).period = (span V : ℤ) := by
  have := (emptyH_legalEmpty hV).span_eq
  exact this.symm

theorem emptyH_rowShift (hV : IsConnectedSkew V) :
    (emptyMarkH V).rowShift = diagLo V (maxContent V) - diagLo V (minContent V) := by
  have := (emptyH_legalEmpty hV).rowShift_eq
  rw [this]
  have h := (emptyH_legalEmpty hV).span_eq
  have hsp := span_eq_of_isConnectedSkew hV
  have e : minContent V + ((emptyMarkH V).period - 1) = maxContent V := by
    have : (emptyMarkH V).period = (span V : ℤ) := h.symm
    omega
  unfold lo
  change diagLo V (minContent V + ((emptyMarkH V).period - 1)) - diagLo V (minContent V + 0) = _
  rw [e]; simp

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {V C : Diagram}

theorem emptyH_oRowLo (J : ℤ) : (emptyMarkH V).oRowLo C J =
    J * (emptyMarkH V).rowShift + diagLo C J := by
  simp [oRowLo, emptyMarkH]

theorem emptyH_oRowHi (J : ℤ) : (emptyMarkH V).oRowHi C J =
    J * (emptyMarkH V).rowShift + diagHi C J := by
  simp [oRowHi, emptyMarkH]

/-- The diagonal rows of `X = V ∘_{∅} C` on the class `(J, i)`: the first rows of `C` and `V`
add (the empty mark chains the copies of `V` along the diagonals of `C`). -/
theorem emptyH_diagLo (hV : IsConnectedSkew V) (hC : IsConnectedSkew C) {J i : ℤ}
    (hJ : minContent C ≤ J ∧ J ≤ maxContent C) (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ)) :
    diagLo ((emptyMarkH V).compose C) (minContent V + (J * (span V : ℤ) + i)) =
      J * (emptyMarkH V).rowShift + diagLo C J + diagLo V (minContent V + i) := by
  have h := emptyH_legalEmpty hV
  have hc := h.classRows hC
  have hper := emptyH_period hV
  have hv : ValidClass (minContent C) (maxContent C) (emptyMarkH V).widthZ J i :=
    Or.inl hJ
  have := hc.diagLo_eq (j := J) (a := i) hi0 (by rw [hper]; exact hi1) hv
  rw [hper] at this
  change diagLo ((emptyMarkH V).compose C) (minContent V + (J * (span V : ℤ) + i)) = _ at this
  rw [this, emptyH_oRowLo]
  rfl

theorem emptyH_diagHi (hV : IsConnectedSkew V) (hC : IsConnectedSkew C) {J i : ℤ}
    (hJ : minContent C ≤ J ∧ J ≤ maxContent C) (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ)) :
    diagHi ((emptyMarkH V).compose C) (minContent V + (J * (span V : ℤ) + i)) =
      J * (emptyMarkH V).rowShift + diagHi C J + diagHi V (minContent V + i) := by
  have h := emptyH_legalEmpty hV
  have hc := h.classRows hC
  have hper := emptyH_period hV
  have hv : ValidClass (minContent C) (maxContent C) (emptyMarkH V).widthZ J i :=
    Or.inl hJ
  have := hc.diagHi_eq (j := J) (a := i) hi0 (by rw [hper]; exact hi1) hv
  rw [hper] at this
  change diagHi ((emptyMarkH V).compose C) (minContent V + (J * (span V : ℤ) + i)) = _ at this
  rw [this, emptyH_oRowHi]
  rfl

theorem emptyH_minContent (hV : IsConnectedSkew V) (hC : IsConnectedSkew C) :
    minContent ((emptyMarkH V).compose C) = minContent V + minContent C * (span V : ℤ) := by
  have h := (emptyMarkH_isLegal hV).minContent_compose hC
  rw [h, emptyH_period hV]; rfl

theorem emptyH_maxContent (hV : IsConnectedSkew V) (hC : IsConnectedSkew C) :
    maxContent ((emptyMarkH V).compose C) =
      minContent V + maxContent C * (span V : ℤ) + (span V : ℤ) - 1 := by
  have h := (emptyMarkH_isLegal hV).maxContent_compose hC
  rw [h, emptyH_period hV]
  have : ((emptyMarkH V).width : ℤ) = 0 := (emptyH_legalEmpty hV).width_zero
  have e : minContent (emptyMarkH V).E = minContent V := rfl
  rw [e]
  omega

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {V C : Diagram}

theorem emptyH_profM (hV : IsConnectedSkew V) (hC : IsConnectedSkew C) {J i : ℤ}
    (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ)) :
    profM ((emptyMarkH V).compose C) (minContent V + (J * (span V : ℤ) + i)) =
      if minContent C ≤ J ∧ J ≤ maxContent C then
        profM V (minContent V + i) + profM C J - 1 else 0 := by
  have hsp := aligned_span_eq hV
  have hminX := emptyH_minContent hV hC
  have hmaxX := emptyH_maxContent hV hC
  have hN : 1 ≤ (span V : ℤ) := by omega
  by_cases hJ : minContent C ≤ J ∧ J ≤ maxContent C
  · simp only [hJ.1, hJ.2, and_self, ite_true]
    have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
    have hX : minContent ((emptyMarkH V).compose C) ≤ minContent V + (J * (span V : ℤ) + i) ∧
        minContent V + (J * (span V : ℤ) + i) ≤ maxContent ((emptyMarkH V).compose C) := by
      rw [hminX, hmaxX]
      constructor <;> nlinarith [hJ.1, hJ.2]
    rw [aligned_profM_eq hX, emptyH_diagLo hV hC hJ hi0 hi1, emptyH_diagHi hV hC hJ hi0 hi1,
      aligned_profM_eq (D := V) (J := minContent V + i) (by
        omega),
      aligned_profM_eq hJ]
    ring
  · simp only [hJ, ite_false]
    apply aligned_profM_eq_zero
    rw [hminX, hmaxX]
    intro hh
    apply hJ
    constructor
    · by_contra hc
      have : J + 1 ≤ minContent C := by omega
      nlinarith [hh.1]
    · by_contra hc
      have : maxContent C + 1 ≤ J := by omega
      nlinarith [hh.2]

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {V C : Diagram}

theorem emptyH_profS_pos (hV : IsConnectedSkew V) (hC : IsConnectedSkew C) {J i : ℤ}
    (hi0 : 1 ≤ i) (hi1 : i < (span V : ℤ)) :
    profS ((emptyMarkH V).compose C) (minContent V + (J * (span V : ℤ) + i)) =
      if minContent C ≤ J ∧ J ≤ maxContent C then
        profS V (minContent V + i) + profM C J - 1 else 1 := by
  have hsp := aligned_span_eq hV
  have hminX := emptyH_minContent hV hC
  have hmaxX := emptyH_maxContent hV hC
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  by_cases hJ : minContent C ≤ J ∧ J ≤ maxContent C
  · simp only [hJ.1, hJ.2, and_self, ite_true]
    have hX : minContent ((emptyMarkH V).compose C) + 1 ≤
        minContent V + (J * (span V : ℤ) + i) ∧
        minContent V + (J * (span V : ℤ) + i) ≤ maxContent ((emptyMarkH V).compose C) := by
      rw [hminX, hmaxX]
      constructor <;> nlinarith [hJ.1, hJ.2]
    rw [aligned_profS_eq hX]
    have e : minContent V + (J * (span V : ℤ) + i) - 1 =
        minContent V + (J * (span V : ℤ) + (i - 1)) := by ring
    rw [e, emptyH_diagHi hV hC hJ (by omega) (by omega),
      emptyH_diagLo hV hC hJ (by omega) hi1,
      aligned_profS_eq (D := V) (J := minContent V + i) (by omega),
      aligned_profM_eq hJ]
    have e2 : minContent V + i - 1 = minContent V + (i - 1) := by ring
    rw [e2]
    ring
  · simp only [hJ, ite_false]
    apply aligned_profS_eq_one
    rw [hminX, hmaxX]
    intro hh
    apply hJ
    constructor
    · by_contra hc
      have : J + 1 ≤ minContent C := by omega
      nlinarith [hh.1]
    · by_contra hc
      have : maxContent C + 1 ≤ J := by omega
      nlinarith [hh.2]

theorem emptyH_profS_zero (hV : IsConnectedSkew V) (hC : IsConnectedSkew C) (J : ℤ) :
    profS ((emptyMarkH V).compose C) (minContent V + (J * (span V : ℤ) + 0)) = profS C J := by
  have hsp := aligned_span_eq hV
  have hminX := emptyH_minContent hV hC
  have hmaxX := emptyH_maxContent hV hC
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hends := D_ends hV
  by_cases hJ : minContent C + 1 ≤ J ∧ J ≤ maxContent C
  · have hX : minContent ((emptyMarkH V).compose C) + 1 ≤
        minContent V + (J * (span V : ℤ) + 0) ∧
        minContent V + (J * (span V : ℤ) + 0) ≤ maxContent ((emptyMarkH V).compose C) := by
      rw [hminX, hmaxX]
      constructor <;> nlinarith [hJ.1, hJ.2]
    rw [aligned_profS_eq hX, aligned_profS_eq hJ]
    have e : minContent V + (J * (span V : ℤ) + 0) - 1 =
        minContent V + ((J - 1) * (span V : ℤ) + ((span V : ℤ) - 1)) := by ring
    rw [e, emptyH_diagHi hV hC (J := J - 1) (i := (span V : ℤ) - 1) (by omega) (by omega)
      (by omega)]
    have h0 := emptyH_diagLo hV hC (J := J) (i := 0) (by omega) (le_refl _) (by omega)
    simp only [add_zero] at h0 ⊢
    rw [h0, emptyH_rowShift hV]
    have e3 : minContent V + ((span V : ℤ) - 1) = maxContent V := by omega
    rw [e3]
    have : (J - 1) * (diagLo V (maxContent V) - diagLo V (minContent V)) =
        J * (diagLo V (maxContent V) - diagLo V (minContent V)) -
          (diagLo V (maxContent V) - diagLo V (minContent V)) := by ring
    rw [this]
    omega
  · have hX : ¬ (minContent ((emptyMarkH V).compose C) + 1 ≤
        minContent V + (J * (span V : ℤ) + 0) ∧
        minContent V + (J * (span V : ℤ) + 0) ≤ maxContent ((emptyMarkH V).compose C)) := by
      rw [hminX, hmaxX]
      intro hh
      apply hJ
      constructor
      · by_contra hc
        have : J ≤ minContent C := by omega
        nlinarith [hh.1]
      · by_contra hc
        have : maxContent C + 1 ≤ J := by omega
        nlinarith [hh.2]
    rw [aligned_profS_eq_one hX, aligned_profS_eq_one hJ]

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- The height `Ω_α` of the lower copy on the relative content `α`. -/
def Om (ω : MarkedInner) (α : ℤ) : ℤ := height ω.W (minContent ω.E + α)

theorem aligned_profM_first (hV : IsConnectedSkew V) : profM V (minContent V) = 1 := by
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  rw [aligned_profM_eq ⟨le_refl _, hmM⟩, (D_ends hV).1]; ring

theorem aligned_profM_last (hV : IsConnectedSkew V) : profM V (maxContent V) = 1 := by
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  rw [aligned_profM_eq ⟨hmM, le_refl _⟩, (D_ends hV).2]; ring

theorem HU_first (h : ω.IsLegalNonempty) (hd : ω.case = .d) (hV : IsConnectedSkew V) {s t : ℤ}
    (hph : ω.IsPhases s t) (hlt : t < s) {α : ℤ} (h0 : 0 ≤ α) (h1 : α < ω.widthZ) :
    HU ω V α = Om ω α + (if α < t then 0 else if α < s then 0 else 1) := by
  have hq := h.width_lt_period
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hv : ValidClass (minContent V) (maxContent V) ω.widthZ (minContent V) α :=
    Or.inl ⟨le_refl _, hmM⟩
  have hmp := h.mixed_profile hV hd hph hlt (J := minContent V) (a := α) h0 (by omega) hv
  have e : alignedC0 ω V + α = minContent ω.E + (minContent V * ω.period + α) := by
    unfold alignedC0; ring
  unfold HU Om
  rw [e]
  have p1 := aligned_profM_first hV
  have p2 : profS V (minContent V) = 1 := aligned_profS_eq_one (by omega)
  have p3 : profM V (minContent V - 1) = 0 := aligned_profM_eq_zero (by omega)
  by_cases h2 : α < t
  · rw [hmp.2.2.1 h2, p3]; simp [h2]
  · by_cases h3 : α < s
    · rw [hmp.2.2.2.1 (by omega) h3, p2]; simp [h2, h3]
    · rw [hmp.2.2.2.2 (by omega) h1, p1]; simp [h2, h3]

theorem HU_last (h : ω.IsLegalNonempty) (hd : ω.case = .d) (hV : IsConnectedSkew V) {s t : ℤ}
    (hph : ω.IsPhases s t) (hlt : t < s) {α : ℤ} (h0 : 0 ≤ α) (h1 : α < ω.widthZ) :
    HU ω V (α + (span V : ℤ) * ω.period) = Om ω α + (if α < t then 1 else 0) := by
  have hq := h.width_lt_period
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hsp := aligned_span_eq hV
  have hv : ValidClass (minContent V) (maxContent V) ω.widthZ (maxContent V + 1) α :=
    Or.inr ⟨rfl, h1⟩
  have hmp := h.mixed_profile hV hd hph hlt (J := maxContent V + 1) (a := α) h0 (by omega) hv
  have e : alignedC0 ω V + (α + (span V : ℤ) * ω.period) =
      minContent ω.E + ((maxContent V + 1) * ω.period + α) := by
    unfold alignedC0; rw [hsp]; ring
  unfold HU Om
  rw [e]
  have p1 := aligned_profM_last hV
  have p2 : profS V (maxContent V + 1) = 1 := aligned_profS_eq_one (by omega)
  have p3 : profM V (maxContent V + 1) = 0 := aligned_profM_eq_zero (by omega)
  have p4 : maxContent V + 1 - 1 = maxContent V := by ring
  by_cases h2 : α < t
  · rw [hmp.2.2.1 h2, p4, p1]; simp [h2]
  · by_cases h3 : α < s
    · rw [hmp.2.2.2.1 (by omega) h3, p2]; simp [h2]
    · rw [hmp.2.2.2.2 (by omega) h1, p3]; simp [h2]

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

theorem eta_widthZ_empty (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hη : η.IsLegal)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) : η.widthZ = ω.widthZ := by
  have := eta_width_eq hω hV hη hU ha
  have h2 : η.widthZ = (η.width : ℤ) := rfl
  have h3 : ω.widthZ = (ω.width : ℤ) := rfl
  rw [h2, this, h3, hb]; ring

theorem eta_dLo_empty (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {x : ℤ}
    (h0 : 0 ≤ x) (h1 : x < ω.widthZ) :
    η.dLo x = if x < t then -1 else if x < s then 0 else 1 := by
  have hl := aligned_legalNonempty hω hd
  have hw := eta_widthZ_empty hω hV hη hU ha hb
  rw [eta_dLo hω hd hV hη hU ha h0 (by omega), hb, HU_first hl hd hV hph hlt h0 h1,
    HU_last hl hd hV hph hlt h0 h1]
  by_cases h2 : x < t
  · simp [h2]
  · by_cases h3 : x < s
    · simp [h2, h3]
    · simp [h2, h3]

theorem eta_isPhases_empty (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) :
    η.IsPhases s t := by
  have hw := eta_widthZ_empty hω hV hη hU ha hb
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  refine ⟨hs1, by omega, ht1, by omega, ?_, ?_⟩
  · intro x h0 h1
    have h1' : x < ω.widthZ := by omega
    have := eta_dLo_empty hω hd hV hη hU ha hb ⟨hs1, hs2, ht1, ht2, hS, hT⟩ hlt h0 h1'
    have h2 := eta_dHi_zero hω hd hV hη hU ha h0 h1
    unfold TailLower
    rw [this, h2]
    by_cases h3 : x < t
    · simp [h3]; omega
    · by_cases h4 : x < s
      · simp [h3, h4]
      · simp [h3, h4]; omega
  · intro x h0 h1
    have h1' : x < ω.widthZ := by omega
    have := eta_dLo_empty hω hd hV hη hU ha hb ⟨hs1, hs2, ht1, ht2, hS, hT⟩ hlt h0 h1'
    have h2 := eta_dHi_zero hω hd hV hη hU ha h0 h1
    unfold TailUpper
    rw [this, h2]
    by_cases h3 : x < t
    · simp [h3]
    · by_cases h4 : x < s
      · simp [h3, h4]
      · simp [h3, h4]

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

theorem HU_priv (h : ω.IsLegalNonempty) (hd : ω.case = .d) (hV : IsConnectedSkew V) {s t : ℤ}
    (hph : ω.IsPhases s t) (hlt : t < s) {α : ℤ} (h0 : ω.widthZ ≤ α) (h1 : α < ω.period) :
    HU ω V α = height ω.E (minContent ω.E + α) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hv : ValidClass (minContent V) (maxContent V) ω.widthZ (minContent V) α :=
    Or.inl ⟨le_refl _, hmM⟩
  have hmp := h.mixed_profile hV hd hph hlt (J := minContent V) (a := α) (by omega) h1 hv
  have e : alignedC0 ω V + α = minContent ω.E + (minContent V * ω.period + α) := by
    unfold alignedC0; ring
  unfold HU
  rw [e, hmp.2.1 h0, aligned_profM_first hV]
  ring

theorem eta_height_E (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hU : η.E = ω.compose V) (x : ℤ) :
    height η.E (minContent η.E + x) = HU ω V x := by
  rw [eta_minContent hω hV hU, hU]; rfl

theorem eta_height_W_empty (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {x : ℤ}
    (h0 : 0 ≤ x) (h1 : x < ω.widthZ) :
    height η.W (minContent η.E + x) = Om ω x := by
  have hl := aligned_legalNonempty hω hd
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hw := eta_widthZ_empty hω hV hη hU ha hb
  have hdL := eta_dLo_empty hω hd hV hη hU ha hb hph hlt h0 h1
  have hdH := eta_dHi_zero hω hd hV hη hU ha h0 (by omega)
  have hH := HU_first hl hd hV hph hlt h0 h1
  have hlo := eta_lo_hi_height hω hV hU x
  unfold height
  rw [hηl.diagHi_W h0 (by omega), hηl.diagLo_W h0 (by omega)]
  unfold dLo at hdL
  unfold dHi at hdH
  unfold Om at hH
  have e1 := hH
  by_cases h2 : x < t
  · simp only [h2, ↓reduceIte] at hdL e1
    unfold Om; omega
  · by_cases h3 : x < s
    · simp only [h2, h3, ↓reduceIte] at hdL e1
      unfold Om; omega
    · simp only [h2, h3, ↓reduceIte] at hdL e1
      unfold Om; omega

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

private theorem eq_of_diag_eq {A B : Diagram} (hA : IsConnectedSkew A) (hB : IsConnectedSkew B)
    (hc : contents A = contents B) (hlo : ∀ k ∈ contents A, diagLo A k = diagLo B k)
    (hhi : ∀ k ∈ contents A, diagHi A k = diagHi B k) : A = B := by
  have sA := isConnectedSkew_iff_diagonal.mp hA
  have sB := isConnectedSkew_iff_diagonal.mp hB
  ext ⟨i, j⟩
  have e : (i, j) = (i, i + (j - i)) := by ext <;> simp
  rw [e, sA.mem_iff, sB.mem_iff, ← hc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rw [← hlo _ h1]; exact h2, by rw [← hhi _ h1]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rw [hlo _ h1]; exact h2, by rw [hhi _ h1]; exact h3⟩

/-- The common value of the heights of both sides at the class `(J', i, α)`. -/
noncomputable def reassocTarget (ω : MarkedInner) (V C : Diagram) (s t J' i α : ℤ) : ℤ :=
  if i = 0 ∧ α < ω.widthZ then
    Om ω α + (if α < t then profM C (J' - 1) else if α < s then profS C J' - 1
      else profM C J')
  else HU ω V (i * ω.period + α) + profM C J' - 1

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

theorem class_index_eq (hω : ω.IsLegal) (hV : IsConnectedSkew V) (hU : η.E = ω.compose V)
    {a : ℤ} (ha : content η.v = a * ω.period) (J' i α : ℤ) :
    minContent η.E + (J' * η.period + (i * ω.period + α)) =
      minContent ω.E + ((minContent V + (J' * a + i)) * ω.period + α) := by
  have hper : η.period = a * ω.period := ha
  rw [eta_minContent hω hV hU, hper]
  unfold alignedC0
  ring

theorem FL_height (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) (hC : IsConnectedSkew C) {s t : ℤ} (hph : ω.IsPhases s t)
    (hlt : t < s) {J' i α : ℤ} (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ)) (hα0 : 0 ≤ α)
    (hα1 : α < ω.period)
    (hv : ValidClass (minContent C) (maxContent C) ω.widthZ J' (i * ω.period + α)) :
    height (η.compose C)
      (minContent ω.E + ((minContent V + (J' * (span V : ℤ) + i)) * ω.period + α)) =
      reassocTarget ω V C s t J' i α := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hηc := eta_case_d hω hd hV hη hU ha
  have hphη := eta_isPhases_empty hω hd hV hη hU ha hb hph hlt
  have hw := eta_widthZ_empty hω hV hη hU ha hb
  have hper : η.period = a * ω.period := ha
  have hq0 : 0 < ω.period := by omega
  have hx0 : 0 ≤ i * ω.period + α := add_nonneg (mul_nonneg hi0 hq0.le) hα0
  have hxq : i * ω.period + α < η.period := by
    rw [hper, hb]; nlinarith
  have hvη : ValidClass (minContent C) (maxContent C) η.widthZ J' (i * ω.period + α) := by
    rw [hw]; exact hv
  have hmp := hηl.mixed_profile hC hηc hphη hlt (J := J') (a := i * ω.period + α) hx0 hxq hvη
  have ek := class_index_eq hω hV hU ha J' i α
  rw [← hb, ← ek]
  unfold reassocTarget
  by_cases hlow : i = 0 ∧ α < ω.widthZ
  · obtain ⟨rfl, hαw⟩ := hlow
    have hx : (0 : ℤ) * ω.period + α = α := by ring
    rw [hx] at hmp ⊢
    simp only [hαw, and_self, ↓reduceIte]
    by_cases h2 : α < t
    · rw [hmp.2.2.1 h2, eta_height_W_empty hω hd hV hη hU ha hb hph hlt hα0 hαw]
      simp [h2]
    · by_cases h3 : α < s
      · rw [hmp.2.2.2.1 (by omega) h3, eta_height_W_empty hω hd hV hη hU ha hb hph hlt hα0 hαw]
        simp [h2, h3]; ring
      · rw [hmp.2.2.2.2 (by omega) (by omega),
          eta_height_W_empty hω hd hV hη hU ha hb hph hlt hα0 hαw]
        simp [h2, h3]
  · have hnot : ¬ (i = 0 ∧ α < ω.widthZ) := hlow
    simp only [hnot, ↓reduceIte]
    have hge : η.widthZ ≤ i * ω.period + α := by
      rw [hw]
      by_cases hi : i = 0
      · subst hi; have : ¬ α < ω.widthZ := fun h => hnot ⟨rfl, h⟩
        omega
      · have : 1 ≤ i := by omega
        nlinarith
    rw [hmp.2.1 hge, eta_height_E hω hV hU]

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

theorem HU_class (h : ω.IsLegalNonempty) (hd : ω.case = .d) (hV : IsConnectedSkew V) {s t : ℤ}
    (hph : ω.IsPhases s t) (hlt : t < s) {i α : ℤ} (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ))
    (hα0 : 0 ≤ α) (hα1 : α < ω.period) :
    HU ω V (i * ω.period + α) =
      if α < ω.widthZ then
        Om ω α + (if α < t then profM V (minContent V + i - 1)
          else if α < s then profS V (minContent V + i) - 1 else profM V (minContent V + i))
      else height ω.E (minContent ω.E + α) + profM V (minContent V + i) - 1 := by
  have hq := h.width_lt_period
  have hsp := aligned_span_eq hV
  have hv : ValidClass (minContent V) (maxContent V) ω.widthZ (minContent V + i) α :=
    Or.inl ⟨by omega, by omega⟩
  have hmp := h.mixed_profile hV hd hph hlt (J := minContent V + i) (a := α) hα0 hα1 hv
  have e : alignedC0 ω V + (i * ω.period + α) =
      minContent ω.E + ((minContent V + i) * ω.period + α) := by
    unfold alignedC0; ring
  unfold HU Om
  rw [e]
  by_cases hw : α < ω.widthZ
  · simp only [hw, ↓reduceIte]
    by_cases h2 : α < t
    · rw [hmp.2.2.1 h2]; simp [h2]
    · by_cases h3 : α < s
      · rw [hmp.2.2.2.1 (by omega) h3]; simp [h2, h3]; ring
      · rw [hmp.2.2.2.2 (by omega) hw]; simp [h2, h3]
  · simp only [hw, ↓reduceIte]
    rw [hmp.2.1 (by omega)]

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

theorem FR_height (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hC : IsConnectedSkew C) {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {J' i α : ℤ}
    (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ)) (hα0 : 0 ≤ α) (hα1 : α < ω.period)
    (hv : ValidClass (minContent C) (maxContent C) ω.widthZ J' (i * ω.period + α)) :
    height (ω.compose ((emptyMarkH V).compose C))
      (minContent ω.E + ((minContent V + (J' * (span V : ℤ) + i)) * ω.period + α)) =
      reassocTarget ω V C s t J' i α := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hsp := aligned_span_eq hV
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hX : IsConnectedSkew ((emptyMarkH V).compose C) :=
    (emptyMarkH_isLegal hV).isConnectedSkew_compose hC
  have hminX := emptyH_minContent hV hC
  have hmaxX := emptyH_maxContent hV hC
  have hCmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  -- the class `(J, α)` of the composite with the outer `X`
  have hvX : ValidClass (minContent ((emptyMarkH V).compose C))
      (maxContent ((emptyMarkH V).compose C)) ω.widthZ
      (minContent V + (J' * (span V : ℤ) + i)) α := by
    unfold ValidClass at hv ⊢
    rw [hminX, hmaxX]
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor <;> nlinarith
    · right
      have hi : i = 0 := by
        by_contra hne
        have : 1 ≤ i := by omega
        have : ω.period ≤ i * ω.period := by nlinarith
        omega
      have hα : α < ω.widthZ := by rw [hi] at h2; simpa using h2
      subst hi
      refine ⟨?_, hα⟩
      rw [h1]; ring
  have hmp := hl.mixed_profile hX hd hph hlt
    (J := minContent V + (J' * (span V : ℤ) + i)) (a := α) hα0 hα1 hvX
  have ek : minContent V + (J' * (span V : ℤ) + i) - 1 =
      minContent V + (J' * (span V : ℤ) + (i - 1)) := by ring
  have hPV : ∀ j, 0 ≤ j → j < (span V : ℤ) → minContent V ≤ minContent V + j ∧
      minContent V + j ≤ maxContent V := fun j h0 h1 => ⟨by omega, by omega⟩
  unfold reassocTarget Om
  by_cases hlow : i = 0 ∧ α < ω.widthZ
  · obtain ⟨rfl, hαw⟩ := hlow
    simp only [hαw, and_self, ↓reduceIte]
    have hJ0 : minContent V + (J' * (span V : ℤ) + 0) - 1 =
        minContent V + ((J' - 1) * (span V : ℤ) + ((span V : ℤ) - 1)) := by ring
    have hVl : minContent V + ((span V : ℤ) - 1) = maxContent V := by omega
    by_cases h2 : α < t
    · rw [hmp.2.2.1 h2]
      simp only [h2, ↓reduceIte]
      rw [hJ0, emptyH_profM hV hC (J := J' - 1) (i := (span V : ℤ) - 1) (by omega) (by omega)]
      by_cases hr : minContent C ≤ J' - 1 ∧ J' - 1 ≤ maxContent C
      · simp only [hr.1, hr.2, and_self, ↓reduceIte]
        rw [hVl, aligned_profM_last hV]; ring
      · simp only [hr, ↓reduceIte]
        rw [aligned_profM_eq_zero hr]
    · by_cases h3 : α < s
      · rw [hmp.2.2.2.1 (by omega) h3]
        simp only [h2, h3, ↓reduceIte]
        rw [emptyH_profS_zero hV hC J']; ring
      · rw [hmp.2.2.2.2 (by omega) hαw]
        simp only [h2, h3, ↓reduceIte]
        have := emptyH_profM hV hC (J := J') (i := 0) (le_refl _) (by omega)
        rw [add_zero] at this ⊢
        rw [this]
        by_cases hr : minContent C ≤ J' ∧ J' ≤ maxContent C
        · simp only [hr.1, hr.2, and_self, ↓reduceIte]
          have : minContent V + 0 = minContent V := by ring
          rw [this, aligned_profM_first hV]; ring
        · simp only [hr, ↓reduceIte]
          rw [aligned_profM_eq_zero hr]
  · have hnot : ¬ (i = 0 ∧ α < ω.widthZ) := hlow
    simp only [hnot, ↓reduceIte]
    have hJr : minContent C ≤ J' ∧ J' ≤ maxContent C := by
      rcases hv with h | ⟨h1, h2⟩
      · exact h
      · exfalso
        apply hnot
        refine ⟨?_, ?_⟩
        · by_contra hne
          have : 1 ≤ i := by omega
          have : ω.period ≤ i * ω.period := by nlinarith
          omega
        · have hi : i = 0 := by
            by_contra hne
            have : 1 ≤ i := by omega
            have : ω.period ≤ i * ω.period := by nlinarith
            omega
          rw [hi] at h2; simpa using h2
    have hHU := HU_class hl hd hV hph hlt hi0 hi1 hα0 hα1
    unfold Om at hHU
    have pM := emptyH_profM hV hC (J := J') hi0 hi1
    simp only [hJr.1, hJr.2, and_self, ↓reduceIte] at pM
    by_cases hw : α < ω.widthZ
    · simp only [hw, ↓reduceIte] at hHU
      have hi1' : 1 ≤ i := by
        by_contra hne
        exact hnot ⟨by omega, hw⟩
      have pM1 := emptyH_profM hV hC (J := J') (i := i - 1) (by omega) (by omega)
      simp only [hJr.1, hJr.2, and_self, ↓reduceIte] at pM1
      have pS := emptyH_profS_pos hV hC (J := J') hi1' hi1
      simp only [hJr.1, hJr.2, and_self, ↓reduceIte] at pS
      by_cases h2 : α < t
      · rw [hmp.2.2.1 h2, ek, pM1, hHU]
        simp only [h2, ↓reduceIte]
        have : minContent V + i - 1 = minContent V + (i - 1) := by ring
        rw [this]; ring
      · by_cases h3 : α < s
        · rw [hmp.2.2.2.1 (by omega) h3, pS, hHU]
          simp only [h2, h3, ↓reduceIte]
          ring
        · rw [hmp.2.2.2.2 (by omega) hw, pM, hHU]
          simp only [h2, h3, ↓reduceIte]
          ring
    · simp only [hw, ↓reduceIte] at hHU
      rw [hmp.2.1 (by omega), pM, hHU]
      ring

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

theorem FL_diagHi (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) (hC : IsConnectedSkew C) {s t : ℤ} (hph : ω.IsPhases s t)
    (hlt : t < s) {J' i α : ℤ} (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ)) (hα0 : 0 ≤ α)
    (hα1 : α < ω.period)
    (hv : ValidClass (minContent C) (maxContent C) ω.widthZ J' (i * ω.period + α)) :
    diagHi (η.compose C)
      (minContent ω.E + ((minContent V + (J' * (span V : ℤ) + i)) * ω.period + α)) =
      ω.hi α + (minContent V + (J' * (span V : ℤ) + i)) * ω.rowShift := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hηc := eta_case_d hω hd hV hη hU ha
  have hphη := eta_isPhases_empty hω hd hV hη hU ha hb hph hlt
  have hw := eta_widthZ_empty hω hV hη hU ha hb
  have hper : η.period = a * ω.period := ha
  have hx0 : 0 ≤ i * ω.period + α := add_nonneg (mul_nonneg hi0 hq0.le) hα0
  have hxq : i * ω.period + α < η.period := by
    rw [hper, hb]; nlinarith
  have hvη : ValidClass (minContent C) (maxContent C) η.widthZ J' (i * ω.period + α) := by
    rw [hw]; exact hv
  have hmp := hηl.mixed_profile hC hηc hphη hlt (J := J') (a := i * ω.period + α) hx0 hxq hvη
  have ek := class_index_eq hω hV hU ha J' i α
  rw [← hb, ← ek, hmp.1]
  have hdm := aligned_divmod_eq (j := i) hq0 hα0 hα1
  have hspan : (span V : ℤ) * ω.period + ω.width - 1 ≥ i * ω.period + α := by
    have hwz : (ω.width : ℤ) = ω.widthZ := rfl
    nlinarith
  have hwz' : (ω.width : ℤ) = ω.widthZ := rfl
  have hH := eta_hi_formula hω hd hV hU hx0 (by nlinarith)
  rw [hdm.1, hdm.2] at hH
  have hrs := eta_rowShift hω hd hV hη hU ha
  change η.hi (i * ω.period + α) + J' * η.rowShift = _
  rw [hH, hrs, hb]
  ring

theorem FR_diagHi (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hC : IsConnectedSkew C) {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {J' i α : ℤ}
    (hi0 : 0 ≤ i) (hi1 : i < (span V : ℤ)) (hα0 : 0 ≤ α) (hα1 : α < ω.period)
    (hv : ValidClass (minContent C) (maxContent C) ω.widthZ J' (i * ω.period + α)) :
    diagHi (ω.compose ((emptyMarkH V).compose C))
      (minContent ω.E + ((minContent V + (J' * (span V : ℤ) + i)) * ω.period + α)) =
      ω.hi α + (minContent V + (J' * (span V : ℤ) + i)) * ω.rowShift := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hsp := aligned_span_eq hV
  have hX : IsConnectedSkew ((emptyMarkH V).compose C) :=
    (emptyMarkH_isLegal hV).isConnectedSkew_compose hC
  have hminX := emptyH_minContent hV hC
  have hmaxX := emptyH_maxContent hV hC
  have hvX : ValidClass (minContent ((emptyMarkH V).compose C))
      (maxContent ((emptyMarkH V).compose C)) ω.widthZ
      (minContent V + (J' * (span V : ℤ) + i)) α := by
    unfold ValidClass at hv ⊢
    rw [hminX, hmaxX]
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor <;> nlinarith
    · right
      have hi : i = 0 := by
        by_contra hne
        have : 1 ≤ i := by omega
        have : ω.period ≤ i * ω.period := by nlinarith
        omega
      have hα : α < ω.widthZ := by rw [hi] at h2; simpa using h2
      subst hi
      refine ⟨?_, hα⟩
      rw [h1]; ring
  have hmp := hl.mixed_profile hX hd hph hlt
    (J := minContent V + (J' * (span V : ℤ) + i)) (a := α) hα0 hα1 hvX
  rw [hmp.1]
  rfl

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

/-- **`lem:gluing-aligned`, case (d) of `ω`, `b = 0`.**  For `a = N_V` the lower mark is the
horizontal empty mark of `V` and `C ∘_η U = (C ∘_{∅} V) ∘_ω E` for every connected `C`. -/
theorem reassoc_empty (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) (hC : IsConnectedSkew C) :
    η.compose C = ω.compose ((emptyMarkH V).compose C) := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hsp := aligned_span_eq hV
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hCmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hd) hph
  have hX : IsConnectedSkew ((emptyMarkH V).compose C) :=
    (emptyMarkH_isLegal hV).isConnectedSkew_compose hC
  have hL : IsConnectedSkew (η.compose C) := hη.isConnectedSkew_compose hC
  have hR : IsConnectedSkew (ω.compose ((emptyMarkH V).compose C)) :=
    hω.isConnectedSkew_compose hX
  have hper : η.period = a * ω.period := ha
  have hw := eta_widthZ_empty hω hV hη hU ha hb
  have hminX := emptyH_minContent hV hC
  have hmaxX := emptyH_maxContent hV hC
  have hminL := hη.minContent_compose hC
  have hmaxL := hη.maxContent_compose hC
  have hminR := hω.minContent_compose hX
  have hmaxR := hω.maxContent_compose hX
  have hηmin := eta_minContent hω hV hU
  have hwη : (η.width : ℤ) = ω.widthZ := hw
  have hwω : (ω.width : ℤ) = ω.widthZ := rfl
  have hLmin : minContent (η.compose C) =
      minContent ω.E + (minContent V + minContent C * (span V : ℤ)) * ω.period := by
    rw [hminL, hηmin, hper, hb]; unfold alignedC0; ring
  have hLmax : maxContent (η.compose C) =
      minContent ω.E + (minContent V + maxContent C * (span V : ℤ) + (span V : ℤ)) * ω.period
        + ω.widthZ - 1 := by
    rw [hmaxL, hηmin, hper, hb, hwη]; unfold alignedC0; ring
  have hRmin : minContent (ω.compose ((emptyMarkH V).compose C)) =
      minContent ω.E + (minContent V + minContent C * (span V : ℤ)) * ω.period := by
    rw [hminR, hminX]
  have hRmax : maxContent (ω.compose ((emptyMarkH V).compose C)) =
      minContent ω.E + (minContent V + maxContent C * (span V : ℤ) + (span V : ℤ)) * ω.period
        + ω.widthZ - 1 := by
    rw [hmaxR, hmaxX, hwω]; ring
  have sL := isConnectedSkew_iff_diagonal.mp hL
  have sR := isConnectedSkew_iff_diagonal.mp hR
  -- the classes of a content
  have key : ∀ k ∈ contents (η.compose C), ∃ J' i α : ℤ, 0 ≤ i ∧ i < (span V : ℤ) ∧ 0 ≤ α ∧
      α < ω.period ∧ ValidClass (minContent C) (maxContent C) ω.widthZ J' (i * ω.period + α) ∧
      k = minContent ω.E + ((minContent V + (J' * (span V : ℤ) + i)) * ω.period + α) := by
    intro k hk
    rw [sL.mem_contents_iff, hLmin, hLmax] at hk
    obtain ⟨hk1, hk2⟩ := hk
    set r := k - minContent ω.E with hr
    have hr1 := Int.mul_ediv_add_emod r ω.period
    have hr2 := Int.emod_nonneg r hq0.ne'
    have hr3 := Int.emod_lt_of_pos r hq0
    set J := r / ω.period with hJ
    set α := r % ω.period with hα
    have hN : 1 ≤ (span V : ℤ) := by omega
    have hJ1 : minContent V + minContent C * (span V : ℤ) ≤ J := by
      by_contra hne
      have : J + 1 ≤ minContent V + minContent C * (span V : ℤ) := by omega
      have := mul_le_mul_of_nonneg_right this hq0.le
      linarith
    have hJ2 : J ≤ minContent V + maxContent C * (span V : ℤ) + (span V : ℤ) := by
      by_contra hne
      have : minContent V + maxContent C * (span V : ℤ) + (span V : ℤ) + 1 ≤ J := by omega
      have := mul_le_mul_of_nonneg_right this hq0.le
      linarith
    have hJ3 : J = minContent V + maxContent C * (span V : ℤ) + (span V : ℤ) → α < ω.widthZ := by
      intro he
      rw [he] at hr1
      linarith
    set u := J - minContent V with hu
    have hu1 := Int.mul_ediv_add_emod u (span V : ℤ)
    have hu2 := Int.emod_nonneg u (by omega : (span V : ℤ) ≠ 0)
    have hu3 := Int.emod_lt_of_pos u (by omega : 0 < (span V : ℤ))
    set J' := u / (span V : ℤ) with hJ'
    set i := u % (span V : ℤ) with hi
    refine ⟨J', i, α, hu2, hu3, hr2, hr3, ?_, ?_⟩
    · unfold ValidClass
      have hc1 : minContent C ≤ J' := by
        by_contra hne
        have : J' + 1 ≤ minContent C := by omega
        have := mul_le_mul_of_nonneg_right this (by omega : (0 : ℤ) ≤ span V)
        linarith
      by_cases hc2 : J' ≤ maxContent C
      · left; exact ⟨hc1, hc2⟩
      · right
        have hc3 : J' = maxContent C + 1 := by
          by_contra hne
          have : maxContent C + 2 ≤ J' := by omega
          have := mul_le_mul_of_nonneg_right this (by omega : (0 : ℤ) ≤ span V)
          linarith
        have hi0 : i = 0 := by
          rw [hc3] at hu1
          linarith
        refine ⟨hc3, ?_⟩
        have hJe : J = minContent V + maxContent C * (span V : ℤ) + (span V : ℤ) := by
          rw [hi0, hc3] at hu1
          linarith
        have := hJ3 hJe
        rw [hi0]; simpa using this
    · have e : J = minContent V + (J' * (span V : ℤ) + i) := by linarith
      rw [← e]; linarith
  refine eq_of_diag_eq hL hR ?_ ?_ ?_
  · rw [sL.contents_eq, sR.contents_eq, hLmin, hLmax, hRmin, hRmax]
  · intro k hk
    obtain ⟨J', i, α, hi0, hi1, hα0, hα1, hv, rfl⟩ := key k hk
    have h1 := FL_diagHi hω hd hV hη hU ha hb hC hph hlt hi0 hi1 hα0 hα1 hv
    have h2 := FR_diagHi hω hd hV hC hph hlt hi0 hi1 hα0 hα1 hv
    have h3 := FL_height hω hd hV hη hU ha hb hC hph hlt hi0 hi1 hα0 hα1 hv
    have h4 := FR_height hω hd hV hC hph hlt hi0 hi1 hα0 hα1 hv
    unfold height at h3 h4
    omega
  · intro k hk
    obtain ⟨J', i, α, hi0, hi1, hα0, hα1, hv, rfl⟩ := key k hk
    have h1 := FL_diagHi hω hd hV hη hU ha hb hC hph hlt hi0 hi1 hα0 hα1 hv
    have h2 := FR_diagHi hω hd hV hC hph hlt hi0 hi1 hα0 hα1 hv
    rw [h1, h2]



end MarkedInner
end SkewGluing
