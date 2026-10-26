/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Asm0.lean`. -/
import GluingCore.Aligned.CaseD.Gen

/-!
# Aligned marks, case (d): the southeast rows of the two sides of the reassociation

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-reassociation`).

For `η` on `U = V ∘_ω E` of displacement content `a q` and the lower mark `μ` on `V`, the
southeast row of `C ∘_η U` and of `(C ∘_μ V) ∘_ω E` on the diagonal of relative content
`(m + J a + i) q + α` is `ω.hi α + (m + J a + i) p` (`alD_FL_diagHi`, `alD_FR_diagHi`).  The class
bookkeeping `alD_classValid` relates the validity of a class for `η` and for `ω ∘ X`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

theorem alD_FL_diagHi (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hC : IsConnectedSkew C) {J i α : ℤ} (hi0 : 0 ≤ i) (hi1 : i < a) (hα0 : 0 ≤ α)
    (hα1 : α < ω.period)
    (hv : ValidClass (minContent C) (maxContent C) η.widthZ J (i * ω.period + α)) :
    diagHi (η.compose C)
      (minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α)) =
      ω.hi α + (minContent V + (J * a + i)) * ω.rowShift := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hηc := eta_case_d hω hd hV hη hU ha
  obtain ⟨s, t, hphη⟩ := hηl.exists_phases
  have hlt := hηl.phases_lt (Or.inr hηc) hphη
  have hap := eta_pos hω hV hη hU ha
  have hle := eta_le_span hω hV hη hU ha
  have hper : η.period = a * ω.period := ha
  have hx0 : 0 ≤ i * ω.period + α := add_nonneg (mul_nonneg hi0 hq0.le) hα0
  have hxq : i * ω.period + α < η.period := by
    rw [hper]; nlinarith
  have hmp := hηl.mixed_profile hC hηc hphη hlt (J := J) (a := i * ω.period + α) hx0 hxq hv
  have ek := class_index_eq hω hV hU ha J i α
  rw [← ek, hmp.1]
  have hdm := aligned_divmod_eq (j := i) hq0 hα0 hα1
  have hwz' : (ω.width : ℤ) = ω.widthZ := rfl
  have hH := eta_hi_formula hω hd hV hU hx0 (by nlinarith)
  rw [hdm.1, hdm.2] at hH
  have hrs := eta_rowShift hω hd hV hη hU ha
  change η.hi (i * ω.period + α) + J * η.rowShift = _
  rw [hH, hrs]
  ring

theorem alD_FR_diagHi (hω : ω.IsLegal) (hd : ω.case = .d) {X : Diagram}
    (hX : IsConnectedSkew X) {J α : ℤ} (hα0 : 0 ≤ α) (hα1 : α < ω.period)
    (hv : ValidClass (minContent X) (maxContent X) ω.widthZ J α) :
    diagHi (ω.compose X) (minContent ω.E + (J * ω.period + α)) = ω.hi α + J * ω.rowShift := by
  have hl := aligned_legalNonempty hω hd
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hd) hph
  have := (hl.mixed_profile hX hd hph hlt hα0 hα1 hv).1
  rw [this]
  rfl

end MarkedInner

end GluingCore
