import SkewGluing.Aligned.CaseD.Rot4

/-!
# Aligned marks, case (d): the reassociation identity for `b > 0`

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-nested-count`).

`alD_identity` is the identity `C ∘_η U = (C ∘_μ V) ∘_ω E` for the lower mark
`μ = alD_lowerMark V a θ` and every connected `C`; it follows from the nested count `alD_NC`
(`alD_identity_of_NCI`, `alD_NCI_of_NC`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

/-- **`eq:gluing-nested-count`** for the lower mark `μ` of `lem:gluing-aligned`, by the four
attachment cases of `μ`: ordinary (`alD_NC_ord`), (d) (`alD_NC_d`) and (c) by rotation
(`alD_NC_c`). -/
theorem alD_NC_all {a θ : ℤ} (hV : IsConnectedSkew V) (hD : alD_Data V a θ)
    (hC : IsConnectedSkew C) : alD_NC V a θ C := by
  by_cases hmix : (alD_lowerMark V a θ).case.IsMixed
  · rcases hmix with hc | hc
    · have hV' := isConnectedSkew_rotate hV
      have hD' := alD_data_rotate hV hD
      have hC' := isConnectedSkew_rotate hC
      have hd : (alD_lowerMark (SkewGluing.rotate V) a θ).case = .d := by
        rw [← alD_lowerMark_rotate]
        change (alD_lowerMark V a θ).case.rotate = _
        rw [hc]; rfl
      exact alD_NC_c hV hD hC hc (alD_NC_d hV' hD' hC' hd)
    · exact alD_NC_d hV hD hC hc
  · exact alD_NC_ord hV hD hC hmix

/-- **`lem:gluing-aligned`, case (d), `b > 0`: the identity.** -/
theorem alD_identity (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {θ : ℤ} (hD : alD_Data V a θ) (hC : IsConnectedSkew C) :
    η.compose C = ω.compose ((alD_lowerMark V a θ).compose C) :=
  alD_identity_of_NCI hω hd hV hη hU ha hD hC (alD_NCI_of_NC hV hD hC (alD_NC_all hV hD hC))

end MarkedInner

end SkewGluing
