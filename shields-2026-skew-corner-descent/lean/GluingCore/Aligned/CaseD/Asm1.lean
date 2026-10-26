/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Asm1.lean`. -/
import GluingCore.Aligned.CaseD.Asm0

/-!
# Aligned marks, case (d): the heights of `C ∘_η U`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-mixed-profile`, `eq:gluing-nested-count`).

For a legal case-(d) mark `ω` with a nonempty copy: `height W₋ = height E - [dLo = 1]` on a marked
diagonal (`alD_height_W_d`).  Consequently, for `η` on `U = V ∘_ω E` and a connected `C`, the
height of `C ∘_η U` on the diagonal `x` of `η` is `HU(x) - [δ_x = 1] + CT_{δ_x}(J)` for a marked
`x` and `HU(x) + M^C_J - 1` for a private one, `δ_x = η.dLo x`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω η : MarkedInner} {V C : Diagram}

theorem alD_height_W_d (hl : ω.IsLegalNonempty) (hc : ω.case = .d) {i : ℤ} (hi0 : 0 ≤ i)
    (hi1 : i < ω.widthZ) :
    height ω.W (minContent ω.E + i) =
      height ω.E (minContent ω.E + i) - (if ω.dLo i = 1 then 1 else 0) := by
  have h1 := hl.diagHi_W hi0 (by omega : i ≤ ω.widthZ - 1)
  have h2 := hl.diagLo_W hi0 (by omega : i ≤ ω.widthZ - 1)
  have hs := hl.sides_d hc hi0 (by omega : i ≤ ω.widthZ - 1)
  have th := hl.thin_upper hi0 (by omega : i ≤ ω.widthZ - 1)
  have tl := hl.thin_lower i hi0 (by omega : i ≤ ω.widthZ - 1)
  unfold height
  rw [h1, h2]
  unfold dHi at hs
  unfold dLo at th tl ⊢
  unfold lo hi at *
  split_ifs <;> omega

theorem alD_FL_height_marked (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hC : IsConnectedSkew C) {J x : ℤ} (hx0 : 0 ≤ x) (hx1 : x < η.widthZ)
    (hv : ValidClass (minContent C) (maxContent C) η.widthZ J x) :
    height (η.compose C) (minContent η.E + (J * η.period + x)) =
      HU ω V x - (if η.dLo x = 1 then 1 else 0) + alD_CT C (η.dLo x) J := by
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hηc := eta_case_d hω hd hV hη hU ha
  rw [alD_mixed_marked hηl hC hηc hx0 hx1 hv, alD_height_W_d hηl hηc hx0 hx1,
    eta_height_E hω hV hU]

theorem alD_FL_height_private (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hC : IsConnectedSkew C) {J x : ℤ} (hx0 : η.widthZ ≤ x) (hx1 : x < η.period)
    (hJ : minContent C ≤ J ∧ J ≤ maxContent C) :
    height (η.compose C) (minContent η.E + (J * η.period + x)) =
      HU ω V x + profM C J - 1 := by
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hηc := eta_case_d hω hd hV hη hU ha
  rw [alD_mixed_private hηl hC hηc hx0 hx1 hJ, eta_height_E hω hV hU]

end MarkedInner

end GluingCore
