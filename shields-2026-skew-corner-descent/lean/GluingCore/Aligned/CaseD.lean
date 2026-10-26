/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD.lean`. -/
import GluingCore.Aligned.CaseD.Identity

/-!
# Aligned marks, case (d)

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-walk-signs`,
`eq:gluing-nested-count`).

`MarkedInner.aligned_mixed_d_proof` is the case-(d) assertion of `lem:gluing-aligned`: for a legal
case-(d) mark `ω`, a connected `V`, and a legal mark `η` on `U = V ∘_ω E` whose displacement has
content `a q`, there are a legal mark `μ` on `V` and `γ ∈ {id, AT}` with
`C ∘_η U = (γ(C) ∘_μ V) ∘_ω E` for every connected `C`.  The upper mark `η` is studied in
`Aligned/CaseD/Eta.lean`, the case `b = N_V - a = 0` is `Aligned/CaseD/Empty.lean`, and the walk
of `eq:gluing-walk-signs` is `Aligned/CaseD/Walk.lean`.

For `b > 0` the lower mark is `μ = alD_lowerMark V a θ` with `Z = V ∩ (V - z)`,
`z = (θ, θ + a)`: its data from the walk (`Data.lean`), its copy and complements (`Mark0.lean`,
`Mark1.lean`, `Compl.lean`), its legality (`Legal0.lean`, `Legal1.lean`, `Legal2.lean`), the
nested count `eq:gluing-nested-count` for the composite `C ∘_μ V` in the four attachment cases of
`μ` (`Nci.lean`, `NcOrd.lean`, `NcD.lean`, and by rotation `Rot0.lean` to `Rot4.lean`), and the
identity (`Asm0.lean` to `Asm3.lean`, `Identity.lean`).

Sorry-free.
-/

namespace GluingCore
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-! ### The lemma -/

/-- **`lem:gluing-aligned`, case (d) of `ω`, `b = 0`.**  For `a = N_V` the lower mark is the
horizontal empty mark of `V` and `γ = id`. -/
theorem aligned_mixed_d_empty (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hb : a = (span V : ℤ)) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ :=
  ⟨emptyMarkH V, id, ⟨emptyMarkH_isLegal hV, rfl, Or.inl rfl,
    fun C hC => reassoc_empty (C := C) hω hd hV hη hU ha hb hC⟩⟩

/-- **`lem:gluing-aligned`, case (d) of `ω`, `b > 0`.**  The lower mark is
`μ = alD_lowerMark V a θ`, `Z = V ∩ (V - z)` with `z = (θ, θ + a)` (`Aligned/CaseD/Legal2.lean`,
legal by `alD_lowerMark_isLegal`), and `γ = id`. -/
theorem aligned_mixed_d_pos (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hpos : a < (span V : ℤ)) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ := by
  obtain ⟨θ, hD⟩ := alD_data hω hd hV hη hU ha hpos
  exact ⟨alD_lowerMark V a θ, id, ⟨alD_lowerMark_isLegal hV hD, rfl, Or.inl rfl,
    fun C hC => alD_identity hω hd hV hη hU ha hD hC⟩⟩

/-- **`lem:gluing-aligned`, case (d) of `ω`**: the southeast boundary is periodic, the walk
`eq:gluing-walk-signs` fixes the displacement `a v` and the lower mark `Z = V ∩ (V - z)`, and the
nested count `eq:gluing-nested-count` gives the identity. -/
theorem aligned_mixed_d_proof (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    ∃ (μ : MarkedInner) (γ : Diagram → Diagram), IsReassociation ω η V μ γ := by
  rcases lt_or_eq_of_le (eta_le_span hω hV hη hU ha) with hlt | heq
  · exact aligned_mixed_d_pos hω hd hV hη hU ha hlt
  · exact aligned_mixed_d_empty hω hd hV hη hU ha heq

end MarkedInner

/-! ### Checked examples -/

section Examples

open MarkedInner

/-- The column `(1, 1)`. -/
def alignedExV : Diagram := skewOf [1, 1] []

/-- The mark of period four and width one on `U = V ∘_ω E`, `ω` the singleton case-(d) hook mark
of period two, `V` the column `(1, 1)` (`a = N_V = 2`, so `b = 0`). -/
def alignedExEta : MarkedInner where
  E := compose alignedExV hookInner
  W := {(2, -1)}
  v := (-2, 2)
  case := .d

example : alignedExEta.IsLegal := by decide +kernel

/-- `lem:gluing-aligned`, case (d), `b = 0`, on sample outers. -/
example : ∀ C ∈ [skewOf [2] [], skewOf [1, 1] [], skewOf [2, 1] [], skewOf [2, 2] [],
      skewOf [3, 2] [1]],
    alignedExEta.compose C = hookInner.compose ((emptyMarkH alignedExV).compose C) := by
  decide +kernel

example : ∃ (μ : MarkedInner) (γ : Diagram → Diagram),
    IsReassociation hookInner alignedExEta alignedExV μ γ :=
  aligned_mixed_d_empty (a := 2) (by decide +kernel) rfl (by decide) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel)

end Examples

end GluingCore

