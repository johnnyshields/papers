/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/Statement.lean`. -/
import GluingCore.Aligned.Lattice
import GluingCore.MarkLocality

/-!
# The conclusion of `lem:gluing-aligned`, and the empty lower mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`).

`IsReassociation ω η V μ γ` is the conclusion of `lem:gluing-aligned` for the chart
`U = V ∘_ω E` and the mark `η` on `U`: a legal mark `μ` on `V` and `γ ∈ {id, AT}` with
`C ∘_η U = (γ(C) ∘_μ V) ∘_ω E` for every connected `C`, where `γ = AT` only for an empty `μ`.
Here `μ` and `γ` are fixed before `C` is chosen.  The identity is an equality of cell sets,
without translation.  The empty mark `emptyMarkH V` is legal on every connected `V`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

/-- The conclusion of `lem:gluing-aligned` (`eq:gluing-reassociation`) for the marked inner `ω`,
the outer `V` and the mark `η` on `U = V ∘_ω E`: the legal lower mark `μ` on `V` and the map
`γ ∈ {id, AT}` (`γ = AT` only when `μ` is empty), such that for every connected `C`,
`C ∘_η U = (γ(C) ∘_μ V) ∘_ω E`. -/
structure IsReassociation (ω η : MarkedInner) (V : Diagram) (μ : MarkedInner)
    (γ : Diagram → Diagram) : Prop where
  legal : μ.IsLegal
  inner : μ.E = V
  gamma : γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)
  compose_eq : ∀ C : Diagram, IsConnectedSkew C → η.compose C = ω.compose (μ.compose (γ C))

end MarkedInner

end GluingCore
