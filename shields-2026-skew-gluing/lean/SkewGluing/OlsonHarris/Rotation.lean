import SkewGluing.CellSchur
import SkewGluing.Composition
import SkewGluing.Invariance

/-!
# Composition commutes with rotation

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): the rotation of a composition,
`(D ∘_ω E)* = D* ∘_{ω*} E*`, which is the passage from the composition statement to the
reversal statement of the fiber `𝓕(ω, Q)`.

The identity `MarkedInner.rotate_compose` of `SkewGluing.Invariance`, an equality of cell sets
with no translation, gives the equality of Schur functions
`s_{D ∘_ω E} = s_{D* ∘_{ω*} E*}` (`cellSchur_compose_rotate_outer`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

/-- Composing with the rotated inner and the rotated outer gives a skew diagram with the same
Schur function (`rotate_compose` and `cellSchur_rotate`). -/
theorem cellSchur_compose_rotate_outer {D : Diagram} (hD : D.Nonempty) (ω : MarkedInner) :
    cellSchur (ω.compose D) = cellSchur (ω.rotate.compose (SkewGluing.rotate D)) := by
  rw [rotate_compose hD, cellSchur_rotate]

end MarkedInner

end SkewGluing
