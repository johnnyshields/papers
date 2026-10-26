/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Rotation.lean
import SkewMarkedFactor.Gluing.CellSchur
import SkewMarkedFactor.Gluing.Composition
import SkewMarkedFactor.Gluing.Invariance

/-!
# Composition commutes with rotation

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): the rotation of a composition,
`(D ∘_ω E)* = D* ∘_{ω*} E*`, which is the passage from the composition statement to the
reversal statement of the fiber `𝓕(ω, Q)`.

The identity `MarkedInner.rotate_compose` of `SkewMarkedFactor.Gluing.Invariance`,
an equality of cell sets
with no translation, gives the equality of Schur functions
`s_{D ∘_ω E} = s_{D* ∘_{ω*} E*}` (`cellSchur_compose_rotate_outer`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

/-- Composing with the rotated inner and the rotated outer gives a skew diagram with the same
Schur function (`rotate_compose` and `cellSchur_rotate`). -/
theorem cellSchur_compose_rotate_outer {D : Diagram} (hD : D.Nonempty) (ω : MarkedInner) :
    cellSchur (ω.compose D) =
      cellSchur (ω.rotate.compose (SkewMarkedFactor.Gluing.rotate D)) := by
  rw [rotate_compose hD, cellSchur_rotate]

end MarkedInner

end SkewMarkedFactor.Gluing
