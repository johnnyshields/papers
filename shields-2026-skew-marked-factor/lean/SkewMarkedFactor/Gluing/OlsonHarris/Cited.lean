/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Cited.lean
import SkewMarkedFactor.Gluing.CellSchur
import SkewMarkedFactor.Gluing.Composition

/-!
# The composition theorem of Olson-Harris, as a proposition

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`, and the paragraph on the fiber `𝓕(ω, Q)`): the forward
composition theorem of Olson-Harris, Thm. 5.3.9 of `OlsonHarris2024HopfApplications`, which the
paper cites as the symmetric-function input.

`OlsonHarrisComposition` is that theorem, in the cell form of `MarkedInner.compose`.  It is the
composition input of the whole development: the reversal statement and the fiber statement
(`SkewMarkedFactor.Gluing.OlsonHarris.Deductions`) are derived from it with no further
    input, and it is
proved as `olsonHarrisComposition` in `SkewMarkedFactor.Gluing.OlsonHarris.Frontier`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

/-- Olson-Harris, Thm. 5.3.9 (`OlsonHarris2024HopfApplications`), Hypotheses I–IV; proved as
`olsonHarrisComposition`, and taken as the hypothesis `hOH` by the modules that consume it.
For every legal marked inner `ω` and connected outers `D`, `D'` with the same skew Schur
function, the composites `D ∘_ω E` and `D' ∘_ω E` have the same skew Schur function.

The proof in the source is Hopf-algebraic (the kernel of `schur` on the shape Hopf algebra,
the Murnaghan–Nakayama rule for a power sum, and the ribbons removable from `D ∘_ω E`); the
McNamara–van Willigenburg route needs Hypothesis V and does not cover legal marks in general. -/
def OlsonHarrisComposition : Prop :=
  ∀ ω : MarkedInner, ω.IsLegal → ∀ D D' : Diagram, IsConnectedSkew D → IsConnectedSkew D' →
    cellSchur D = cellSchur D' → cellSchur (ω.compose D) = cellSchur (ω.compose D')

end SkewMarkedFactor.Gluing
