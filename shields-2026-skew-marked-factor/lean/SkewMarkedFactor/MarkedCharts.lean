/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.Gluing.MarkLocality
import SkewMarkedFactor.Gluing.CellSchur

/-!
# Legal charts with both ordinary empty-edge readings

The marked geometry in «Marked composition and the power-sum action»
(`sec:action`, `eq:ordinary-offsets`) of
`shields-2026-skew-marked-factor.tex`.
The gluing predicate admits only the horizontal empty edge.  The predicate here
also admits the explicitly specified vertical empty edge; positive-width marks
retain exactly the copied Hypotheses I–IV.
-/

namespace SkewMarkedFactor
open Gluing

namespace Gluing.MarkedInner

/-- Hypotheses I–IV, including the paper's vertical empty-edge reading. -/
def IsReadoutLegal (η : MarkedInner) : Prop :=
  η.IsLegal ∨ (IsConnectedSkew η.E ∧ η = emptyMarkV η.E)

/-- Both end attachments are alike. -/
def IsOrdinary (η : MarkedInner) : Prop := ¬ η.case.IsMixed

/-- Existing legal marks belong to the paper's full chart domain. -/
theorem IsLegal.readoutLegal {η : MarkedInner} (h : η.IsLegal) : η.IsReadoutLegal :=
  Or.inl h

/-- The vertical empty datum is a genuine admitted mark, not an extra proof premise. -/
theorem emptyMarkV_readoutLegal {E : Diagram} (hE : IsConnectedSkew E) :
    (emptyMarkV E).IsReadoutLegal := Or.inr ⟨hE, rfl⟩

/-- The horizontal empty datum is admitted by the copied geometric legality theorem. -/
theorem emptyMarkH_readoutLegal {E : Diagram} (hE : IsConnectedSkew E) :
    (emptyMarkH E).IsReadoutLegal := (emptyMarkH_isLegal hE).readoutLegal

/-- Readout legality agrees with gluing legality on every nonempty mark. -/
theorem readoutLegal_iff_of_nonempty {η : MarkedInner} (hw : η.W.Nonempty) :
    η.IsReadoutLegal ↔ η.IsLegal := by
  constructor
  · rintro (h | ⟨_, he⟩)
    · exact h
    · have hW : η.W = ∅ := by simpa only [emptyMarkV] using congrArg MarkedInner.W he
      exact False.elim (Finset.nonempty_iff_ne_empty.mp hw hW)
  · exact IsLegal.readoutLegal

end Gluing.MarkedInner

namespace Gluing.Chart

/-- Proper legal charts in precisely the differential manuscript's mark domain. -/
def IsProperReadoutLegal (χ : Chart) : Prop :=
  IsConnectedSkew χ.D ∧ 2 ≤ χ.D.card ∧ 2 ≤ χ.ω.E.card ∧ χ.ω.IsReadoutLegal

/-- Proper ordinary charts at the supplied period. -/
def IsProperOrdinary (χ : Chart) : Prop :=
  χ.IsProperReadoutLegal ∧ χ.ω.IsOrdinary

end Gluing.Chart
end SkewMarkedFactor
