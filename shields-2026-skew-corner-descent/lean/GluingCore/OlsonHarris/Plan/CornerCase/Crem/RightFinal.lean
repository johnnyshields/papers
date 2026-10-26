-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/CornerCase/Crem/RightFinal.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.RightSep
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.RightCount
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.Components

/-!
# The remainder after removing the lift of a ribbon removable on the right

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), the clause for ribbons removable on the right.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

theorem right_remainder {ω : MarkedInner} (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) {D : Diagram} (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m)
    {A : Diagram} (hA : A ∈ rightRibbons D m) :
    cellSchur (ω.compose D \ cornerLift ω D m s A) =
      cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
        cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
          cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) * compSchur ω (D \ A) := by
  obtain ⟨j0, rfl, hw⟩ := RightWindow.of_mem hD hm hA
  rw [cellSchur_right_remainder h hc hph hw, cellSchur_Fp h hc hw.isSkew_X, card_rLone hw,
    card_rLoneW hw, card_rLoneN hw]
  ring

end Rem

end Corner

end Plan

end GluingCore
