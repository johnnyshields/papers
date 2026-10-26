import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.LeftSep
import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.LeftCount
import SkewGluing.OlsonHarris.Plan.CornerCase.Crem.Components

/-!
# The remainder after removing the lift of a ribbon removable on the left

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), the clause for ribbons removable on the left.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

theorem left_remainder {ω : MarkedInner} (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hph : ω.IsPhases s t) {D : Diagram} (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m)
    {A : Diagram} (hA : A ∈ leftRibbons D m) :
    cellSchur (ω.compose D \ cornerLift ω D m t A) =
      cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
        cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
          cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) * compSchur ω (D \ A) := by
  obtain ⟨j0, rfl, hw⟩ := LeftWindow.of_mem hD hm hA
  rw [cellSchur_left_remainder h hc hph hw, cellSchur_Fp h hc hw.isSkew_X, card_rLone_L hw,
    card_lLoneE hw, card_lLoneS hw]
  ring

end Rem

end Corner

end Plan

end SkewGluing
