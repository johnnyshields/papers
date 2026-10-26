/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.PositiveSpecialization

/-!
# Geometric corner cofactor transport

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `thm:transport`, `eq:transport`).  The actual cofactor equals the
finite-cap normalization times the actual composed interior-component functions.
Positivity eliminates the sign left by coefficient extraction and cancellation.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
variable {ω : MarkedInner}

/-- The corner-transport product formula for every proper connected legal outer. -/
theorem IsLegal.corner_transport (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) :
    cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior =
      ω.transportScalar h D * ω.childProduct h D hD.1 := by
  have hm : 0 < span D := by
    have := two_le_span_of_two_le_card hD hcard
    omega
  have hF := h.connected_compose hD
  have hl : 0 < span (ω.compose D) :=
    Finset.card_pos.mpr (hF.2.1.image content)
  let M : ℕ+ := ⟨span D, hm⟩
  let L : ℕ+ := ⟨span (ω.compose D), hl⟩
  have hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width := span_compose hD h
  exact (h.corner_transport_signed hD hcard M L rfl hL).resolve_right
    ((positiveAtOnes_cellSchur hF.1.interior).ne_neg (h.positiveAtOnes_transport hD.1))

/-- All three transport powers are justified, with a strict two-content loss. -/
theorem IsLegal.corner_transport_exponents {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) :
    ((diagramInterior D).image Prod.fst).card + 1 ≤ (D.image Prod.fst).card ∧
      ((diagramInterior D).image Prod.snd).card + 1 ≤ (D.image Prod.snd).card ∧
      span (diagramInterior D) + 2 ≤ span D := by
  have hb := interior_component_bounds hD hcard
  simpa only [sum_component_rows hD.1.interior, sum_component_cols hD.1.interior,
    sum_component_spans hD.1.interior] using hb

end SkewGluing.MarkedInner
