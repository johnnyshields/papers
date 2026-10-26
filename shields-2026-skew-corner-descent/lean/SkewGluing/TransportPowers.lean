/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.CompositionProductBookkeeping

/-!
# Transport exponent cancellation

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:transport`).  Natural-number subtraction is justified by the
actual area and interior-component inequalities before combining polynomial powers.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
variable {ω : MarkedInner}

/-- The prefactors before cancellation differ by exactly the three displayed transport powers. -/
theorem IsLegal.transport_power_identity (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card) :
    ω.compositionPrefactor h D *
      (ω.normalTheta h *
        ω.normalA h ^ ((D.image Prod.fst).card - 1 - ((diagramInterior D).image Prod.fst).card) *
        ω.normalB h ^ ((D.image Prod.snd).card - 1 - ((diagramInterior D).image Prod.snd).card) *
        ω.normalC h ^ (span D - span (diagramInterior D))) =
      ω.normalA h ^ (span D - 1) * ω.normalTheta h * ω.normalC h ^ span D *
        ω.normalB h ^ (span D - 1) * ω.compositionPrefactor h (diagramInterior D) := by
  have ha := card_eq_span_add_interior hD.1
  have hr := interior_component_rows_le hD
  have hc := interior_component_cols_le hD
  have hs := interior_component_spans_le hD hcard
  rw [sum_component_rows hD.1.interior] at hr
  rw [sum_component_cols hD.1.interior] at hc
  rw [sum_component_spans hD.1.interior] at hs
  have hrD : (D.image Prod.fst).card ≤ D.card := Finset.card_image_le
  have hcD : (D.image Prod.snd).card ≤ D.card := Finset.card_image_le
  have hrI : ((diagramInterior D).image Prod.fst).card ≤ (diagramInterior D).card :=
    Finset.card_image_le
  have hcI : ((diagramInterior D).image Prod.snd).card ≤ (diagramInterior D).card :=
    Finset.card_image_le
  have hsI : span (diagramInterior D) ≤ (diagramInterior D).card := Finset.card_image_le
  have ea : (D.card - (D.image Prod.fst).card) +
      ((D.image Prod.fst).card - 1 - ((diagramInterior D).image Prod.fst).card) =
      (span D - 1) + ((diagramInterior D).card - ((diagramInterior D).image Prod.fst).card) := by
    omega
  have eb : (D.card - (D.image Prod.snd).card) +
      ((D.image Prod.snd).card - 1 - ((diagramInterior D).image Prod.snd).card) =
      (span D - 1) + ((diagramInterior D).card - ((diagramInterior D).image Prod.snd).card) := by
    omega
  have ec : (D.card - span D) + (span D - span (diagramInterior D)) =
      span D + ((diagramInterior D).card - span (diagramInterior D)) := by omega
  unfold compositionPrefactor
  calc
    _ = ω.normalTheta h *
        (ω.normalA h ^ ((D.card - (D.image Prod.fst).card) +
          ((D.image Prod.fst).card - 1 - ((diagramInterior D).image Prod.fst).card))) *
        (ω.normalB h ^ ((D.card - (D.image Prod.snd).card) +
          ((D.image Prod.snd).card - 1 - ((diagramInterior D).image Prod.snd).card))) *
        (ω.normalC h ^ ((D.card - span D) + (span D - span (diagramInterior D)))) := by
      simp only [pow_add]
      ring
    _ = _ := by
      rw [ea, eb, ec]
      simp only [pow_add]
      ring

end SkewGluing.MarkedInner
