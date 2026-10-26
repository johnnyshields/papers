/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.ComponentCompositionMap

/-!
# Component normalization bookkeeping

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:coefficient-transport`).  Component areas and coordinate counts
add exactly, so the product of geometric prefactors is the prefactor of their union.

Sorry-free.
-/

namespace SkewGluing

/-- Erosion removes one cell from each occupied content diagonal of a skew diagram. -/
theorem card_eq_span_add_interior {D : Diagram} (hD : IsSkew D) :
    D.card = span D + (diagramInterior D).card :=
  GluingCore.Plan.card_eq_span_add_countSE (show GluingCore.IsSkew D from hD)

namespace MarkedInner
variable {ω : MarkedInner}

/-- Multiplying component prefactors adds their three actual exponents. -/
theorem IsLegal.prod_compositionPrefactor (h : ω.IsLegal) {D : Diagram} (hD : IsSkew D) :
    (∏ C ∈ (edgeComponents D).attach, ω.compositionPrefactor h C.1) =
      ω.compositionPrefactor h D := by
  classical
  have hcard : (∑ C ∈ edgeComponents D, C.card) = D.card :=
    (GluingCore.card_eq_sum_edgeComponents (D := D)).symm
  have hr : (∑ C ∈ edgeComponents D, (C.card - (C.image Prod.fst).card)) =
      D.card - (D.image Prod.fst).card := by
    rw [Finset.sum_tsub_distrib _ (fun C _ => Finset.card_image_le), hcard,
      sum_component_rows hD]
  have hc : (∑ C ∈ edgeComponents D, (C.card - (C.image Prod.snd).card)) =
      D.card - (D.image Prod.snd).card := by
    rw [Finset.sum_tsub_distrib _ (fun C _ => Finset.card_image_le), hcard,
      sum_component_cols hD]
  have hs : (∑ C ∈ edgeComponents D, (C.card - span C)) = D.card - span D := by
    rw [Finset.sum_tsub_distrib _ (fun C _ => (show span C ≤ C.card from Finset.card_image_le)),
      hcard,
      sum_component_spans hD]
  unfold compositionPrefactor
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_attach (edgeComponents D) (fun C => C.card - (C.image Prod.fst).card),
    Finset.sum_attach (edgeComponents D) (fun C => C.card - (C.image Prod.snd).card),
    Finset.sum_attach (edgeComponents D) (fun C => C.card - span C), hr, hc, hs]

/-- Every skew outer has the actual componentwise composition image with the aggregate normalization. -/
theorem IsLegal.modifiedCompositionMap_component_product (h : ω.IsLegal) {D : Diagram}
    (hD : IsSkew D) :
    ∃ sign : ℕ, ω.modifiedCompositionMap h (cellSchur D hD) =
      (-1 : Lambda) ^ sign * (ω.compositionPrefactor h D *
        ∏ C ∈ (edgeComponents D).attach,
          cellSchur (ω.compose C.1) (h.connected_compose (isConnectedSkew_component hD C.2)).1) := by
  obtain ⟨sign, hs⟩ := h.modifiedCompositionMap_components hD
  refine ⟨sign, ?_⟩
  rw [Finset.prod_mul_distrib, h.prod_compositionPrefactor hD] at hs
  exact hs

end MarkedInner
end SkewGluing
