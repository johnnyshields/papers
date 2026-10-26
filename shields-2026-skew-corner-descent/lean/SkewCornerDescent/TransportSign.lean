/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.NormalizedTransport
import SkewGluing.SignedCornerTransport

/-!
# The coefficient-transport sign convention

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:coefficient-transport`).

The source, row-image, and parent cofactor orientations combine into the single displayed
sign. The interior image is the product of the actual connected-component images.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- The actual interior function's algebra-map image is its full component-image product. -/
theorem IsLegal.modifiedCompositionMap_interior_product (h : ω.IsLegal)
    {D : Diagram} (hD : IsSkew D) :
    ω.modifiedCompositionMap h (cellSchur (diagramInterior D) hD.interior) =
      ∏ C ∈ (edgeComponents (diagramInterior D)).attach,
        ω.modifiedCompositionMap h (cellSchur C.1
          (isConnectedSkew_component hD.interior C.2).1) := by
  conv_lhs => unfold cellSchur
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro C _
  exact congrArg (ω.modifiedCompositionMap h)
    (cellSchur_eq_connected (isConnectedSkew_component hD.interior C.2)).symm

/-- All three orientation factors reduce to the single sign in coefficient transport. -/
theorem IsLegal.coefficient_transport_signed (h : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (M L : ℕ+) (hM : (M : ℕ) = span D)
    (hL : (L : ℤ) = (M : ℤ) * ω.period + ω.width) :
    ∃ sign : ℕ,
      ω.compositionPrefactor h D *
        cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior =
      (-1 : Lambda) ^ sign *
        (ω.normalA h ^ ((M : ℕ) - 1) * ω.normalTheta h *
          ω.normalC h ^ (M : ℕ) * ω.normalB h ^ ((M : ℕ) - 1) *
          ∏ C ∈ (edgeComponents (diagramInterior D)).attach,
            ω.modifiedCompositionMap h (cellSchur C.1
              (isConnectedSkew_component hD.1.interior C.2).1)) := by
  obtain ⟨s, hs⟩ := h.normalized_cofactor_transport hD M L hM hL
  rw [h.modifiedCompositionMap_interior_product hD.1] at hs
  let p := s + (((ω.compose D).image Prod.fst).card - 1)
  let q := ((D.image Prod.fst).card - 1) +
    (((ω.compose (horizontalRow M)).image Prod.fst).card - 1)
  let f := ω.compositionPrefactor h D *
    cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior
  let g := ω.normalA h ^ ((M : ℕ) - 1) * ω.normalTheta h *
    ω.normalC h ^ (M : ℕ) * ω.normalB h ^ ((M : ℕ) - 1) *
    ∏ C ∈ (edgeComponents (diagramInterior D)).attach,
      ω.modifiedCompositionMap h (cellSchur C.1
        (isConnectedSkew_component hD.1.interior C.2).1)
  have he : (-1 : Lambda) ^ p * f = (-1) ^ q * g := by
    dsimp [p, q, f, g, compositionPrefactor]
    simp only [pow_add]
    calc
      _ = _ := by ring
      _ = _ := hs
      _ = _ := by ring
  refine ⟨p + q, ?_⟩
  change f = (-1 : Lambda) ^ (p + q) * g
  calc
    f = (-1 : Lambda) ^ p * ((-1) ^ p * f) := by
      rw [← mul_assoc, ← pow_two, sign_pow_sq]
      simp
    _ = (-1 : Lambda) ^ p * ((-1) ^ q * g) := by rw [he]
    _ = _ := by rw [pow_add]; ring

end SkewGluing.MarkedInner
