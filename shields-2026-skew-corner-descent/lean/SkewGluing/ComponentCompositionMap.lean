/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.NormalizedTransport

/-!
# Composition on the interior component product

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:coefficient-transport`).  Multiplicativity and the connected
geometric identity supply every interior component factor, including one-cell factors.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
variable {ω : MarkedInner}

/-- The geometric scalar multiplying a connected outer's composition function. -/
noncomputable def compositionPrefactor (ω : MarkedInner) (h : ω.IsLegal) (D : Diagram) : Lambda :=
  ω.normalA h ^ (D.card - (D.image Prod.fst).card) *
  ω.normalB h ^ (D.card - (D.image Prod.snd).card) *
  ω.normalC h ^ (D.card - span D)

/-- The actual algebra map acts on all components of a skew diagram by the geometric formula. -/
theorem IsLegal.modifiedCompositionMap_components (h : ω.IsLegal) {D : Diagram}
    (hD : IsSkew D) :
    ∃ sign : ℕ, ω.modifiedCompositionMap h (cellSchur D hD) = (-1 : Lambda) ^ sign *
      ∏ C ∈ (edgeComponents D).attach,
        (ω.compositionPrefactor h C.1 *
          cellSchur (ω.compose C.1) (h.connected_compose (isConnectedSkew_component hD C.2)).1) := by
  classical
  let cs := (edgeComponents D).attach
  have hh (C : {C // C ∈ edgeComponents D}) :
      ∃ sign : ℕ, ω.modifiedCompositionMap h (connectedSchur C.1
        (isConnectedSkew_component hD C.2)) = (-1 : Lambda) ^ sign *
        (ω.compositionPrefactor h C.1 *
          cellSchur (ω.compose C.1) (h.connected_compose (isConnectedSkew_component hD C.2)).1) := by
    simpa only [cellSchur_eq_connected (isConnectedSkew_component hD C.2),
      compositionPrefactor] using
      h.modifiedCompositionMap_cellSchur (isConnectedSkew_component hD C.2)
  choose s hs using hh
  refine ⟨∑ C ∈ cs, s C, ?_⟩
  unfold cellSchur
  rw [map_prod]
  simp_rw [hs]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

end SkewGluing.MarkedInner
