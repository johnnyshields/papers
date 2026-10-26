/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.RowGeneratorBridge

/-!
# The geometric modified composition identity

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner transport»
(`eq:homomorphism`).  The map specified on complete generators agrees with actual
four-case composition on every connected skew outer.  The Schur-relation kernel
and the generator seam are proved, not additional hypotheses.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
variable {ω : MarkedInner}

/-- Actual composition is connected skew for every legal mark. -/
theorem IsLegal.connected_compose (h : ω.IsLegal) {D : Diagram} (hD : IsConnectedSkew D) :
    IsConnectedSkew (ω.compose D) := by
  have hD' : GluingCore.IsConnectedSkew D := hD
  have hc := GluingCore.MarkedInner.IsLegal.isConnectedSkew_compose h.toGluing hD'
  rw [toGluing_compose] at hc
  exact hc

/-- The certified component normalization is the actual paper normalization. -/
theorem IsLegal.componentT_eq (h : ω.IsLegal) {D : Diagram} (hD : IsConnectedSkew D) :
    GluingCore.Plan.componentT ω.toGluing D =
      ω.normalA h ^ (D.card - (D.image Prod.fst).card) *
      ω.normalB h ^ (D.card - (D.image Prod.snd).card) *
      ω.normalC h ^ (D.card - span D) *
      cellSchur (ω.compose D) (h.connected_compose hD).1 := by
  unfold GluingCore.Plan.componentT
  rw [← h.normalA_eq_gluing, ← h.normalB_eq_gluing, ← h.normalC_eq_gluing,
    toGluing_compose, ← cellSchur_eq_gluing _ (h.connected_compose hD).1,
    GluingCore.numCols_eq_card_image_snd]
  rfl

/-- The complete-generator algebra map realizes four-case geometric composition. -/
theorem IsLegal.modifiedCompositionMap_cellSchur (h : ω.IsLegal)
    {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ sign : ℕ, ω.modifiedCompositionMap h (cellSchur D hD.1) =
      (-1 : Lambda) ^ sign *
      (ω.normalA h ^ (D.card - (D.image Prod.fst).card) *
       ω.normalB h ^ (D.card - (D.image Prod.snd).card) *
       ω.normalC h ^ (D.card - span D) *
       cellSchur (ω.compose D) (h.connected_compose hD).1) := by
  obtain ⟨φ, hφ, hrow⟩ := GluingCore.Plan.exists_legalComposition_algHom h.toGluing
  have he := h.algHom_eq_modifiedCompositionMap φ (fun j => hrow (horizontalRow j)
    (show GluingCore.IsConnectedSkew (horizontalRow j) from isConnectedSkew_horizontalRow j.pos)
    0 (fun x hx => (mem_horizontalRow.mp hx).1))
  obtain ⟨sign, hs⟩ := hφ D (show GluingCore.IsConnectedSkew D from hD)
  refine ⟨sign, ?_⟩
  rw [he, ← cellSchur_eq_gluing D hD.1, h.componentT_eq hD] at hs
  exact hs

/-- Ordinary attachments have positive orientation for every connected outer. -/
theorem IsLegal.modifiedCompositionMap_cellSchur_ordinary (h : ω.IsLegal)
    (hc : ω.case = .a ∨ ω.case = .b) {D : Diagram} (hD : IsConnectedSkew D) :
    ω.modifiedCompositionMap h (cellSchur D hD.1) =
      ω.normalA h ^ (D.card - (D.image Prod.fst).card) *
      ω.normalB h ^ (D.card - (D.image Prod.snd).card) *
      ω.normalC h ^ (D.card - span D) *
      cellSchur (ω.compose D) (h.connected_compose hD).1 := by
  have hc' : ω.toGluing.case = .a ∨ ω.toGluing.case = .b := by
    rcases hc with ha | hb
    · left; simp only [MarkedInner.toGluing, ha, AttachCase.toGluing]
    · right; simp only [MarkedInner.toGluing, hb, AttachCase.toGluing]
  obtain ⟨φ, hφ⟩ := GluingCore.Plan.exists_ordinaryComposition_algHom h.toGluing hc'
  have hvalue : ∀ X : Diagram, IsConnectedSkew X →
      φ (GluingCore.cellSchur X) = GluingCore.Plan.componentT ω.toGluing X := by
    intro X hX
    simpa only [GluingCore.Plan.modComp_connected hX] using hφ X hX.1
  have he := h.algHom_eq_modifiedCompositionMap φ (fun j => hvalue (horizontalRow j)
    (isConnectedSkew_horizontalRow j.pos))
  have hs := hvalue D hD
  rw [he, ← cellSchur_eq_gluing D hD.1, h.componentT_eq hD] at hs
  exact hs

end SkewGluing.MarkedInner
