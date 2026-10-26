/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.CornerTransport

/-!
# Descent of actual composed interior children

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `cor:proper-child`, `eq:child-descent`).  Every child divides the
actual cofactor.  Its content span loses at least two periods, and weighted-degree
comparison makes its cell count strictly smaller than the parent composition.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
open SkewCornerDescent.Matrix
variable {ω : MarkedInner}

/-- Every displayed actual child function divides the cofactor. -/
theorem IsLegal.child_dvd_cofactor (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card)
    (hC : C ∈ edgeComponents (diagramInterior D)) :
    cellSchur (ω.compose C) (h.connected_compose (isConnectedSkew_component hD.1.interior hC)).1 ∣
      cellSchur (diagramInterior (ω.compose D)) (h.connected_compose hD).1.interior := by
  rw [h.corner_transport hD hcard]
  apply dvd_mul_of_dvd_right
  unfold childProduct
  exact Finset.dvd_prod_of_mem
    (a := ⟨C, hC⟩) (s := (edgeComponents (diagramInterior D)).attach)
    (fun C : {C // C ∈ edgeComponents (diagramInterior D)} =>
      cellSchur (ω.compose C.1)
        (h.connected_compose (isConnectedSkew_component hD.1.interior C.2)).1)
    (Finset.mem_attach _ ⟨C, hC⟩)

/-- Every child span is smaller than the parent span by at least two periods. -/
theorem IsLegal.child_span_descent (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card)
    (hC : C ∈ edgeComponents (diagramInterior D)) :
    (span (ω.compose C) : ℤ) ≤ (span (ω.compose D) : ℤ) - 2 * ω.period := by
  have hc := isConnectedSkew_component hD.1.interior hC
  have hsub : span C ≤ span (diagramInterior D) :=
    Finset.card_le_card (Finset.image_subset_image (component_subset hC))
  have hb := interior_span_le_of_two_le_card hD hcard
  have hp : 0 ≤ ω.period := by have := h.2.2.1.2; omega
  have hm := mul_le_mul_of_nonneg_right (show (span C : ℤ) ≤ (span D : ℤ) - 2 by
    have hz : (span C : ℤ) ≤ span (diagramInterior D) := by exact_mod_cast hsub
    omega) hp
  rw [span_compose hc h, span_compose hD h]
  nlinarith

/-- Child area cannot exceed the area of the parent's southeast interior. -/
theorem IsLegal.child_card_le_interior (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card)
    (hC : C ∈ edgeComponents (diagramInterior D)) :
    (ω.compose C).card ≤ (diagramInterior (ω.compose D)).card := by
  have hF := h.connected_compose hD
  have hG := h.connected_compose (isConnectedSkew_component hD.1.interior hC)
  by_contra hn
  have hlt : (diagramInterior (ω.compose D)).card < (ω.compose C).card := by omega
  have hhomF := GluingCore.isWeightedHomogeneous_cellSchur
    (show GluingCore.IsSkew (diagramInterior (ω.compose D)) from hF.1.interior)
  have hhomG := GluingCore.isWeightedHomogeneous_cellSchur
    (show GluingCore.IsSkew (ω.compose C) from hG.1)
  have hnot := GluingCore.not_dvd_of_weightedDegree_lt hhomF hhomG hlt
    (GluingCore.Plan.MarkFacts.cellSchur_ne_zero (show GluingCore.IsSkew _ from hF.1.interior))
  apply hnot
  simpa only [cellSchur_eq_gluing] using h.child_dvd_cofactor hD hcard hC

/-- Every displayed child has strictly fewer cells than the parent composition. -/
theorem IsLegal.child_card_descent (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hcard : 2 ≤ D.card)
    (hC : C ∈ edgeComponents (diagramInterior D)) :
    (ω.compose C).card < (ω.compose D).card := by
  have hF := h.connected_compose hD
  have ha := card_eq_span_add_interior hF.1
  have hs : 0 < span (ω.compose D) := Finset.card_pos.mpr (hF.2.1.image content)
  have hc := h.child_card_le_interior hD hcard hC
  omega

/-- A one-cell composition is a translate of the inner, in every attachment case. -/
theorem compose_singleton (ω : MarkedInner) (x : ℤ × ℤ) :
    ω.compose {x} = translate (ω.origin {x} x) ω.E := by
  have hn : ¬ ω.SameRibbon {x} x := by
    intro hh
    have he := Finset.mem_singleton.mp hh.1
    have hf := congrArg Prod.fst he
    omega
  simp [compose, hn]

/-- The child factor of a one-cell outer is exactly the inner function. -/
theorem IsLegal.cellSchur_compose_singleton (h : ω.IsLegal) (x : ℤ × ℤ)
    (hC : IsConnectedSkew ({x} : Diagram)) :
    cellSchur (ω.compose {x}) (h.connected_compose hC).1 = cellSchur ω.E h.1.1.1 := by
  have he := ω.compose_singleton x
  exact (cellSchur_congr he _ (isSkew_translate _ h.1.1.1)).trans
    (cellSchur_translate _ _ _)

/-- Every child at the minimum transported span is the single inner factor. -/
theorem IsLegal.child_at_minimum_span (h : ω.IsLegal) {D C : Diagram}
    (hD : IsConnectedSkew D) (hC : C ∈ edgeComponents (diagramInterior D))
    (hspan : (span (ω.compose C) : ℤ) = ω.period + ω.width) :
    cellSchur (ω.compose C) (h.connected_compose (isConnectedSkew_component hD.1.interior hC)).1 =
      cellSchur ω.E h.1.1.1 := by
  have hc := isConnectedSkew_component hD.1.interior hC
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have he := span_compose hc h
  have hsp : span C = 1 := by nlinarith
  have hcard : C.card = 1 := by
    have hpos := Finset.card_pos.mpr hc.2.1
    by_contra hn
    have hh := two_le_span_of_two_le_card hc (show 2 ≤ C.card by omega)
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  subst C
  exact h.cellSchur_compose_singleton x hc

end SkewGluing.MarkedInner
