/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.LinePeriod

/-!
# Cofactor descent in the actual source-minimal chart API

Supports `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `thm:descent`, `prop:beta-reduction`).
Each statement transfers through proved cell-set and Schur-function bridges.

Sorry-free.
-/

namespace GluingCore
open SkewCornerDescent.Matrix

/-- Equal actual connected functions have equal corner cofactors in the total API. -/
theorem interior_cellSchur_eq_of_eq {D E : Diagram} (hD : IsConnectedSkew D)
    (hE : IsConnectedSkew E) (hs : cellSchur D = cellSchur E) :
    cellSchur (SkewGluing.diagramInterior D) = cellSchur (SkewGluing.diagramInterior E) := by
  have hs' : SkewGluing.cellSchur D hD.1 = SkewGluing.cellSchur E hE.1 := by
    rw [SkewGluing.cellSchur_eq_gluing D hD.1, SkewGluing.cellSchur_eq_gluing E hE.1]
    exact hs
  simpa only [SkewGluing.cellSchur_eq_gluing] using
    SkewGluing.interiorSchur_eq_of_cellSchur_eq hD hE hs'

/-- Rational associates of actual skew Schur functions are equal in the total API. -/
theorem cellSchur_eq_of_associated {D E : Diagram} (hD : IsSkew D) (hE : IsSkew E)
    (hs : Associated (cellSchur D) (cellSchur E)) : cellSchur D = cellSchur E := by
  have hs' : Associated (SkewGluing.cellSchur D hD) (SkewGluing.cellSchur E hE) := by
    rw [SkewGluing.cellSchur_eq_gluing D hD, SkewGluing.cellSchur_eq_gluing E hE]
    exact hs
  have he := SkewGluing.cellSchur_eq_of_associated hD hE hs'
  rw [SkewGluing.cellSchur_eq_gluing D hD, SkewGluing.cellSchur_eq_gluing E hE] at he
  exact he

/-- Every actual child is an irreducible divisor of the actual parent's cofactor. -/
theorem Chart.IsProperLegal.child_factor {χ : Chart} (hχ : χ.IsProperLegal) {C : Diagram}
    (hC : C ∈ edgeComponents (SkewGluing.diagramInterior χ.D)) :
    Irreducible (cellSchur (χ.ω.compose C)) ∧
      cellSchur (χ.ω.compose C) ∣ cellSchur (SkewGluing.diagramInterior χ.parent) := by
  have hi := hχ.2.2.2.toCorner.irreducible_child hχ.1 hC
  have hd := hχ.2.2.2.toCorner.child_dvd_cofactor hχ.1 hχ.2.1 hC
  rw [SkewGluing.cellSchur_eq_gluing] at hi hd
  rw [SkewGluing.cellSchur_eq_gluing] at hd
  rw [MarkedInner.toCorner_compose] at hi
  rw [MarkedInner.toCorner_compose, MarkedInner.toCorner_compose] at hd
  exact And.intro hi hd

/-- High-span irreducible divisors are actual child functions, with no scalar ambiguity. -/
theorem Chart.IsProperLegal.highSpan_child {χ : Chart} (hχ : χ.IsProperLegal)
    {G : Diagram} (hG : IsConnectedSkew G)
    (hs : χ.period ≤ (span G : ℤ))
    (hd : cellSchur G ∣ cellSchur (SkewGluing.diagramInterior χ.parent)) :
    ∃ C : Diagram, C ∈ edgeComponents (SkewGluing.diagramInterior χ.D) ∧
      cellSchur G = cellSchur (χ.ω.compose C) := by
  have hG' : SkewGluing.IsConnectedSkew G := hG
  have hD' : SkewGluing.IsConnectedSkew χ.D := hχ.1
  have hf : Irreducible (SkewGluing.cellSchur G hG'.1) := by
    simpa only [SkewGluing.map_integralCellSchur] using
      SkewGluing.irreducible_integralCellSchur (K := ℚ) hG'
  have hsp : χ.ω.toCorner.period ≤
      (polynomialSpan (SkewGluing.cellSchur G hG'.1) : ℤ) := by
    rw [SkewGluing.polynomialSpan_cellSchur hG']
    exact hs
  have hd' : SkewGluing.cellSchur G hG'.1 ∣
      SkewGluing.cellSchur (SkewGluing.diagramInterior (χ.ω.toCorner.compose χ.D))
        (hχ.2.2.2.toCorner.connected_compose hD').1.interior := by
    rw [SkewGluing.cellSchur_eq_gluing G hG'.1, SkewGluing.cellSchur_eq_gluing,
      MarkedInner.toCorner_compose]
    exact hd
  obtain ⟨C, he⟩ := hχ.2.2.2.toCorner.highSpan_factor_is_child hD' hχ.2.1 hf hsp hd'
  refine ⟨C.1, C.2, ?_⟩
  have hg := SkewGluing.cellSchur_eq_of_associated hG'.1
    (hχ.2.2.2.toCorner.connected_compose
      (SkewGluing.isConnectedSkew_component hD'.1.interior C.2)).1 he
  rw [SkewGluing.cellSchur_eq_gluing G hG'.1, SkewGluing.cellSchur_eq_gluing,
    MarkedInner.toCorner_compose] at hg
  exact hg

/-- The actual child span loses at least two full periods. -/
theorem Chart.IsProperLegal.child_span_descent {χ : Chart} (hχ : χ.IsProperLegal) {C : Diagram}
    (hC : C ∈ edgeComponents (SkewGluing.diagramInterior χ.D)) :
    (span (χ.ω.compose C) : ℤ) ≤ (span χ.parent : ℤ) - 2 * χ.period := by
  have he := hχ.2.2.2.toCorner.child_span_descent hχ.1 hχ.2.1 hC
  rw [MarkedInner.toCorner_compose, MarkedInner.toCorner_compose] at he
  exact he

end GluingCore
