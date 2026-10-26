/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.ChartBridge
import GluingCore.OlsonHarris.Frontier

/-!
# Line fibers cannot give distinct source-minimal periods

Formalizes the line-inner exclusion in `shields-2026-skew-corner-descent.tex`,
«Period comparison and polynomial obstructions» (`sec:periods`, `thm:descent`).
The cited full-class line transport and fiber domination are supplied by proved declarations,
including the unconditional Olson-Harris composition theorem.

Sorry-free.
-/

namespace GluingCore

/-- A fiber member carries a proper chart with the same score and period. -/
theorem Chart.IsProperLegal.chart_of_fiber_member {χ : Chart} (hχ : χ.IsProperLegal)
    {F : Diagram} (hF : F ∈ fiberClass cellSchur χ.ω (cellSchur χ.D)) :
    ∃ δ : Chart, δ.IsProperLegal ∧ δ.IsChartOf F ∧ δ.score = χ.score ∧ δ.period = χ.period := by
  obtain ⟨F', ⟨A, hA, hcard, _, hF'⟩, t, rfl⟩ := hF
  rcases hF' with rfl | rfl
  · exact ⟨⟨A, χ.ω⟩, ⟨hA, hcard, hχ.2.2.1, hχ.2.2.2⟩, ⟨t, rfl⟩, rfl, rfl⟩
  · refine ⟨⟨A, χ.ω.rotate⟩, ⟨hA, hcard, ?_, MarkedInner.isLegal_rotate hχ.2.2.2⟩,
      ⟨t, rfl⟩, ?_, MarkedInner.period_rotate _⟩
    · change 2 ≤ (GluingCore.rotate χ.ω.E).card
      rw [GluingCore.rotate, Finset.card_image_of_injective _ neg_injective]
      exact hχ.2.2.1
    · simp only [Chart.score, MarkedInner.width_rotate, MarkedInner.rotate_E, span_rotate]

/-- Source-minimal periods agree across Schur equality if either supplied inner is a line. -/
theorem Chart.IsSourceMinimal.period_eq_of_line {χ ψ : Chart}
    (hχ : χ.IsSourceMinimal χ.parent) (hψ : ψ.IsSourceMinimal ψ.parent)
    (hs : cellSchur χ.parent = cellSchur ψ.parent) (hl : LineInner χ.ω) :
    χ.period = ψ.period := by
  have hH := hψ.1.2.2.2.isConnectedSkew_compose hψ.1.1
  obtain ⟨ζ, hζ, hω, hD, cζ⟩ := hχ.1.exists_chart_of_line hl hH.1 hs.symm
  have hHmem : ψ.parent ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
    have hm := hζ.mem_fiberClass_parent cζ
    rwa [hω, hD] at hm
  have hFmem : χ.parent ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) :=
    hχ.1.mem_fiberClass_parent hχ.2.1
  have hFψ := hψ.fiberClass_subset olsonHarrisComposition hχ.1.2.2.2 hχ.1.2.2.1 hHmem hFmem
  obtain ⟨δ, hδ, cδ, hscore, hperiod⟩ := hψ.1.chart_of_fiber_member hFψ
  have hle := hχ.2.2 δ hδ cδ
  rw [hscore] at hle
  have hle' := hψ.2.2 ζ hζ cζ
  have hscoreζ : ζ.score = χ.score := by simp only [Chart.score, hω]
  rw [hscoreζ] at hle'
  have he : χ.score = ψ.score := le_antisymm hle hle'
  have hperiod' := hχ.1.period_eq_of_score_eq hδ hχ.2.1 cδ (he.trans hscore.symm)
  exact hperiod'.trans hperiod

end GluingCore
