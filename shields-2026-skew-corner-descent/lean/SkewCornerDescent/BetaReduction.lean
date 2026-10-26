/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.PeriodDescent

/-!
# Nonempty discrete-interior reduction

Formalizes `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `prop:beta-reduction`).
The extracted child is an actual composition; equality with the supplied inner
is an equality of functions, not a claimed chart on that literal inner.

Sorry-free.
-/

namespace GluingCore

/-- A connected singleton outer has the inner's actual Schur function. -/
theorem MarkedInner.IsLegal.cellSchur_singleton {ω : MarkedInner} (h : ω.IsLegal)
    (x : ℤ × ℤ) (hx : IsConnectedSkew ({x} : Diagram)) :
    cellSchur (ω.compose {x}) = cellSchur ω.E := by
  have he := h.toCorner.cellSchur_compose_singleton x hx
  rw [SkewGluing.cellSchur_eq_gluing, SkewGluing.cellSchur_eq_gluing,
    MarkedInner.toCorner_compose] at he
  exact he

/-- Actual geometric child area strictly decreases from the parent. -/
theorem Chart.IsProperLegal.child_card_descent {χ : Chart} (hχ : χ.IsProperLegal)
    {C : Diagram} (hC : C ∈ edgeComponents (SkewGluing.diagramInterior χ.D)) :
    (χ.ω.compose C).card < χ.parent.card := by
  have he := hχ.2.2.2.toCorner.child_card_descent hχ.1 hχ.2.1 hC
  rw [MarkedInner.toCorner_compose, MarkedInner.toCorner_compose] at he
  exact he

/-- The nonempty discrete residual yields the exact inner function and all child alternatives. -/
theorem Chart.IsSourceMinimal.beta_reduction {χ ψ : Chart}
    (hχ : χ.IsSourceMinimal χ.parent) (hψ : ψ.IsSourceMinimal ψ.parent)
    (hs : cellSchur χ.parent = cellSchur ψ.parent) (hlt : ψ.period < χ.period)
    (hnl : ¬ LineInner ψ.ω) (hd : SkewGluing.HasDiscreteInterior χ.D)
    (hne : (SkewGluing.diagramInterior χ.D).Nonempty) :
    ∃ V : Diagram, V ∈ edgeComponents (SkewGluing.diagramInterior ψ.D) ∧
      IsConnectedSkew V ∧ cellSchur χ.ω.E = cellSchur (ψ.ω.compose V) ∧
      χ.period + χ.ω.width = (span V : ℤ) * ψ.period + ψ.ω.width ∧
      ((span V = 1 → cellSchur χ.ω.E = cellSchur ψ.ω.E ∧
          ψ.period < χ.period ∧ χ.period < 2 * ψ.period) ∧
        (2 ≤ span V → (⟨V, ψ.ω⟩ : Chart).IsSourceMinimal (ψ.ω.compose V) ∧
          (ψ.ω.compose V).card = χ.ω.E.card ∧ χ.ω.E.card < χ.parent.card)) := by
  classical
  obtain ⟨x, hx⟩ := hne
  let S := (SkewGluing.diagramInterior χ.D).filter
    fun y => DiagReach (SkewGluing.diagramInterior χ.D) x y
  have hS : S ∈ edgeComponents (SkewGluing.diagramInterior χ.D) :=
    mem_edgeComponents.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hd S hS)
  have hD : SkewGluing.IsConnectedSkew χ.D := hχ.1.1
  have hSc : IsConnectedSkew S := SkewGluing.isConnectedSkew_component hD.1.interior hS
  have he : cellSchur (χ.ω.compose S) = cellSchur χ.ω.E := by
    rw [hy]
    exact hχ.1.2.2.2.cellSchur_singleton y (hy ▸ hSc)
  have hdiv := (hχ.1.child_factor hS).2
  rw [he] at hdiv
  have hc := interior_cellSchur_eq_of_eq
    (hχ.1.2.2.2.isConnectedSkew_compose hχ.1.1)
    (hψ.1.2.2.2.isConnectedSkew_compose hψ.1.1) hs
  change cellSchur (SkewGluing.diagramInterior χ.parent) =
    cellSchur (SkewGluing.diagramInterior ψ.parent) at hc
  rw [hc] at hdiv
  have hE : IsConnectedSkew χ.ω.E := hχ.1.2.2.2.1.1
  have hEsp : (span χ.ω.E : ℤ) = χ.period + χ.ω.width := hχ.1.2.2.2.1.span_eq
  obtain ⟨V, hV, hEq⟩ := hψ.1.highSpan_child hE (by omega) hdiv
  have hR : SkewGluing.IsConnectedSkew ψ.D := hψ.1.1
  have hVc : IsConnectedSkew V := SkewGluing.isConnectedSkew_component hR.1.interior hV
  have hchild := hψ.1.2.2.2.isConnectedSkew_compose hVc
  have hspan := span_eq_of_cellSchur_eq hE hchild hEq
  have hspan' := MarkedInner.span_compose hVc hψ.1.2.2.2
  change (span (ψ.ω.compose V) : ℤ) = (span V : ℤ) * ψ.period + ψ.ω.width at hspan'
  refine ⟨V, hV, hVc, hEq, by omega, ?_, ?_⟩
  · intro h1
    have hcard : V.card = 1 := by
      have hp := Finset.card_pos.mpr hVc.2.1
      by_contra hn
      have hh := two_le_span_of_two_le_card hVc (show 2 ≤ V.card by omega)
      omega
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hf : cellSchur (ψ.ω.compose V) = cellSchur ψ.ω.E := by
      rw [hz]
      exact hψ.1.2.2.2.cellSchur_singleton z (hz ▸ hVc)
    have hu : (ψ.ω.width : ℤ) < ψ.period := hψ.1.2.2.2.2.2.1.2
    rw [h1] at hspan'
    simp only [Nat.cast_one, one_mul] at hspan'
    exact ⟨hEq.trans hf, hlt, by omega⟩
  · intro h2
    have hcard : 2 ≤ V.card := by
      have hp := Finset.card_pos.mpr hVc.2.1
      by_contra hn
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (show V.card = 1 by omega)
      have hsp1 : span V = 1 := by
        rw [hz]
        simp [span, contents]
      omega
    have harea := Plan.card_eq_of_cellSchur_eq hE hchild hEq
    have hless := hχ.1.child_card_descent hS
    have hareaS := Plan.card_eq_of_cellSchur_eq
      (hχ.1.2.2.2.isConnectedSkew_compose hSc) hE he
    exact ⟨hψ.outer_independent hnl hVc hcard, harea.symm, by omega⟩

end GluingCore
