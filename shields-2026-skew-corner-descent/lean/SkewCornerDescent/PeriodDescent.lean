/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ChartCofactor

/-!
# Minimal-span period descent

Formalizes `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `thm:descent`, `cor:equivalent-base`).
Actual geometric children give a strictly smaller counterexample unless the
larger-period outer has discrete southeast interior.

Sorry-free.
-/

namespace GluingCore

/-- A pair of source-minimal actual charts with equal functions and different periods. -/
def PeriodFailure (χ ψ : Chart) : Prop :=
  χ.IsSourceMinimal χ.parent ∧ ψ.IsSourceMinimal ψ.parent ∧
    cellSchur χ.parent = cellSchur ψ.parent ∧ χ.period ≠ ψ.period

/-- A singleton actual outer has the inner's span. -/
theorem MarkedInner.span_compose_singleton (ω : MarkedInner) (x : ℤ × ℤ) :
    span (ω.compose {x}) = span ω.E := by
  have he := ω.toCorner.compose_singleton x
  rw [MarkedInner.toCorner_compose] at he
  rw [he]
  exact span_translate _

/-- Every component witnessing nondiscreteness contains at least two cells. -/
theorem component_two_le_card {D C : Diagram} (hD : IsSkew D)
    (hC : C ∈ edgeComponents D) (hne : C.card ≠ 1) : 2 ≤ C.card := by
  have hp := Finset.card_pos.mpr (isConnectedSkew_component hD hC).2.1
  omega

/-- A least-span different-period pair has a discrete larger-period outer. -/
theorem PeriodFailure.discrete_of_least_span {χ ψ : Chart} (h : PeriodFailure χ ψ)
    (hlt : χ.period < ψ.period)
    (hmin : ∀ χ' ψ', PeriodFailure χ' ψ' → span χ.parent ≤ span χ'.parent) :
    SkewGluing.HasDiscreteInterior ψ.D := by
  classical
  have hχ := h.1
  have hψ := h.2.1
  have hs := h.2.2.1
  have hnlχ : ¬ LineInner χ.ω := fun hl => h.2.2.2 (hχ.period_eq_of_line hψ hs hl)
  have hnlψ : ¬ LineInner ψ.ω := fun hl => h.2.2.2 (hψ.period_eq_of_line hχ hs.symm hl).symm
  intro T hT
  by_contra hn
  have hψD : SkewGluing.IsConnectedSkew ψ.D := hψ.1.1
  have hTconn : IsConnectedSkew T :=
    SkewGluing.isConnectedSkew_component hψD.1.interior hT
  have hTcard : 2 ≤ T.card := component_two_le_card hψD.1.interior hT hn
  have hG := hψ.1.2.2.2.isConnectedSkew_compose hTconn
  have hGspan := MarkedInner.span_compose hTconn hψ.1.2.2.2
  have hTspan := two_le_span_of_two_le_card hTconn hTcard
  have hp : 0 < χ.period := hχ.1.2.2.2.period_pos
  have hq : 0 < ψ.period := hψ.1.2.2.2.period_pos
  have hw : χ.ω.width < χ.period := hχ.1.2.2.2.2.2.1.2
  have hu : (0 : ℤ) ≤ ψ.ω.width := hψ.1.2.2.2.2.2.1.1
  change (span (ψ.ω.compose T) : ℤ) = (span T : ℤ) * ψ.period + ψ.ω.width at hGspan
  have hTspan' : (2 : ℤ) ≤ span T := by exact_mod_cast hTspan
  have hGlarge : χ.period + χ.ω.width < (span (ψ.ω.compose T) : ℤ) := by
    nlinarith
  have hd := (hψ.1.child_factor hT).2
  have hc := interior_cellSchur_eq_of_eq
    (hχ.1.2.2.2.isConnectedSkew_compose hχ.1.1)
    (hψ.1.2.2.2.isConnectedSkew_compose hψ.1.1) hs
  change cellSchur (SkewGluing.diagramInterior χ.parent) =
    cellSchur (SkewGluing.diagramInterior ψ.parent) at hc
  rw [← hc] at hd
  have hw0 : (0 : ℤ) ≤ χ.ω.width := hχ.1.2.2.2.2.2.1.1
  obtain ⟨S, hS, hchild⟩ := hχ.1.highSpan_child hG (by omega) hd
  have hχD : SkewGluing.IsConnectedSkew χ.D := hχ.1.1
  have hSconn : IsConnectedSkew S :=
    SkewGluing.isConnectedSkew_component hχD.1.interior hS
  have hScomp := hχ.1.2.2.2.isConnectedSkew_compose hSconn
  have hsp := span_eq_of_cellSchur_eq hG hScomp hchild
  have hScard : 2 ≤ S.card := by
    have hpS := Finset.card_pos.mpr hSconn.2.1
    by_contra hnS
    have he : S.card = 1 := by omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp he
    have hs1 := χ.ω.span_compose_singleton x
    have hi : (span χ.ω.E : ℤ) = χ.period + χ.ω.width := hχ.1.2.2.2.1.span_eq
    omega
  have hχ' := hχ.outer_independent hnlχ hSconn hScard
  have hψ' := hψ.outer_independent hnlψ hTconn hTcard
  have hf : PeriodFailure (⟨S, χ.ω⟩ : Chart) (⟨T, ψ.ω⟩ : Chart) :=
    ⟨hχ', hψ', hchild.symm, h.2.2.2⟩
  have hm := hmin _ _ hf
  have hdsp := hψ.1.child_span_descent hT
  have hpar := span_eq_of_cellSchur_eq
    (hχ.1.2.2.2.isConnectedSkew_compose hχ.1.1)
    (hψ.1.2.2.2.isConnectedSkew_compose hψ.1.1) hs
  change span χ.parent = span ψ.parent at hpar
  change span χ.parent ≤ span (χ.ω.compose S) at hm
  omega

/-- Equality of source-minimal periods reduces exactly to discrete larger-period outers. -/
theorem sourceMinimal_periods_iff_discrete :
    (∀ χ ψ : Chart, χ.IsSourceMinimal χ.parent → ψ.IsSourceMinimal ψ.parent →
      cellSchur χ.parent = cellSchur ψ.parent → χ.period = ψ.period) ↔
    (∀ χ ψ : Chart, χ.IsSourceMinimal χ.parent → ψ.IsSourceMinimal ψ.parent →
      cellSchur χ.parent = cellSchur ψ.parent → χ.period < ψ.period →
      SkewGluing.HasDiscreteInterior ψ.D → χ.period = ψ.period) := by
  classical
  constructor
  · intro h χ ψ hχ hψ hs _ _
    exact h χ ψ hχ hψ hs
  · intro hr
    by_contra hn
    have he : ∃ n : ℕ, ∃ χ ψ : Chart, PeriodFailure χ ψ ∧ span χ.parent = n := by
      push Not at hn
      obtain ⟨χ, ψ, hχ, hψ, hs, hp⟩ := hn
      exact ⟨span χ.parent, χ, ψ, ⟨hχ, hψ, hs, hp⟩, rfl⟩
    obtain ⟨χ, ψ, hf, hspan⟩ := Nat.find_spec he
    have hmin : ∀ χ' ψ', PeriodFailure χ' ψ' → span χ.parent ≤ span χ'.parent := by
      intro χ' ψ' hf'
      rw [hspan]
      exact Nat.find_min' he ⟨χ', ψ', hf', rfl⟩
    rcases lt_or_gt_of_ne hf.2.2.2 with hlt | hlt
    · exact hf.2.2.2 (hr χ ψ hf.1 hf.2.1 hf.2.2.1 hlt
        (hf.discrete_of_least_span hlt hmin))
    · have hf' : PeriodFailure ψ χ :=
        ⟨hf.2.1, hf.1, hf.2.2.1.symm, hf.2.2.2.symm⟩
      have hp := span_eq_of_cellSchur_eq
        (hf.1.1.2.2.2.isConnectedSkew_compose hf.1.1.1)
        (hf.2.1.1.2.2.2.isConnectedSkew_compose hf.2.1.1.1) hf.2.2.1
      change span χ.parent = span ψ.parent at hp
      have hm : ∀ χ' ψ', PeriodFailure χ' ψ' → span ψ.parent ≤ span χ'.parent := by
        intro χ' ψ' h'
        rw [← hp]
        exact hmin χ' ψ' h'
      exact hf'.2.2.2 (hr ψ χ hf'.1 hf'.2.1 hf'.2.2.1 hlt
        (hf'.discrete_of_least_span hlt hm))

end GluingCore
