/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.OrdinaryAction
import SkewMarkedFactor.TableauDeletion
import SkewMarkedFactor.MarkAtlas

/-!
# Literal ordinary examples

«Explicit formulas and examples» (`sec:examples`, `eq:example-tail`,
`eq:example-outer`, `eq:two-row-mark`) of
`shields-2026-skew-marked-factor.tex`.
The cell sets and marks here are actual data for the differential assemblies.
-/

-- Kernel reduction of the literal fifty-three-cell unions uses nested finite-list recursors.
set_option maxRecDepth 4096

namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

/-- The displayed two-row inner, with row lengths four and five and overlap two. -/
def exampleInner : Diagram := skewOf [7, 5] [3, 0]

/-- The displayed connected seven-cell outer. -/
def exampleOuter : Diagram := skewOf [3, 2, 2] []

/-- The actual two-cell southwest mark and period-six displacement. -/
def exampleMark : MarkedInner where
  E := exampleInner
  W := {(1, 0), (1, 1)}
  v := (-1, 5)
  case := .a

/-- The two actual composed parents. -/
def exampleParent : Diagram := exampleMark.compose exampleOuter

/-- The parent obtained by composing the displayed mark with the rotated outer. -/
def exampleRotatedParent : Diagram := exampleMark.compose (rotate exampleOuter)

/-- The displayed mark satisfies the actual copied Hypotheses I–IV. -/
theorem exampleMark_legal : exampleMark.IsLegal := by decide +kernel

/-- The concrete input belongs to the complete paper-faithful ordinary domain. -/
theorem exampleMark_readoutLegal : exampleMark.IsReadoutLegal := exampleMark_legal.readoutLegal

theorem exampleMark_ordinary : exampleMark.IsOrdinary := by
  simp [MarkedInner.IsOrdinary, exampleMark, AttachCase.IsMixed]

@[simp]
theorem exampleMark_period : exampleMark.period = 6 := rfl

@[simp]
theorem exampleInner_card : exampleInner.card = 9 := by decide

@[simp]
theorem exampleOuter_card : exampleOuter.card = 7 := by decide

@[simp]
theorem exampleParent_card : exampleParent.card = 53 := by decide

@[simp]
theorem exampleRotatedParent_card : exampleRotatedParent.card = 53 := by decide

/-- The shape has actual standard-tableau count twenty-one. -/
theorem exampleOuter_tableau_count : standardTableauCount exampleOuter = 21 := by decide

/-- Both factors are concrete connected skew diagrams, not a certificate bundle. -/
theorem exampleInner_connected : IsConnectedSkew exampleInner := exampleMark_legal.1.1

theorem exampleOuter_connected : IsConnectedSkew exampleOuter := by decide +kernel

/-- The displayed chart is proper in the full readout domain. -/
theorem exampleChart_proper : (⟨exampleOuter, exampleMark⟩ : Chart).IsProperOrdinary := by
  exact ⟨⟨exampleOuter_connected, by decide, by decide, exampleMark_readoutLegal⟩,
    exampleMark_ordinary⟩

/-- The parents are distinct cell sets. -/
theorem example_parents_ne : exampleParent ≠ exampleRotatedParent := by decide

/-- They are not translates: southwest normalization distinguishes the actual cell sets. -/
theorem example_parents_not_translates :
    ¬ ∃ t : ℤ × ℤ, exampleParent = translate t exampleRotatedParent := by
  rintro ⟨t, ht⟩
  have hsw := congrArg sw ht
  have h1 : exampleParent.Nonempty := by decide
  have h2 : exampleRotatedParent.Nonempty := by decide
  rw [sw_translate h2] at hsw
  have hs1 : sw exampleParent = (5, -8) := by decide
  have hs2 : sw exampleRotatedParent = (3, -10) := by decide
  rw [hs1, hs2] at hsw
  have htval : t = (2, 2) := by
    apply Prod.ext <;> have := congrArg Prod.fst hsw <;> have := congrArg Prod.snd hsw <;>
      simp only [Prod.fst_add, Prod.snd_add] at * <;> omega
  subst t
  exact (by decide : exampleParent ≠ translate (2, 2) exampleRotatedParent) ht

end SkewMarkedFactor
