/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.FactorRecovery

/-!
# Rejection at a supplied period

«Recovering the factors» (`sec:extraction`, `cor:period-test`) of
`shields-2026-skew-marked-factor.tex`.
Rejection excludes every proper ordinary chart whose parent function is the
supplied polynomial, not merely charts presenting one literal diagram.
A nonrational quotient is tested in the actual fraction field.  These are
necessary conditions only; no converse or period-selection rule is asserted.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan

/-- Rationality in the genuine fraction field, not a coefficient-reading surrogate. -/
def IsRationalReadout (x : ReadoutField) : Prop :=
  ∃ q : ℚ, x = algebraMap ℚ ReadoutField q

/-- A realization is identified by its parent function and its supplied integer period. -/
def HasProperOrdinaryChart (P : Lambda) (p : ℤ) : Prop :=
  ∃ χ : Chart, χ.IsProperOrdinary ∧ cellSchur χ.parent = P ∧ χ.period = p

/-- The two mathematical obstructions evaluated from the polynomial and period alone. -/
def BadPeriod (P : Lambda) (p : ℕ) : Prop :=
  pDeriv p P = 0 ∨
    ∃ d ∈ partitionExponents (terminalOrder P p),
      ¬ IsRationalReadout (actualRatio (characterDerivative P p d) (terminalDerivative P p))

/-- Any proper ordinary realization discharges both necessary supplied-period tests. -/
theorem proper_ordinary_period_not_bad {P : Lambda} {p : ℤ}
    (h : HasProperOrdinaryChart P p) : ¬ BadPeriod P p.toNat := by
  obtain ⟨χ, hχ, hP, hp⟩ := h
  have hpn : χ.period.toNat = p.toNat := congrArg Int.toNat hp
  intro hbad
  rcases hbad with hz | ⟨d, hd, hnr⟩
  · have hn := ordinary_parent_first_derivative_ne_zero hχ
    rw [hP, hpn] at hn
    exact hn hz
  · apply hnr
    refine ⟨characterCoefficient (adjustedOuter χ) d / (standardTableauCount χ.D : ℚ), ?_⟩
    have hd' : d ∈ partitionExponents
        (terminalOrder (cellSchur χ.parent) χ.period.toNat) := by
      simpa only [hP, hpn] using hd
    simpa only [hP, hpn] using character_ratios_rational hχ hd'

/-- Either obstruction rejects all proper ordinary realizations of the parent function. -/
theorem period_test {P : Lambda} {p : ℤ} (_hP : P ≠ 0) (_hp : 1 ≤ p)
    (hbad : BadPeriod P p.toNat) : ¬ HasProperOrdinaryChart P p := by
  intro hchart
  exact proper_ordinary_period_not_bad hchart hbad

/-- The first-derivative obstruction alone rules out every such realization. -/
theorem period_test_zero_derivative {P : Lambda} {p : ℤ}
    (hzero : pDeriv p.toNat P = 0) : ¬ HasProperOrdinaryChart P p := by
  intro hchart
  exact proper_ordinary_period_not_bad hchart (Or.inl hzero)

/-- A single genuinely nonrational character quotient rules out every such realization. -/
theorem period_test_nonrational {P : Lambda} {p : ℤ} {d : powerExponent}
    (hd : d ∈ partitionExponents (terminalOrder P p.toNat))
    (hnr : ¬ IsRationalReadout
      (actualRatio (characterDerivative P p.toNat d) (terminalDerivative P p.toNat))) :
    ¬ HasProperOrdinaryChart P p := by
  intro hchart
  exact proper_ordinary_period_not_bad hchart (Or.inr ⟨d, hd, hnr⟩)

end SkewMarkedFactor
