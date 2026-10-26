import SkewGluing.Gluing
import SkewGluing.Score
import SkewGluing.NecessityReduction.Statements

/-!
# Facts about the chart score and source-minimal charts

Formalizes `shields-2026-skew-gluing.tex`, «Minimizing a chart» (`eq:chart-score`).

The score `Chart.score χ = (w, N_E)`, source-minimal charts `Chart.IsSourceMinimal χ F`, the
formula `Chart.IsProperLegal.score_eq` (`eq:chart-score`) and the existence
`Chart.exists_isSourceMinimal` are defined in `SkewGluing.NecessityReduction.Statements`.  This file
adds:

* `Chart.IsProperLegal.two_mul_period_le`: the period of a proper chart of `F` lies in the finite
  range `2 ≤ p ≤ N_F / 2`;
* `Chart.IsProperLegal.period_eq_of_score_eq`: the score of a proper chart determines its period;
* `exists_isSourceMinimal_of_rooted`: a rooted diagram has a source-minimal chart.

Sorry-free.
-/

namespace SkewGluing

namespace Chart

/-- The period of a proper chart is at most half the span of its parent: `N_F = r q + w` with
`r ≥ 2` (so the period lies in the finite range `2 ≤ p ≤ N_F / 2` of `eq:chart-score`). -/
theorem IsProperLegal.two_mul_period_le {F : Diagram} {χ : Chart} (h : χ.IsProperLegal)
    (hF : χ.IsChartOf F) : 2 * χ.period.toNat ≤ span F := by
  obtain ⟨t, rfl⟩ := hF
  have hspan := MarkedInner.span_compose h.1 h.2.2.2
  have hD := two_le_span_of_two_le_card h.1 h.2.1
  have hq : (χ.period.toNat : ℤ) = χ.period := h.period_toNat
  have hs : span (translate t χ.parent) = span χ.parent := span_translate t
  have hD' : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hD
  have hq0 : 0 < χ.period := h.2.2.2.period_pos
  have hw : (0 : ℤ) ≤ χ.ω.width := by positivity
  have hspan' : (span χ.parent : ℤ) = span χ.D * χ.period + χ.ω.width := hspan
  rw [hs]
  have : (2 : ℤ) * χ.period.toNat ≤ span χ.parent := by
    rw [hq, hspan']
    nlinarith
  exact_mod_cast this

/-- The period of a proper legal chart is determined by its score. -/
theorem IsProperLegal.period_eq_of_score_eq {F : Diagram} {χ χ' : Chart} (h : χ.IsProperLegal)
    (h' : χ'.IsProperLegal) (hF : χ.IsChartOf F) (hF' : χ'.IsChartOf F)
    (hs : χ.score = χ'.score) : χ.period = χ'.period := by
  rw [h.score_eq hF, h'.score_eq hF'] at hs
  unfold SkewGluing.score at hs
  rw [toLex_inj, Prod.mk.injEq] at hs
  have e : χ.period.toNat = χ'.period.toNat := by omega
  rw [← h.period_toNat, ← h'.period_toNat, e]

end Chart

/-- A rooted diagram has a source-minimal chart. -/
theorem exists_isSourceMinimal_of_rooted {F : Diagram} (h : HasProperChart F) :
    ∃ χ : Chart, χ.IsSourceMinimal F :=
  Chart.exists_isSourceMinimal h

end SkewGluing
