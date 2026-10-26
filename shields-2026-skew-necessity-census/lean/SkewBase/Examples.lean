import SkewBase.SearchesNormalize

/-!
# Non-vacuity of the size bounds and of the searches

Formalizes `shields-2026-skew-base-computational.tex`, `lem:size`, `lem:inner-size` and
`thm:searches`: the hypotheses of the size bounds are met by an actual chart, the chart of
`fig:chart` of the sibling paper, an outer domino composed with a case-(a) mark of period `3` and
width `2`.  The bounds are evaluated on it, and searches S and B return it.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-- The chart of the figure: the domino composed with `chartFigureInner`. -/
def figureChart : Chart := ⟨domino, chartFigureInner⟩

theorem figureChart_isProperLegal : figureChart.IsProperLegal := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem figureChart_parent_card : figureChart.parent.card = 10 := by decide +kernel

/-- `lem:size` on the figure: `q |D| + w = 3 · 2 + 2 ≤ 10 = |F|`. -/
example : (6 : ℤ) + 2 ≤ 10 := by
  have h := size_of_proper figureChart_isProperLegal
  have hq : figureChart.ω.period = 3 := by decide +kernel
  have hw : (figureChart.ω.width : ℤ) = 2 := by decide +kernel
  have hD : figureChart.D.card = 2 := by decide +kernel
  rw [figureChart_parent_card, hq, hw, hD] at h
  exact_mod_cast h

/-- `lem:inner-size` on the figure: `3 |E| + 1 = 19 ≤ 20 = 2 |F|`. -/
example : 3 * 6 + 1 ≤ 2 * 10 := by
  have h := inner_size figureChart_isProperLegal
  have hE : figureChart.ω.E.card = 6 := by decide +kernel
  rwa [figureChart_parent_card, hE] at h

/-- The figure chart is in normalized position. -/
theorem figureChart_normalized : sw figureChart.D = 0 ∧ sw figureChart.ω.E = 0 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Search S returns the figure chart on its composite. -/
theorem figureChart_mem_searchS : figureChart ∈ SearchS figureChart.parent :=
  searchS_complete figureChart_isProperLegal rfl figureChart_normalized.1
    figureChart_normalized.2

/-- Search B returns the figure chart on its composite. -/
theorem figureChart_mem_searchB : figureChart ∈ SearchB figureChart.parent :=
  searchB_complete figureChart_isProperLegal rfl figureChart_normalized.1
    figureChart_normalized.2

end SkewBase
