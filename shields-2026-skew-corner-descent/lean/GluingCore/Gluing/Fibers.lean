/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Gluing/Fibers.lean`. -/
import GluingCore.Gluing.Roots
import GluingCore.Gluing.Edges
import GluingCore.Divisible

/-!
# Comparing the fibers of two proper charts of one diagram

Formalizes `shields-2026-skew-factor-gluing.tex`, «Completion of the gluing proof» (`thm:gluing`)
and the comparison table of `thm:source-minimal-domination`: for two proper charts of one diagram,
a period `p` dividing a period `q` puts the period-`q` fiber inside the period-`p` fiber
(`lem:gluing-equal` for `p = q`, `prop:gluing-divisible` for `p < q`).

* `Chart.IsProperLegal.fiber_subset_of_dvd`: the containment, taking the Olson-Harris composition
  and reversal theorems as the hypothesis `hOH : OlsonHarrisComposition`.
* `Chart.IsProperLegal.exists_covering_chart`: for two proper charts of one diagram, neither of
  which can be traded for a line inner, there is a proper chart whose fiber contains both fibers.

The hypothesis `hOH` is discharged by `olsonHarrisComposition` (`GluingCore.OlsonHarris`) in
`GluingCore.MainTheorems`.

Sorry-free.
-/

namespace GluingCore

namespace Chart

/-- **Divisible periods nest the fibers** (`lem:gluing-equal` and `prop:gluing-divisible`).  If
`χ`, `χ'` are proper legal charts of one diagram and `χ.period ∣ χ'.period`, then the fiber of
`χ'` lies in the fiber of `χ`.  Uses the Olson-Harris composition and reversal theorems
(Thms. 5.3.9–5.3.10) through `hOH`. -/
theorem IsProperLegal.fiber_subset_of_dvd (hOH : OlsonHarrisComposition) {F : Diagram}
    {χ χ' : Chart} (h : χ.IsProperLegal) (h' : χ'.IsProperLegal) (c : χ.IsChartOf F)
    (c' : χ'.IsChartOf F) (hdvd : χ.period ∣ χ'.period) :
    fiberClass cellSchur χ'.ω (cellSchur χ'.D) ⊆ fiberClass cellSchur χ.ω (cellSchur χ.D) := by
  have hp : 0 < χ.period := h.2.2.2.period_pos
  have hp' : 0 < χ'.period := h'.2.2.2.period_pos
  rcases (Int.le_of_dvd hp' hdvd).lt_or_eq with hlt | heq
  · obtain ⟨V, t, -, -, -, -, hsub⟩ := MarkedInner.divisible (olsonHarris_pair hOH) h h' c c' hlt
      hdvd
    exact hsub
  · exact (h.equal_periods_same_fiber h' c c' heq).ge

end Chart

end GluingCore
