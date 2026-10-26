/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/Words.lean`. -/
import GluingCore.Coding
import GluingCore.EqualPeriods
import GluingCore.CommonFactorGraph
import GluingCore.MarkTransfer

/-!
# Boundary words of the roots of a diagram

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`): the bookkeeping shared by the constructions.

A *proper root* of period `p` of a diagram `F` is a chart `χ` with `χ.IsProperLegal`,
`χ.IsChartOf F` and `χ.period = p`.  The boundary words `wordA`, `wordB` of a translate of a
connected skew diagram agree with those of the diagram (`wordA_translate`, `wordB_translate`), so
the coding statements of `lem:gluing-coding` for the parent of a chart are statements about every
diagram that the chart presents.  This file collects, for a proper root,

* the span law `N = r q + w` with `r ≥ 2`, `0 ≤ w < q` and `q ≥ 2`;
* the class-constancy of a word with period `g` except at some residues (`PeriodExcept.eq_of_dvd`).

Sorry-free.
-/

namespace GluingCore

open MarkedInner

/-- A proper root of period `p` of `F`: a proper legal chart presenting `F` (up to translation)
with period `p`. -/
def Chart.IsProperRoot (χ : Chart) (F : Diagram) (p : ℕ) : Prop :=
  χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = p

namespace SmallOverlap

/-! ### Words of translates -/

theorem mem_contents_of_conn {D : Diagram} (hD : IsConnectedSkew D) {k : ℤ}
    (h1 : minContent D ≤ k) (h2 : k ≤ maxContent D) : k ∈ contents D :=
  ((isConnectedSkew_iff_diagonal.mp hD).mem_contents_iff).mpr ⟨h1, h2⟩

/-! ### The arithmetic of a proper root -/

/-- **Span law of a proper root.**  A proper root of period `p` and width `w` of `F` has
`N_F = r p + w` with `r = N_D ≥ 2`, `0 ≤ w < p` and `p ≥ 2`. -/
theorem _root_.GluingCore.Chart.IsProperRoot.arith {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) :
    2 ≤ span χ.D ∧ (span F : ℤ) = (span χ.D : ℤ) * p + χ.ω.width ∧
      (χ.ω.width : ℤ) < p ∧ 2 ≤ p := by
  obtain ⟨⟨hD, hc, hE, hω⟩, ⟨t, hF⟩, hp⟩ := h
  have hq : χ.ω.period = p := hp
  have hsp := span_compose hD hω
  have hFs : span F = span χ.parent := by rw [hF]; exact span_translate _
  have hw := hω.2.2.1.2
  have hspE := hω.1.span_eq
  have h2E := two_le_span_of_two_le_card hω.1.1 hE
  refine ⟨two_le_span_of_two_le_card hD hc, ?_, by omega, ?_⟩
  · rw [hFs]
    exact hsp.trans (by rw [hq])
  · have h0 : (0 : ℤ) ≤ χ.ω.width := by positivity
    omega

end SmallOverlap
end GluingCore
