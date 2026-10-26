import SkewGluing.Lines.ChartRoot
import SkewGluing.Lines.Mates
import SkewGluing.Lines.WordFacts

/-!
# Line inners

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`).

**First assertion** (coprime periods): `Chart.IsProperLegal.coprime_periods_line`.
Two proper roots `χ₁`, `χ₂` of one diagram `F` whose periods are coprime are both ordinary, and
either both inners are rows or both are columns.  The proof is `SkewGluing.Lines.coprime_pair`, a
statement about the boundary words only (via `lem:gluing-periods`), fed by `rootData_of_chart`
(`lem:gluing-coding`, `lem:gluing-local` and the first window of the composite).

**Second assertion**: if a diagram has a proper line chart, every skew diagram with its function
has a proper legal chart with the *same marked inner* and an outer with the *same function*
(`Chart.IsProperLegal.exists_chart_of_line`, row case via `lem:gluing-row-action`,
`lem:gluing-row-transport`; column case by antitransposition, with the empty vertical reading
converted by `eq:gluing-gauge`); a line parent has a singleton Schur class
(`eq_translate_of_cellSchur_eq_of_isLine`); and every fork at a diagram with a proper line chart
glues (`HasCommonFinalFactor.of_line_inner`, `classGraph_adj_of_line_inner`).  The last clause
is derived from the mate statement; it does not use `prop:gluing-divisible`.

Sorry-free.
-/

namespace SkewGluing

namespace Chart

/-- The word data of a proper root transfers to any translate of its parent. -/
theorem IsProperLegal.rootData_of_isChartOf {χ : Chart} (hχ : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) :
    Lines.RootData (wordA F) (wordB F) (span F) χ.period.toNat (IsRowDiagram χ.ω.E)
      (IsColumnDiagram χ.ω.E) χ.ω.case.IsMixed := by
  obtain ⟨t, rfl⟩ := hF
  have hconn : IsConnectedSkew χ.parent := hχ.2.2.2.isConnectedSkew_compose hχ.1
  have hs : span (translate t χ.parent) = span χ.parent := span_translate t
  have h := Lines.rootData_of_chart hχ
  rw [← hs] at h
  refine Lines.RootData.congr (fun x hx => ?_) (fun x hx => ?_) h
  · have hx' := Finset.mem_Icc.mp hx
    exact (wordA_translate hconn t hx'.1 (by omega)).symm
  · have hx' := Finset.mem_Icc.mp hx
    exact (wordB_translate hconn t hx'.1 (by omega)).symm

/-- **`lem:gluing-lines` (1).**  If two proper roots `χ₁`, `χ₂` of one diagram `F` have coprime
periods, then both charts are ordinary (case (a) or (b)), and either both inners are rows (read
horizontally) or both inners are columns.  The row (column) inner of an empty mark is the
statement that its diagram lies in one row (column). -/
theorem IsProperLegal.coprime_periods_line {χ₁ χ₂ : Chart} {F : Diagram}
    (h₁ : χ₁.IsProperLegal) (h₂ : χ₂.IsProperLegal) (c₁ : χ₁.IsChartOf F) (c₂ : χ₂.IsChartOf F)
    (hcop : Int.gcd χ₁.period χ₂.period = 1) :
    ¬ χ₁.ω.case.IsMixed ∧ ¬ χ₂.ω.case.IsMixed ∧
      ((IsRowDiagram χ₁.ω.E ∧ IsRowDiagram χ₂.ω.E) ∨
        (IsColumnDiagram χ₁.ω.E ∧ IsColumnDiagram χ₂.ω.E)) := by
  have hF : IsConnectedSkew F := by
    obtain ⟨t, rfl⟩ := c₁
    exact (isConnectedSkew_translate_iff t).mpr (h₁.2.2.2.isConnectedSkew_compose h₁.1)
  have hcop' : Nat.Coprime χ₁.period.toNat χ₂.period.toNat := by
    have p1 : 0 < χ₁.period := h₁.2.2.2.period_pos
    have p2 : 0 < χ₂.period := h₂.2.2.2.period_pos
    unfold Int.gcd at hcop
    have e1 : χ₁.period.toNat = χ₁.period.natAbs := by omega
    have e2 : χ₂.period.toNat = χ₂.period.natAbs := by omega
    rw [e1, e2]
    exact hcop
  exact Lines.coprime_pair
    (fun x hx => by
      have hx' := Finset.mem_Icc.mp hx
      have hspan : 1 ≤ span F := by
        have := span_eq_of_isConnectedSkew hF
        have := minContent_le (maxContent_mem hF.2.1)
        omega
      exact ⟨Lines.wordA_bit hF hx'.1 (by omega), Lines.wordB_bit hF hx'.1 (by omega)⟩)
    (Lines.sum_wordA_eq_sum_wordB hF) hcop'
    (h₁.rootData_of_isChartOf c₁) (h₂.rootData_of_isChartOf c₂)

end Chart

/-! ### Checked examples -/

section Examples

/-- `(7) = (3) ∘_{ω} (3) = (2) ∘_{ω'} (4)`: the two charts of the row `(7)` with the singleton
marks of periods two and three are coprime, and both inners are rows. -/
example : Chart.IsProperLegal ⟨skewOf [3] [], rowInnerThree⟩ := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩

example : Chart.IsProperLegal ⟨skewOf [2] [], rowInnerFour⟩ := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩

example : Chart.IsChartOf ⟨skewOf [3] [], rowInnerThree⟩ (skewOf [7] []) :=
  ⟨0, by rw [translate_zero]; exact (by decide +kernel :
    MarkedInner.compose (skewOf [3] []) rowInnerThree = skewOf [7] []).symm⟩

example : Chart.IsChartOf ⟨skewOf [2] [], rowInnerFour⟩ (skewOf [7] []) :=
  ⟨0, by rw [translate_zero]; exact (by decide +kernel :
    MarkedInner.compose (skewOf [2] []) rowInnerFour = skewOf [7] []).symm⟩

/-- **The first assertion on the row `(7)`.**  Coprime periods two and three. -/
example : (¬ rowInnerThree.case.IsMixed ∧ ¬ rowInnerFour.case.IsMixed) ∧
    ((IsRowDiagram rowInnerThree.E ∧ IsRowDiagram rowInnerFour.E) ∨
      (IsColumnDiagram rowInnerThree.E ∧ IsColumnDiagram rowInnerFour.E)) := by
  have h₁ : Chart.IsProperLegal ⟨skewOf [3] [], rowInnerThree⟩ :=
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩
  have h₂ : Chart.IsProperLegal ⟨skewOf [2] [], rowInnerFour⟩ :=
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩
  have c₁ : Chart.IsChartOf ⟨skewOf [3] [], rowInnerThree⟩ (skewOf [7] []) :=
    ⟨0, by rw [translate_zero]; exact (by decide +kernel :
      MarkedInner.compose (skewOf [3] []) rowInnerThree = skewOf [7] []).symm⟩
  have c₂ : Chart.IsChartOf ⟨skewOf [2] [], rowInnerFour⟩ (skewOf [7] []) :=
    ⟨0, by rw [translate_zero]; exact (by decide +kernel :
      MarkedInner.compose (skewOf [2] []) rowInnerFour = skewOf [7] []).symm⟩
  have := Chart.IsProperLegal.coprime_periods_line h₁ h₂ c₁ c₂ (by decide +kernel)
  exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩

end Examples

end SkewGluing
