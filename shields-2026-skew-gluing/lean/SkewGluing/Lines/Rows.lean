import SkewGluing.OlsonHarris.RowCase
import SkewGluing.EqualPeriods
import SkewGluing.CommonFactorGraph

/-!
# Mates of a diagram with a row inner

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`), second assertion, the row case.

A diagram whose proper chart has a row for inner (read horizontally) is the image of its outer
under `𝓛_{q,w}` (`lem:gluing-row-action`), and `𝓛_{q,w}` bijects Schur classes
(`lem:gluing-row-transport`).  Hence every skew diagram with the same function has the same
marked row inner and an outer with the outer function of the given chart:
`MarkedInner.IsRowMark.exists_chart_of_cellSchur_eq`.

* `IsRowDiagram`, `IsColumnDiagram`: a diagram in one row, respectively one column.
* `card_eq_of_cellSchur_eq`: Schur-equal connected diagrams have as many cells.
* `Chart.IsProperLegal.exists_proper_chart_of_row`: the transport in terms of proper legal charts.

Sorry-free.
-/

namespace SkewGluing

/-- The diagram lies in a single row. -/
def IsRowDiagram (E : Diagram) : Prop := ∃ r : ℤ, ∀ x ∈ E, x.1 = r

/-- The diagram lies in a single column. -/
def IsColumnDiagram (E : Diagram) : Prop := ∃ c : ℤ, ∀ x ∈ E, x.2 = c

/-- Schur-equal skew diagrams, one of them connected, have the same number of cells
(homogeneity of `cellSchur`). -/
theorem card_eq_of_cellSchur_eq {D D' : Diagram} (hD : IsConnectedSkew D) (hD' : IsSkew D')
    (h : cellSchur D' = cellSchur D) : D'.card = D.card := by
  have h1 := isWeightedHomogeneous_cellSchur hD.1
  have h2 := isWeightedHomogeneous_cellSchur hD'
  rw [h] at h2
  have hne : cellSchur D ≠ 0 := by
    rw [cellSchur_of_isConnectedSkew hD]
    exact (barekatIrreducibility _ _).ne_zero
  exact MvPolynomial.IsWeightedHomogeneous.inj_right hne h2 h1

namespace MarkedInner

/-- **`lem:gluing-lines` (2), row case, on outers.**  Let `ω` be a marked inner that is a placed
row mark `ω_{q,w}`, and `D` a connected outer.  Every skew diagram `H` with the function of
`D ∘_ω E` is, up to translation, `D' ∘_ω E` for a connected outer `D'` with the same function and
the same number of cells as `D`.  No assumption on the number of rows of the parent is needed. -/
theorem IsRowMark.exists_chart_of_cellSchur_eq {ω : MarkedInner} {s : RowShift} {u : ℤ × ℤ}
    (h : ω.IsRowMark s u) {D H : Diagram} (hD : IsConnectedSkew D) (hH : IsSkew H)
    (hs : cellSchur H = cellSchur (ω.compose D)) :
    ∃ D' : Diagram, IsConnectedSkew D' ∧ cellSchur D' = cellSchur D ∧ D'.card = D.card ∧
      ∃ t, H = SkewGluing.translate t (ω.compose D') := by
  obtain ⟨v, hv⟩ := rowMark_compose_eq_liftCells s hD
  rw [h.compose hD.2.1, cellSchur_translate, hv, cellSchur_translate] at hs
  have hHc : IsConnectedSkew H := by
    refine isConnectedSkew_of_cellSchur_eq (isConnectedSkew_liftCells s D) hH hs
  obtain ⟨D', hD'c, hD's, w, hw⟩ := exists_liftCells_of_cellSchur_eq s hD hHc hs
  refine ⟨D', hD'c, hD's, card_eq_of_cellSchur_eq hD hD'c.1 hD's, ?_⟩
  obtain ⟨v', hv'⟩ := rowMark_compose_eq_liftCells s hD'c
  refine ⟨w - (u + v'), ?_⟩
  rw [h.compose hD'c.2.1, hv', SkewGluing.translate_translate, SkewGluing.translate_translate, hw]
  congr 1
  abel

end MarkedInner

theorem card_rowCells (m : ℕ) : (rowCells 0 (m : ℤ)).card = m := by
  unfold rowCells
  rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Int.card_Ico]
  simp

theorem card_translate (u : ℤ × ℤ) (D : Diagram) : (translate u D).card = D.card :=
  Finset.card_image_of_injective _ (add_left_injective _)

/-- A connected skew diagram in one row is a placed row of `E.card` cells. -/
theorem exists_translate_rowCells_of_isRow {E : Diagram} (hE : IsConnectedSkew E)
    (hrow : IsRowDiagram E) : ∃ u : ℤ × ℤ, E = translate u (rowCells 0 (E.card : ℤ)) := by
  obtain ⟨r, hr⟩ := hrow
  obtain ⟨lo, hi, hlohi, -, -, hW⟩ := exists_eq_translate_rowCells hE.1 hE.2.1 hr
  have h0 : (((hi - lo + 1).toNat : ℕ) : ℤ) = hi - lo + 1 := Int.toNat_of_nonneg (by omega)
  have h1 := card_rowCells (hi - lo + 1).toNat
  rw [h0] at h1
  have hc : E.card = (hi - lo + 1).toNat := by
    rw [hW, card_translate]
    exact h1
  refine ⟨(r, lo), ?_⟩
  rw [hc, h0]
  exact hW

namespace Chart

/-- **`lem:gluing-lines` (2), row case, for charts.**  Let `χ` be a proper legal chart whose inner
is a row (read horizontally).  Every skew diagram `H` with the function of the parent of `χ` has a
proper legal chart with the *same marked inner* and an outer with the function of `χ.D`. -/
theorem IsProperLegal.exists_chart_of_row {χ : Chart} (hχ : χ.IsProperLegal)
    (hrow : IsRowDiagram χ.ω.E) {H : Diagram} (hH : IsSkew H)
    (hs : cellSchur H = cellSchur χ.parent) :
    ∃ χ' : Chart, χ'.IsProperLegal ∧ χ'.ω = χ.ω ∧ cellSchur χ'.D = cellSchur χ.D ∧
      χ'.IsChartOf H := by
  obtain ⟨hD, hDc, hEc, hω⟩ := hχ
  obtain ⟨u, hE⟩ := exists_translate_rowCells_of_isRow hω.1.1 hrow
  obtain ⟨s, hs'⟩ := hω.exists_isRowMark hE (by omega)
  obtain ⟨D', hD'c, hD's, hD'card, t, ht⟩ := hs'.exists_chart_of_cellSchur_eq hD hH hs
  exact ⟨⟨D', χ.ω⟩, ⟨hD'c, by change 2 ≤ D'.card; omega, hEc, hω⟩, rfl, hD's, t, ht⟩

end Chart

end SkewGluing
