import SkewGluing.Lines.ColumnMates
import SkewGluing.MarkLocality
import SkewGluing.CommonFactorGraph
import SkewGluing.OlsonHarris.FiberClique

/-!
# Mates of a diagram with a proper line inner

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`), second assertion.

A *line inner* is a marked inner whose diagram is a row or a column (read horizontally).

* `Chart.IsProperLegal.exists_chart_of_row`, `Chart.IsProperLegal.exists_chart_of_column`,
  `Chart.IsProperLegal.exists_chart_of_line`: every skew diagram with the function of the parent of
  a proper legal chart with a line inner has a proper legal chart with **the same marked inner**
  (as data, not only up to translation) and an outer with the function of the given outer.  The
  column case antitransposes; a nonempty column mark has the case (b) and becomes a row mark, and
  the empty vertical reading is converted back to the horizontal one by `eq:gluing-gauge`.
* `eq_translate_of_cellSchur_eq_of_isRow`, `eq_translate_of_cellSchur_eq_of_isColumn`,
  `eq_translate_of_cellSchur_eq_of_isLine`: a connected skew diagram lying in one row, or one
  column, has a singleton Schur class up to translation.
* `HasCommonFinalFactor.of_line_inner`: if `Y` has a proper line chart and `X`, `Z` are skew
  diagrams in the Schur class of `Y` that are not translates of one another, then `X` and `Z`
  have a common final factor.  This is the content of "every fork at that diagram glues"
  (`def:gluing-graph`): the two edges of the fork are not used, only that the three vertices lie
  in one common-factor graph; `classGraph_adj_of_line_inner` states it as adjacency in the graph
  `classGraph (skewClass P)`.

Sorry-free.
-/

namespace SkewGluing

theorem emptyMarkH_anti {E : Diagram} (hE : IsConnectedSkew E) :
    (emptyMarkH E).anti = emptyMarkV (antitranspose E) := by
  have hne := hE.2.1
  have hv : atVec (vH E) = vV (antitranspose E) := by
    unfold vH vV
    rw [sw_antitranspose hE, ne_antitranspose hE]
    ext <;> simp [atVec] <;> ring
  simp [MarkedInner.anti, emptyMarkH, emptyMarkV, antitranspose, hv, AttachCase.anti]

theorem emptyMarkV_anti {E : Diagram} (hE : IsConnectedSkew E) :
    (emptyMarkV E).anti = emptyMarkH (antitranspose E) := by
  have hv : atVec (vV E) = vH (antitranspose E) := by
    unfold vH vV
    rw [sw_antitranspose hE, ne_antitranspose hE]
    ext <;> simp [atVec] <;> ring
  simp [MarkedInner.anti, emptyMarkH, emptyMarkV, antitranspose, hv, AttachCase.anti]

theorem AttachCase.eq_b_of_anti_eq_a {x : AttachCase} (h : x.anti = .a) : x = .b := by
  cases x <;> simp_all [AttachCase.anti]

theorem MarkedInner.eq_emptyMarkH {ω : MarkedInner} (h : ω.IsEmptyMark) :
    ω = emptyMarkH ω.E := by
  obtain ⟨h1, h2, h3⟩ := h
  cases ω
  simp_all [emptyMarkH]

theorem isRowDiagram_antitranspose {E : Diagram} (hcol : IsColumnDiagram E) :
    IsRowDiagram (antitranspose E) := by
  obtain ⟨c, hc⟩ := hcol
  refine ⟨-c, fun x hx => ?_⟩
  have := hc _ (mem_antitranspose'.mp hx)
  simp only [atVec] at this
  omega

namespace Chart

/-- **`lem:gluing-lines` (2), column case.**  Let `χ` be a proper legal chart whose inner is a
column.  Every skew diagram `H` with the function of the parent of `χ` has a proper legal chart
with the same marked inner and an outer with the function of `χ.D`.  A nonempty mark is of case
(b) and is a row mark after antitransposition; the empty mark is read vertically first, which
antitransposes the outer by `eq:gluing-gauge`.  **Differs from the paper's route.** The paper
transposes the diagram; here the antitransposition `AT`, for which the composition identity
`MarkedInner.antitranspose_compose` and `s_{AT(D)} = ι(s_D)` are available, is used. -/
theorem IsProperLegal.exists_chart_of_column {χ : Chart} (hχ : χ.IsProperLegal)
    (hcol : IsColumnDiagram χ.ω.E) {H : Diagram} (hH : IsSkew H)
    (hs : cellSchur H = cellSchur χ.parent) :
    ∃ χ' : Chart, χ'.IsProperLegal ∧ χ'.ω = χ.ω ∧ cellSchur χ'.D = cellSchur χ.D ∧
      χ'.IsChartOf H := by
  obtain ⟨hD, hDc, hEc, hω⟩ := hχ
  have hDne : χ.D.Nonempty := hD.2.1
  have hE := hω.1.1
  have hAT : cellSchur (antitranspose H) = cellSchur (antitranspose χ.parent) := by
    rw [cellSchur_antitranspose, cellSchur_antitranspose, hs]
  have hEAT : IsConnectedSkew (antitranspose χ.ω.E) := isConnectedSkew_antitranspose hE
  have hEATc : 2 ≤ (antitranspose χ.ω.E).card := by rw [card_antitranspose]; exact hEc
  obtain ⟨u, hu⟩ := exists_translate_rowCells_of_isRow hEAT (isRowDiagram_antitranspose hcol)
  have hm : 2 ≤ (antitranspose χ.ω.E).card := hEATc
  by_cases hW : χ.ω.W.Nonempty
  · have hanti := hω.anti_of_column hW hcol
    obtain ⟨s, hsm⟩ := hanti.exists_isRowMark (u := u) hu hm
    have hcase : χ.ω.case = .b := by
      have h1 : χ.ω.case.anti = .a := hsm.2.2.2
      exact AttachCase.eq_b_of_anti_eq_a h1
    have hord : ¬ χ.ω.case.IsMixed := by simp [AttachCase.IsMixed, hcase]
    have hcomp : antitranspose (χ.ω.compose χ.D) = χ.ω.anti.compose χ.D :=
      MarkedInner.antitranspose_compose hord hDne
    obtain ⟨D', hD'c, hD's, hD'card, t, ht⟩ := hsm.exists_chart_of_cellSchur_eq hD
      (isSkew_antitranspose hH) (by rw [hAT]; exact congrArg cellSchur hcomp)
    have hord' : ¬ χ.ω.anti.case.IsMixed := by
      have : χ.ω.anti.case = .a := hsm.2.2.2
      rintro (h | h) <;> rw [this] at h <;> cases h
    refine ⟨⟨D', χ.ω⟩, ⟨hD'c, by change 2 ≤ D'.card; omega, hEc, hω⟩, rfl, hD's, atVec t, ?_⟩
    have h1 : H = antitranspose (SkewGluing.translate t (χ.ω.anti.compose D')) := by
      rw [← ht, antitranspose_antitranspose]
    rw [h1, antitranspose_translate, MarkedInner.antitranspose_compose hord' hD'c.2.1,
      MarkedInner.anti_anti]
    rfl
  · have hWe : χ.ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    have hemp : χ.ω.IsEmptyMark := by
      rcases hω.1.2 with h | h
      · exact h
      · exact (h.1.ne_empty hWe).elim
    have hωeq : χ.ω = emptyMarkH χ.ω.E := MarkedInner.eq_emptyMarkH hemp
    have hE' := emptyMarkH_isLegal hEAT
    obtain ⟨s, hsm⟩ := hE'.exists_isRowMark (u := u) hu hm
    set E := χ.ω.E with hEdef
    have hgauge : ∀ X : Diagram, X.Nonempty →
        (emptyMarkH E).compose X = (emptyMarkV E).compose (antitranspose X) :=
      fun X hX => compose_emptyMarks_antitranspose hX E
    have hVord : ¬ (emptyMarkV E).case.IsMixed := by simp [AttachCase.IsMixed, emptyMarkV]
    have hAT' : antitranspose χ.parent = (emptyMarkH (antitranspose E)).compose
        (antitranspose χ.D) := by
      have h1 : χ.parent = (emptyMarkH E).compose χ.D := by
        unfold Chart.parent; rw [← hωeq]
      rw [h1, hgauge _ hDne,
        MarkedInner.antitranspose_compose hVord
          (show (antitranspose χ.D).Nonempty from hDne.image _),
        emptyMarkV_anti hE]
    have hDAT : IsConnectedSkew (antitranspose χ.D) := isConnectedSkew_antitranspose hD
    obtain ⟨D'', hD''c, hD''s, hD''card, t, ht⟩ := hsm.exists_chart_of_cellSchur_eq hDAT
      (isSkew_antitranspose hH) (by rw [hAT, hAT'])
    have hHord : ¬ (emptyMarkH (antitranspose E)).case.IsMixed := by
      simp [AttachCase.IsMixed, emptyMarkH]
    have hD''ne : D''.Nonempty := hD''c.2.1
    have h1 : H = antitranspose (SkewGluing.translate t
        ((emptyMarkH (antitranspose E)).compose D'')) := by
      rw [← ht, antitranspose_antitranspose]
    have hD'' : (emptyMarkH E).compose (antitranspose D'') =
        (emptyMarkV E).compose D'' := by
      rw [hgauge _ (show (antitranspose D'').Nonempty from hD''ne.image _),
        antitranspose_antitranspose]
    refine ⟨⟨antitranspose D'', χ.ω⟩, ⟨isConnectedSkew_antitranspose hD''c, ?_, hEc, hω⟩, rfl,
      ?_, atVec t, ?_⟩
    · change 2 ≤ (antitranspose D'').card
      rw [card_antitranspose, hD''card, card_antitranspose]; exact hDc
    · change cellSchur (antitranspose D'') = cellSchur χ.D
      rw [cellSchur_antitranspose, hD''s, cellSchur_antitranspose, schurInvolution_involutive]
    · change H = SkewGluing.translate (atVec t) (χ.ω.compose (antitranspose D''))
      rw [h1, antitranspose_translate,
        MarkedInner.antitranspose_compose hHord hD''ne, hωeq, hD'', emptyMarkH_anti hEAT,
        antitranspose_antitranspose]

end Chart

/-- A line inner: the inner diagram lies in one row or in one column. -/
def LineInner (ω : MarkedInner) : Prop := IsRowDiagram ω.E ∨ IsColumnDiagram ω.E

namespace Chart

/-- **`lem:gluing-lines` (2), mates.**  Let `χ` be a proper legal chart with a line inner (a row
read horizontally, or a column).  Every skew diagram `H` with the function of the parent of `χ`
has a proper legal chart with the same marked inner and an outer with the function of `χ.D`. -/
theorem IsProperLegal.exists_chart_of_line {χ : Chart} (hχ : χ.IsProperLegal)
    (hline : LineInner χ.ω) {H : Diagram} (hH : IsSkew H)
    (hs : cellSchur H = cellSchur χ.parent) :
    ∃ χ' : Chart, χ'.IsProperLegal ∧ χ'.ω = χ.ω ∧ cellSchur χ'.D = cellSchur χ.D ∧
      χ'.IsChartOf H := by
  rcases hline with h | h
  · exact hχ.exists_chart_of_row h hH hs
  · exact hχ.exists_chart_of_column h hH hs

end Chart

/-! ### A line parent has a singleton Schur class -/

theorem eq_translate_of_row {F H : Diagram} (hF : IsConnectedSkew F) (hH : IsConnectedSkew H)
    (hFr : IsRowDiagram F) (hHr : IsRowDiagram H) (hc : H.card = F.card) :
    ∃ t, H = translate t F := by
  obtain ⟨u, hu⟩ := exists_translate_rowCells_of_isRow hF hFr
  obtain ⟨v, hv⟩ := exists_translate_rowCells_of_isRow hH hHr
  refine ⟨v - u, ?_⟩
  have e1 : translate (v - u) F = translate v (rowCells 0 (F.card : ℤ)) := by
    conv_lhs => rw [hu]
    rw [translate_translate]
    congr 1
    abel
  rw [e1, ← hc]
  exact hv

theorem isRowDiagram_of_numRows_eq_one {H : Diagram} (h : numRows H = 1) : IsRowDiagram H := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
  refine ⟨r, fun x hx => ?_⟩
  have : x.1 ∈ rowSet H := Finset.mem_image_of_mem _ hx
  rw [hr] at this
  exact Finset.mem_singleton.mp this

theorem numRows_eq_one_of_isRow {F : Diagram} (hF : F.Nonempty) (hFr : IsRowDiagram F) :
    numRows F = 1 := by
  obtain ⟨r, hr⟩ := hFr
  obtain ⟨x, hx⟩ := hF
  have : rowSet F = {r} := by
    ext a
    simp only [rowSet, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hr y hy
    · rintro rfl; exact ⟨x, hx, hr x hx⟩
  unfold numRows
  rw [this]; rfl

/-- **A connected skew diagram in a row has a singleton Schur class**: every skew diagram with
its function is a translate of it. -/
theorem eq_translate_of_cellSchur_eq_of_isRow {F H : Diagram} (hF : IsConnectedSkew F)
    (hFr : IsRowDiagram F) (hH : IsSkew H) (h : cellSchur H = cellSchur F) :
    ∃ t, H = translate t F := by
  have hHc := isConnectedSkew_of_cellSchur_eq hF hH h
  have hn := numRows_eq_of_cellSchur_eq hHc hF h
  rw [numRows_eq_one_of_isRow hF.2.1 hFr] at hn
  exact eq_translate_of_row hF hHc hFr (isRowDiagram_of_numRows_eq_one hn)
    (card_eq_of_cellSchur_eq hF hH h)

theorem isColumnDiagram_iff_transpose {E : Diagram} :
    IsColumnDiagram E ↔ IsRowDiagram (transpose E) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x hx => hc _ (mem_transpose.mp hx)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x hx => by
      have := hc x.swap (mem_transpose.mpr (by simpa using hx))
      simpa using this⟩

theorem transpose_translate (t : ℤ × ℤ) (D : Diagram) :
    transpose (translate t D) = translate t.swap (transpose D) := by
  ext y
  rw [mem_transpose, mem_translate, mem_translate, mem_transpose]
  rfl

/-- **A connected skew diagram in a column has a singleton Schur class.** -/
theorem eq_translate_of_cellSchur_eq_of_isColumn {F H : Diagram} (hF : IsConnectedSkew F)
    (hFc : IsColumnDiagram F) (hH : IsSkew H) (h : cellSchur H = cellSchur F) :
    ∃ t, H = translate t F := by
  have h' : cellSchur (transpose H) = cellSchur (transpose F) := by
    rw [cellSchur_transpose, cellSchur_transpose, h]
  obtain ⟨t, ht⟩ := eq_translate_of_cellSchur_eq_of_isRow (isConnectedSkew_transpose hF)
    (isColumnDiagram_iff_transpose.mp hFc) (isSkew_transpose hH) h'
  refine ⟨t.swap, ?_⟩
  have := congrArg transpose ht
  rw [transpose_transpose, transpose_translate, transpose_transpose] at this
  exact this

/-- **`lem:gluing-lines`, last sentence of the second assertion.**  A line parent (a connected skew
diagram in one row or one column) has a singleton Schur class. -/
theorem eq_translate_of_cellSchur_eq_of_isLine {F H : Diagram} (hF : IsConnectedSkew F)
    (hFl : IsRowDiagram F ∨ IsColumnDiagram F) (hH : IsSkew H) (h : cellSchur H = cellSchur F) :
    ∃ t, H = translate t F := by
  rcases hFl with h' | h'
  · exact eq_translate_of_cellSchur_eq_of_isRow hF h' hH h
  · exact eq_translate_of_cellSchur_eq_of_isColumn hF h' hH h

/-! ### Every fork at a diagram with a proper line inner glues -/

/-- **`lem:gluing-lines`, "every fork at that diagram glues".**  Let `Y` have a proper line chart
`χ`, and let `X`, `Z` be skew diagrams in the Schur class of `Y` (that is, vertices of the
common-factor graph of `def:gluing-graph` containing `Y`) that are not translates of one another.
Then `X` and `Z` have a common final factor, whatever charts witness the two edges of the fork.
**Differs from the paper's route.** The edges of the fork are not used; each of `X` and `Z` is
a mate of `Y`, so it has the marked inner of `χ` by `Chart.IsProperLegal.exists_chart_of_line`. -/
theorem HasCommonFinalFactor.of_line_inner {χ : Chart} {Y X Z : Diagram} (hχ : χ.IsProperLegal)
    (hline : LineInner χ.ω) (hY : χ.IsChartOf Y) (hX : IsSkew X) (hZ : IsSkew Z)
    (hXY : cellSchur X = cellSchur Y) (hZY : cellSchur Z = cellSchur Y)
    (hne : ¬ ∃ t, Z = translate t X) : HasCommonFinalFactor cellSchur X Z := by
  obtain ⟨t, ht⟩ := hY
  have hpar : cellSchur Y = cellSchur χ.parent := by rw [ht, cellSchur_translate]
  obtain ⟨χ₁, h₁, hω₁, hs₁, c₁⟩ := hχ.exists_chart_of_line hline hX (hXY.trans hpar)
  obtain ⟨χ₂, h₂, hω₂, hs₂, c₂⟩ := hχ.exists_chart_of_line hline hZ (hZY.trans hpar)
  refine ⟨hne, χ₁, χ₂, h₁, h₂, c₁, c₂, Or.inl ?_, by rw [hs₁, hs₂]⟩
  rw [hω₁, hω₂]
  exact MarkedInner.equivTranslate_refl _

/-- **`lem:gluing-lines`, "every fork at that diagram glues", in the graph.**  In the common-factor
graph `classGraph (skewClass P)`, if one vertex `y` has a proper line chart, any two distinct
vertices `x`, `z` are adjacent. -/
theorem classGraph_adj_of_line_inner {P : Lambda} {χ : Chart}
    {y x z : {F : Diagram // skewClass P F}}
    (hχ : χ.IsProperLegal) (hline : LineInner χ.ω) (hy : χ.IsChartOf y.1)
    (hxz : classOf x ≠ classOf z) : (classGraph (skewClass P)).Adj (classOf x) (classOf z) := by
  rw [classGraph_adj_iff]
  refine HasCommonFinalFactor.of_line_inner hχ hline hy x.2.1 z.2.1 ?_ ?_ ?_
  · rw [x.2.2, y.2.2]
  · rw [z.2.2, y.2.2]
  · rintro ⟨t, ht⟩
    exact hxz (classOf_eq_iff.mpr ⟨t, ht⟩)

end SkewGluing
