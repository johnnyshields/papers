/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Lines/ColumnMates.lean`. -/
import GluingCore.Antitranspose
import GluingCore.Lines.Rows

/-!
# Antitransposition of a marked inner whose diagram is a column

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`), second assertion, the column case.

For a legal mark `ω` with a nonempty copy whose diagram `E` lies in one column, the antitransposed
mark `ω.anti` is legal and lives on a row, hence is a row mark `ω_{q,w}`
(`MarkedInner.IsLegal.exists_isRowMark`).  Only the well-formedness, II and III of `ω.anti` come
from `ω`; I and IV hold on a row for any data (`isMaximal_of_row`, `noHatAdjacency_of_row`).

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

/-- Condition I holds on a row: the marked copy contains every cell of its contents. -/
theorem isMaximal_of_row {ω : MarkedInner} (hrow : IsRowDiagram ω.E) (hWE : ω.W ⊆ ω.E) :
    ω.IsMaximal := by
  obtain ⟨r, hr⟩ := hrow
  intro W' hW' hlt _ hc x hx
  exfalso
  have hsub : W' ⊆ ω.E := Finset.mem_powerset.mp hW'
  have hW : W' ⊆ ω.W := by
    intro y hy
    have h1 : content y ∈ contents W' := content_mem_contents hy
    rw [hc] at h1
    obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp h1
    have hzr := hr z (hWE hz)
    have hyr := hr y (hsub hy)
    have : y = z := by
      obtain ⟨a, b⟩ := y
      obtain ⟨c, d⟩ := z
      simp only [content] at hzc
      simp only at hzr hyr
      ext <;> simp <;> omega
    rw [this]; exact hz
  exact absurd hW (not_subset_of_ssubset hlt)

/-- Condition IV holds on a row: the hatted middle is empty. -/
theorem noHatAdjacency_of_row {ω : MarkedInner} (hrow : IsRowDiagram ω.E) :
    ω.NoHatAdjacency := by
  obtain ⟨r, hr⟩ := hrow
  intro k m x hx
  exfalso
  obtain ⟨hx1, hx2⟩ := hx
  have row : ∀ y ∈ GluingCore.translate (k • ω.v) ω.middle, y.1 = r + (k • ω.v).1 := by
    intro y hy
    have := hr _ (Finset.mem_sdiff.mp (mem_translate.mp hy)).1
    simp only [Prod.fst_sub] at this
    omega
  have h1 := row x hx1
  have h2 := row (x + eCell) hx2
  simp only [Prod.fst_add, eCell] at h2
  omega

/-- Antitransposition preserves legality of a nonempty mark on a column. -/
theorem IsLegal.anti_of_column {ω : MarkedInner} (hω : ω.IsLegal) (hW : ω.W.Nonempty)
    (hcol : IsColumnDiagram ω.E) : ω.anti.IsLegal := by
  obtain ⟨⟨hE, hm⟩, hI, hII, hIII, hIV⟩ := hω
  have hnon : ω.IsNonemptyMark := by
    rcases hm with h | h
    · exact absurd h.1 hW.ne_empty
    · exact h
  have hrow : IsRowDiagram ω.anti.E := by
    obtain ⟨c, hc⟩ := hcol
    refine ⟨-c, fun x hx => ?_⟩
    have := hc _ (mem_antitranspose'.mp hx)
    simp only [atVec] at this
    omega
  have hWE : ω.anti.W ⊆ ω.anti.E := antitranspose_subset hnon.2.2.1
  exact ⟨⟨isConnectedSkew_antitranspose hE, Or.inr (isNonemptyMark_anti hE hnon)⟩,
    isMaximal_of_row hrow hWE, isNarrow_anti hII, removalsConnected_anti hIII,
    noHatAdjacency_of_row hrow⟩

end MarkedInner

end GluingCore
