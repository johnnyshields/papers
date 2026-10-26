-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem.lean
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.RightFinal
import GluingCore.OlsonHarris.Plan.CornerCase.Crem.LeftFinal

/-!
# The remainder after removing a lifted key ribbon: the proof of `corner_lift_remainder`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.5.8
(`OlsonHarris2024HopfApplications`), for a legal mark `ω` of case (c) and a connected outer `D`.

For a ribbon `A` of size `m` removable on the right (respectively on the left) from `D`, with
the lift `Ã = cornerLift ω D m s A` (respectively `cornerLift ω D m t A`) of `A` to a border strip
of `F = D ∘_ω E`, the diagram `F \ Ã` is the edge-disjoint union of `(D \ A) ∘_ω E` (as the
union of the composites of the components of `D \ A`) and of single copies of `\overline O`,
`W`, `\overline W`, one for each diagonal, row and column of `D` that `A` removes
(`Rem.right_decomp`, `Rem.left_decomp`); the pieces lie on diagonals at distance at least `2` from
one another (`Rem.right_sep_*`, `Rem.left_sep_*`), so `s_{F \ Ã}` is the product of their
functions, and the counts of the pieces are the numbers of lost diagonals, rows and columns
(`Rem.card_rLone`, …).

Everything is proved on the cells: the cells of a composite on a diagonal are computed in
`Rem.mem_compose_c`, the border strip `Ã` as the last cells of a window of diagonals, and the
identity of the cells of `F \ Ã` is reduced to integer arithmetic (`Rem.right_arith`,
`Rem.left_arith`).

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

open MarkedInner

/-- A legal mark of case (c) has a nonempty mark. -/
theorem Rem.isLegalNonempty_of_case_c {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ω.IsLegalNonempty := by
  refine ⟨hω, ?_⟩
  rcases hω.1.2 with h | h
  · have := h.2.2
    rw [hc] at this
    cases this
  · exact h.1

/-- **Thesis Lemma 5.5.8: the remainder after removing a lifted key ribbon.**  For a ribbon `A`
of size `m` removable on the right (offset `s`) or on the left (offset `t`) from the connected
outer `D`, `F \ Ã` is the edge-disjoint union of `(D \ A) ∘_ω E`, a copy of `\overline O`, and
copies of `\overline W` and `W`, so
`s_{F \ Ã} = s_W^{row D - row (D \ A)} s_{\overline W}^{col D - col (D \ A)}
s_{\overline O}^{dia D - dia (D \ A)} ∏_C s_{C ∘_ω E}`, the product over the edge components `C`
of `D \ A`.

**Differs from the paper's route.** The thesis removes one box of `A` at a time and follows the
overlaps of neighboring copies of `E`; here the cells of `F \ Ã` are computed on every diagonal of
`F` at once, so that no iteration over the boxes of `A` is needed. -/
theorem corner_lift_remainder_proof {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .c) :
    ∀ D : Diagram, IsConnectedSkew D → ∀ m : ℕ, 0 < m → ∀ s t : ℤ, ω.IsPhases s t →
      (∀ A ∈ rightRibbons D m,
        cellSchur (ω.compose D \ cornerLift ω D m s A) =
          cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
            cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
              cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) * compSchur ω (D \ A)) ∧
      (∀ A ∈ leftRibbons D m,
        cellSchur (ω.compose D \ cornerLift ω D m t A) =
          cellSchur ω.W ^ (numRows D - numRows (D \ A)) *
            cellSchur (hatMarkFin ω) ^ (numCols D - numCols (D \ A)) *
              cellSchur (hatMiddleFin ω) ^ (span D - span (D \ A)) * compSchur ω (D \ A)) := by
  intro D hD m hm s t hph
  have hl := Rem.isLegalNonempty_of_case_c hω hc
  exact ⟨fun A hA => Rem.right_remainder hl hc hph hD hm hA,
    fun A hA => Rem.left_remainder hl hc hph hD hm hA⟩

end Corner

end Plan

end GluingCore
