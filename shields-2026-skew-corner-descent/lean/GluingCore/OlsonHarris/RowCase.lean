/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OlsonHarris/RowCase.lean`. -/
import GluingCore.RowInner
import GluingCore.OlsonHarris.Rotation

/-!
# Composition with a row inner respects Schur-equality

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`), the composition statement of Olson-Harris for the marked
inners whose underlying diagram is a row, together with `lem:gluing-row-action` and
`lem:gluing-row-transport`.

For a row inner `ω_{q,w}` the composite `ω_{q,w}.compose D` is the cell diagram of the lifted
profile `𝓛_{q,w}` (`GluingCore.RowInner`), and `𝓛_{q,w}` preserves Schur-equality
(`Profile.schur_lift_eq_iff`, resting on `reinerRowInvariants`).  So this special case of the
composition statement is proved outright, without the Olson-Harris input.

Sorry-free.
-/

namespace GluingCore

/-- **The composition statement for the row marks `ω_{q,w}`.**  For connected `D`, `D'` with the
same Schur function, the composites `D ∘_{ω_{q,w}} E` and `D' ∘_{ω_{q,w}} E` have the same Schur
function. -/
theorem cellSchur_rowMark_compose_eq (s : RowShift) {D D' : Diagram} (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur ((rowMark s).compose D) = cellSchur ((rowMark s).compose D') := by
  obtain ⟨v, hv⟩ := rowMark_compose_eq_liftCells s hD
  obtain ⟨v', hv'⟩ := rowMark_compose_eq_liftCells s hD'
  rw [hv, hv', cellSchur_translate, cellSchur_translate]
  exact cellSchur_liftCells_eq s hD hD' h

/-- **The composition statement for every legal mark on a row of at least two cells**, placed
anywhere: such a mark is a translate of `ω_{q,w}` (`lem:gluing-row-action`). -/
theorem cellSchur_compose_eq_of_row {ω : MarkedInner} (hω : ω.IsLegal) {u : ℤ × ℤ} {m : ℕ}
    (hE : ω.E = translate u (rowCells 0 m)) (hm : 2 ≤ m) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') := by
  obtain ⟨s, hs⟩ := hω.exists_isRowMark hE hm
  rw [hs.compose hD.2.1, hs.compose hD'.2.1, cellSchur_translate, cellSchur_translate]
  exact cellSchur_rowMark_compose_eq s hD hD' h

end GluingCore
