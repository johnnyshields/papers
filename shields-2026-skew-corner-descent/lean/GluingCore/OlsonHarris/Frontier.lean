/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OlsonHarris/Frontier.lean`. -/
import GluingCore.OlsonHarris.Cited
import GluingCore.OlsonHarris.Rotation
import GluingCore.OlsonHarris.Plan.Assemble

/-!
# The Olson-Harris composition theorem

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the composition theorem of Olson-Harris, Thm. 5.3.9 of
`OlsonHarris2024HopfApplications`, in the cell form of `MarkedInner.compose`
(`OlsonHarrisComposition`).

For a legal marked inner `ω` (conditions I–IV) and connected outers `D`, `D'` with
`s_D = s_{D'}`, the composites `D ∘_ω E` and `D' ∘_ω E` have the same Schur function.  The proof
of the ordinary cases (a), (b) and of the corner case (c) is
`GluingCore.OlsonHarris.Plan.Assemble`, from the results of the `Plan` modules; case (d)
follows from case (c) by rotation.  The theorem is `olsonHarrisComposition`.

Sorry-free.
-/

namespace GluingCore

/-- **Olson-Harris, Thm. 5.3.9, ordinary marks (edge shapes).**  For a legal marked inner of
case (a) or (b) and connected outers `D`, `D'` with `s_D = s_{D'}`, the composites have the same
Schur function.

Proved by `Plan.cellSchur_compose_eq_of_ordinary_plan`.  The case of a row inner is also
proved outright in `GluingCore.OlsonHarris.RowCase`. -/
theorem cellSchur_compose_eq_of_ordinary {ω : MarkedInner} (hω : ω.IsLegal)
    (hcase : ω.case = .a ∨ ω.case = .b) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') := by
  exact Plan.cellSchur_compose_eq_of_ordinary_plan hω hcase hD hD' h

/-- **Olson-Harris, Thm. 5.3.9, the corner case (c).**  For a legal marked inner of case (c)
(lower attachment horizontal, upper attachment vertical) and connected outers `D`, `D'` with
`s_D = s_{D'}`, the composites have the same Schur function.

Proved by `Plan.cellSchur_compose_eq_of_case_c_plan`. -/
theorem cellSchur_compose_eq_of_case_c {ω : MarkedInner} (hω : ω.IsLegal)
    (hcase : ω.case = .c) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') :=
  Plan.cellSchur_compose_eq_of_case_c_plan hω hcase hD hD' h

/-- Composition for the corner case (d), from case (c) by rotation. -/
theorem cellSchur_compose_eq_of_case_d {ω : MarkedInner} (hω : ω.IsLegal)
    (hcase : ω.case = .d) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') := by
  have hωr : ω.rotate.IsLegal := MarkedInner.isLegal_rotate hω
  have hcr : ω.rotate.case = .c := by
    simp [MarkedInner.rotate, hcase, AttachCase.rotate]
  rw [MarkedInner.cellSchur_compose_rotate_outer hD.2.1,
    MarkedInner.cellSchur_compose_rotate_outer hD'.2.1]
  exact cellSchur_compose_eq_of_case_c hωr hcr (isConnectedSkew_rotate_iff.mpr hD)
    (isConnectedSkew_rotate_iff.mpr hD') (by rw [cellSchur_rotate, cellSchur_rotate, h])

/-- **The composition theorem of Olson-Harris** (`OlsonHarrisComposition`), assembled from the
ordinary and corner cases. -/
theorem olsonHarrisComposition : OlsonHarrisComposition := by
  intro ω hω D D' hD hD' h
  cases hc : ω.case
  · exact cellSchur_compose_eq_of_ordinary hω (Or.inl hc) hD hD' h
  · exact cellSchur_compose_eq_of_ordinary hω (Or.inr hc) hD hD' h
  · exact cellSchur_compose_eq_of_case_c hω hc hD hD' h
  · exact cellSchur_compose_eq_of_case_d hω hc hD hD' h

end GluingCore
