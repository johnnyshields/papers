import SkewGluing.OlsonHarris.Cited
import SkewGluing.OlsonHarris.Rotation

/-!
# Reversal and fibers from the composition theorem

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`, and the paragraph on the fiber `𝓕(ω, Q)`): the reversal
statement of Olson-Harris (Thm. 5.3.10, the part the paper uses) and the assertion that every
fiber `𝓕(ω, Q)` lies in one Schur class, as consequences of `OlsonHarrisComposition`.

The reversal follows the route of the source: `(D ∘_ω E)* = D* ∘_{ω*} E*`
(`MarkedInner.rotate_compose`), `s_X = s_{X*}`, and composition for the rotated inner
`ω*`, which is legal (`MarkedInner.isLegal_rotate`).

The statements take the hypothesis `hOH : OlsonHarrisComposition`, discharged by
`olsonHarrisComposition` (`SkewGluing.OlsonHarris.Frontier`).

Sorry-free.
-/

namespace SkewGluing

namespace OlsonHarrisComposition

variable (hOH : OlsonHarrisComposition)

include hOH

/-- **Reversal (Olson-Harris, Thm. 5.3.10, the part the paper uses).**  For a legal marked inner
`ω` and connected outers `D`, `D'` with `s_D = s_{D'}`, the composite `D ∘_ω E` and the composite
`D' ∘_{ω*} E*` with the rotated inner have the same Schur function. -/
theorem compose_eq_rotate_compose {ω : MarkedInner} (hω : ω.IsLegal) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.rotate.compose D') := by
  rw [MarkedInner.cellSchur_compose_rotate_outer hD.2.1]
  exact hOH _ (MarkedInner.isLegal_rotate hω) _ _ (isConnectedSkew_rotate_iff.mpr hD) hD'
    (by rw [cellSchur_rotate, h])

/-- **Every member of a fiber `𝓕(ω, Q)` has the same Schur function.** -/
theorem fiber_eq {ω : MarkedInner} (hω : ω.IsLegal) {Q : Lambda} {F F' : Diagram}
    (hF : F ∈ fiber cellSchur ω Q) (hF' : F' ∈ fiber cellSchur ω Q) :
    cellSchur F = cellSchur F' := by
  obtain ⟨A, hA, -, hAQ, rfl | rfl⟩ := hF <;> obtain ⟨A', hA', -, hA'Q, rfl | rfl⟩ := hF' <;>
    have h : cellSchur A = cellSchur A' := by rw [hAQ, hA'Q]
  · exact hOH ω hω A A' hA hA' h
  · exact hOH.compose_eq_rotate_compose hω hA hA' h
  · exact (hOH.compose_eq_rotate_compose hω hA' hA h.symm).symm
  · exact hOH _ (MarkedInner.isLegal_rotate hω) A A' hA hA' h

/-- A fiber lies in a single Schur class: there is a function `P` that all its members share. -/
theorem exists_cellSchur_of_fiber {ω : MarkedInner} (hω : ω.IsLegal) {Q : Lambda} :
    ∃ P : Lambda, ∀ F ∈ fiber cellSchur ω Q, cellSchur F = P := by
  by_cases hne : (fiber cellSchur ω Q).Nonempty
  · obtain ⟨F₀, hF₀⟩ := hne
    exact ⟨cellSchur F₀, fun F hF => hOH.fiber_eq hω hF hF₀⟩
  · exact ⟨0, fun F hF => absurd ⟨F, hF⟩ hne⟩

end OlsonHarrisComposition

end SkewGluing
