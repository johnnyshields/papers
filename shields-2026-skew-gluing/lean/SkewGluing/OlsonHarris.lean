import SkewGluing.OlsonHarris.Cited
import SkewGluing.OlsonHarris.Deductions
import SkewGluing.OlsonHarris.FiberClique
import SkewGluing.OlsonHarris.Frontier
import SkewGluing.OlsonHarris.Rotation
import SkewGluing.OlsonHarris.RowCase

/-!
# Olson-Harris composition and reversal for legal marked inners

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`, and the paragraph on the fiber `𝓕(ω, Q)`): the composition
and reversal theorems of Olson-Harris under Hypotheses I–IV
(`OlsonHarris2024HopfApplications`, Thms. 5.3.9 and 5.3.10), which the paper consumes in
`prop:gluing-divisible`, `lem:rotation-components` and `thm:necessity-reduction`.

## Statements

For a legal marked inner `ω` (`MarkedInner.IsLegal`) and connected outers `D`, `D'`:

* `cellSchur_compose_eq` (composition): `s_D = s_{D'}` gives
  `s_{ω.compose D} = s_{ω.compose D'}`.
* `cellSchur_compose_eq_rotate_compose` (reversal): `s_D = s_{D'}` gives
  `s_{ω.compose D} = s_{ω.rotate.compose D'}`.
* `fiber_cellSchur_eq` and `exists_cellSchur_of_fiber`: every member of the fiber
  `fiber cellSchur ω Q` has the same Schur function, so the fiber lies in one Schur class and
  is a clique of the common-factor graph.
* `fiber_hasCommonFinalFactor` (`OlsonHarris.FiberClique`): two members of a fiber that are not
  translates of each other have a common final factor.  This part does not use the
  Olson-Harris input.

The unconditional forms here are the forms of `OlsonHarris.Deductions` (hypothesis
`OlsonHarrisComposition`) applied to `olsonHarrisComposition` of `OlsonHarris.Frontier`, which
proves that proposition.  A development that prefers to carry the composition theorem as a
hypothesis uses `OlsonHarrisComposition.compose_eq_rotate_compose` and
`OlsonHarrisComposition.fiber_eq`.

## Route and status

The route is the Hopf-algebraic one of the source (shape Hopf algebra, the two actions of `Sym`
on it, Murnaghan–Nakayama for a single power sum, ribbons removable from `D ∘ E`); the
alternative of McNamara–van Willigenburg through the Hamel–Goulden identity needs Hypothesis V,
which is not assumed.  A purely determinantal route does not exist: the Jacobi–Trudi type
identity for the composite is itself a consequence of the theorem.  The ingredients are proved
in the modules of `OlsonHarris.Plan`, assembled in `OlsonHarris.Plan.Assemble`, and combined with
the case split in `OlsonHarris.Frontier`.

| Step | Where |
|---|---|
| rotation `(D ∘_ω E)* = D* ∘_{ω*} E*` | `Invariance` (`rotate_compose`) |
| reversal and fiber from composition | `Deductions` |
| composition, ordinary marks (a), (b) and corner mark (c) | `Plan.Assemble` |
| composition for case (d) from case (c) by rotation | `Frontier` |
| each fiber is a clique | `FiberClique` (no composition theorem needed) |
| composition for a row inner `ω_{q,w}` | `RowCase` (profile lift, row invariants) |

Sorry-free.
-/

namespace SkewGluing

/-- **Composition (Olson-Harris, Thm. 5.3.9).**  For a legal marked inner `ω` and connected
outers `D`, `D'` with `s_D = s_{D'}`, the composites `D ∘_ω E` and `D' ∘_ω E` have the same
Schur function. -/
theorem cellSchur_compose_eq {ω : MarkedInner} (hω : ω.IsLegal) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') :=
  olsonHarrisComposition ω hω D D' hD hD' h

/-- **Reversal (Olson-Harris, Thm. 5.3.10, the part the paper uses).**  For a legal marked inner
`ω` and connected outers `D`, `D'` with `s_D = s_{D'}`, the composite `D ∘_ω E` and the composite
`D' ∘_{ω*} E*` with the rotated inner have the same Schur function. -/
theorem cellSchur_compose_eq_rotate_compose {ω : MarkedInner} (hω : ω.IsLegal) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.rotate.compose D') :=
  olsonHarrisComposition.compose_eq_rotate_compose hω hD hD' h

/-- **Every member of a fiber `𝓕(ω, Q)` has the same Schur function.** -/
theorem fiber_cellSchur_eq {ω : MarkedInner} (hω : ω.IsLegal) {Q : Lambda} {F F' : Diagram}
    (hF : F ∈ fiber cellSchur ω Q) (hF' : F' ∈ fiber cellSchur ω Q) :
    cellSchur F = cellSchur F' :=
  olsonHarrisComposition.fiber_eq hω hF hF'

/-- A fiber lies in a single Schur class: there is a function `P` that all its members share. -/
theorem exists_cellSchur_of_fiber {ω : MarkedInner} (hω : ω.IsLegal) {Q : Lambda} :
    ∃ P : Lambda, ∀ F ∈ fiber cellSchur ω Q, cellSchur F = P :=
  olsonHarrisComposition.exists_cellSchur_of_fiber hω

/-- **A fiber is a clique inside one Schur class.**  For a legal marked inner `ω` with
`|E| ≥ 2`, all members of `𝓕(ω, Q)` have one Schur function `P`, and two of them that are not
translates of one another have a common final factor. -/
theorem fiber_isClique {ω : MarkedInner} (hω : ω.IsLegal) (hE : 2 ≤ ω.E.card) {Q : Lambda} :
    ∃ P : Lambda, (∀ F ∈ fiber cellSchur ω Q, cellSchur F = P) ∧
      ∀ F ∈ fiber cellSchur ω Q, ∀ F' ∈ fiber cellSchur ω Q, (¬ ∃ t, F' = translate t F) →
        HasCommonFinalFactor cellSchur F F' := by
  obtain ⟨P, hP⟩ := exists_cellSchur_of_fiber (Q := Q) hω
  exact ⟨P, hP, fun F hF F' hF' hne => fiber_hasCommonFinalFactor hω hE hF hF' hne⟩

end SkewGluing
