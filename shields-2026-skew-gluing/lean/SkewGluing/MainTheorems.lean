import SkewGluing.OlsonHarris
import SkewGluing.Divisible
import SkewGluing.Gluing
import SkewGluing.MinimalFibers
import SkewGluing.NecessityReduction

/-!
# The main theorems, unconditionally

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`,
`thm:gluing`, `prop:gluing-divisible`), «Source-minimal fibers» (`sec:minimal-fibers`,
`lem:rotation-components`, `thm:source-minimal-domination`, `prop:component-key`,
`eq:nonminimal-fiber`) and «Reduction of composition necessity» (`sec:necessity-reduction`,
`thm:connectivity-reduction`, `thm:necessity-reduction`).

The modules proving these results take the Olson-Harris composition theorem (Thms. 5.3.9 and
5.3.10 of `OlsonHarris2024HopfApplications`) as an explicit hypothesis `hOH`, and the reduction
theorems take `thm:gluing`, `thm:source-minimal-domination` and `prop:component-key` as
hypotheses.  Here each is discharged by the theorem that proves it — the composition theorem by
`olsonHarrisComposition` (`SkewGluing.OlsonHarris`) — so the statements below carry only the
paper's own parameters.

Sorry-free.
-/

namespace SkewGluing

/-- The composition and reversal statements in the shape `prop:gluing-divisible` consumes. -/
theorem olsonHarris_compose_and_reverse (ω : MarkedInner) (hω : ω.IsLegal) (D D' : Diagram)
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') ∧
      cellSchur (ω.rotate.compose D) = cellSchur (ω.compose D') :=
  ⟨cellSchur_compose_eq hω hD hD' h, (cellSchur_compose_eq_rotate_compose hω hD' hD h.symm).symm⟩

/-- **`thm:gluing` (Local common-factor gluing).**  Every connected component of every
common-factor graph is a clique. -/
theorem gluing : GluingStatement :=
  gluingStatement olsonHarrisComposition

/-- **`thm:gluing`, the fork form.**  If `X, Y` and `Y, Z` have a common final factor, then so do
`X, Z`. -/
theorem gluing_fork_of_edges {X Y Z : Diagram} (hX : IsSkew X) (hZ : IsSkew Z)
    (hXY : cellSchur X = cellSchur Y) (hZY : cellSchur Z = cellSchur Y)
    (hxy : HasCommonFinalFactor cellSchur X Y) (hyz : HasCommonFinalFactor cellSchur Y Z)
    (hne : ¬ ∃ t, Z = translate t X) : HasCommonFinalFactor cellSchur X Z :=
  gluing_fork olsonHarrisComposition hX hZ hXY hZY hxy hyz hne

/-- **`prop:gluing-divisible`.**  For proper legal charts `F = D ∘_ω E = C ∘_η B` of periods
`q < Q` with `q ∣ Q`, the coarse inner factors through the fine one, the coarse chart
reassociates, and its fiber is contained in the fine chart's fiber. -/
theorem gluing_divisible {F : Diagram} {χ₁ χ₂ : Chart} (h₁ : χ₁.IsProperLegal)
    (h₂ : χ₂.IsProperLegal) (hF₁ : χ₁.IsChartOf F) (hF₂ : χ₂.IsChartOf F)
    (hlt : χ₁.period < χ₂.period) (hdiv : χ₁.period ∣ χ₂.period) :
    ∃ (V : Diagram) (t : ℤ × ℤ), IsConnectedSkew V ∧ 2 ≤ V.card ∧
      χ₂.ω.E = SkewGluing.translate t (χ₁.ω.compose V) ∧
      (∃ (μ : MarkedInner) (γ : Diagram → Diagram),
        MarkedInner.IsReassociation (χ₁.ω.translate t) χ₂.ω V μ γ) ∧
      fiberClass cellSchur χ₂.ω (cellSchur χ₂.D) ⊆
        fiberClass cellSchur χ₁.ω (cellSchur χ₁.D) :=
  MarkedInner.divisible olsonHarris_compose_and_reverse h₁ h₂ hF₁ hF₂ hlt hdiv

/-- **`lem:rotation-components`.**  Every component of the rotation-augmented and of the
rotation-quotiented common-factor graph is a clique, and rotation augmentation changes no rooted
component. -/
theorem rotation_components_cliques (P : Lambda) :
    ComponentsAreCliques (connectedRotationData P).augmented ∧
    ComponentsAreCliques (connectedRotationData P).quotientGraph ∧
    ∀ a ∈ (connectedRotationData P).rooted,
      ((connectedRotationData P).augmented.connectedComponentMk a).supp =
        ((connectedRotationData P).graph.connectedComponentMk a).supp :=
  rotation_components_unconditional olsonHarrisComposition P

/-- **`thm:source-minimal-domination`.** -/
theorem source_minimal_domination : SourceMinimalDomination :=
  sourceMinimalDomination olsonHarrisComposition

/-- **`prop:component-key`.** -/
theorem component_key : ComponentKeyClassifies :=
  componentKeyClassifies olsonHarrisComposition

/-- **`thm:connectivity-reduction`.**  For a nonempty connected Schur class, the augmented graph
is connected, iff the quotient graph is, iff every nonrotation pair has a common final factor, iff
(TR) and (RI) hold. -/
theorem connectivity_reduction_class (P : Lambda) (hP : ∃ F, connectedClass P F) :
    List.TFAE
      [ (connectedRotationData P).augmented.Connected,
        (connectedRotationData P).quotientGraph.Connected,
        ∀ F G : Diagram, connectedClass P F → connectedClass P G → ¬ RotationMates F G →
          HasCommonFinalFactor cellSchur F G,
        TerminalRigidity P ∧ RootedKeyInvariance P ] :=
  connectivity_reduction gluing component_key P hP

/-- **`thm:necessity-reduction`.**  Composition-and-reversal necessity, (TR) ∧ (RI) in every
connected Schur class, and exhaustion of every class by the reversal family of every complete
source-minimal tower are equivalent. -/
theorem necessity_reduction_tfae :
    List.TFAE [CommonPresentations, TerminalRigidityAndKeyInvariance, TowersExhaustClasses] :=
  necessity_reduction olsonHarrisComposition gluing source_minimal_domination component_key

/-- **The nonminimal fiber (`eq:nonminimal-fiber`).**  `X` and `Y` lie in one fine fiber, are
Schur-equal and share a common final factor, while `X` lies outside the coarse fiber of `Y`. -/
theorem nonminimal_fiber_example :
    NonminimalFiber.X ∈ fiber cellSchur NonminimalFiber.ω (cellSchur NonminimalFiber.D) ∧
      NonminimalFiber.Y ∈ fiber cellSchur NonminimalFiber.ω (cellSchur NonminimalFiber.D) ∧
      cellSchur NonminimalFiber.X = cellSchur NonminimalFiber.Y ∧
      HasCommonFinalFactor cellSchur NonminimalFiber.X NonminimalFiber.Y ∧
      NonminimalFiber.X ∉ fiberClass cellSchur NonminimalFiber.η (cellSchur NonminimalFiber.H) ∧
      NonminimalFiber.Y ∈ fiberClass cellSchur NonminimalFiber.η (cellSchur NonminimalFiber.H) :=
  NonminimalFiber.nonminimal_fiber olsonHarrisComposition

end SkewGluing
