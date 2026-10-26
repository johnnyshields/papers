import SkewGluing.MinimalFibers.Score
import SkewGluing.MinimalFibers.Domination
import SkewGluing.MinimalFibers.LeastPeriod
import SkewGluing.MinimalFibers.Key
import SkewGluing.MinimalFibers.Nonminimal

/-!
# Source-minimal fibers

Formalizes `shields-2026-skew-gluing.tex`, «Source-minimal fibers» (`sec:minimal-fibers`).

* `sourceMinimalDomination` (`thm:source-minimal-domination`): the proposition
  `SourceMinimalDomination` on the concrete common-factor graph, from
  `Chart.IsSourceMinimal.fiber_subset` and `Chart.IsSourceMinimal.component_eq`.
* `componentKeyClassifies` (`prop:component-key`): the proposition `ComponentKeyClassifies`, from
  `Chart.IsSourceMinimal.key_eq` and `component_key_iff`.
* `eq:chart-score`: `Chart.IsProperLegal.score_eq`; `cor:least-root-period`: `least_root_period`,
  `Chart.IsSourceMinimal.period_dvd`, `row_seven_least_period`; the hook example and
  `lem:rotation-components`: `SkewGluing.CommonFactorGraph` and `rotation_components_unconditional`;
  the gauge example: `gauge_necessity`; `eq:nonminimal-fiber`: `NonminimalFiber.nonminimal_fiber`.

The Olson-Harris composition theorem is the hypothesis `hOH`, discharged by
`olsonHarrisComposition` in `SkewGluing.MainTheorems`.

Sorry-free.
-/

namespace SkewGluing

theorem classOf_mem_classVertices_fiberClass_iff {P : Lambda} {ω : MarkedInner} {Q : Lambda}
    (G : {F : Diagram // connectedClass P F}) :
    classOf G ∈ classVertices P (fiberClass cellSchur ω Q) ↔ G.1 ∈ fiberClass cellSchur ω Q := by
  constructor
  · rintro ⟨x, hx, hxS⟩
    obtain ⟨t, ht⟩ := classOf_eq_iff.mp hx
    rw [ht]
    exact fiberClass_translate_mem hxS t
  · exact fun h => ⟨G, rfl, h⟩

/-- **`thm:source-minimal-domination`.**  The statement `SourceMinimalDomination` on the concrete
common-factor graph: for a source-minimal chart `χ` of a connected diagram `F`, every proper-chart
fiber through `F` is contained in `𝓕_χ`, and the components of `F` in `Γ(P)` and `Γ⁺(P)` are
`𝓕_χ`.  The Olson-Harris composition theorem is `hOH`. -/
theorem sourceMinimalDomination (hOH : OlsonHarrisComposition) : SourceMinimalDomination := by
  intro P F χ hχ
  refine ⟨fun χ' h' c' => hχ.fiber_subset hOH h' c', fun G => ?_⟩
  obtain ⟨h1, h2⟩ := hχ.component_eq hOH F.2
  have e1 : G.1 ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) ↔
      classOf G ∈ ((classGraph (connectedClass P)).connectedComponentMk (classOf F)).supp := by
    rw [h1, classOf_mem_classVertices_fiberClass_iff]
  have e2 : G.1 ∈ fiberClass cellSchur χ.ω (cellSchur χ.D) ↔
      classOf G ∈ ((connectedRotationData P).augmented.connectedComponentMk (classOf F)).supp := by
    rw [h2, classOf_mem_classVertices_fiberClass_iff]
  refine ⟨?_, ?_⟩
  · rw [e1, SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · rw [e2, SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **`prop:component-key`.**  The statement `ComponentKeyClassifies` on the concrete graph: the key
is independent of the source-minimal chart, and for rooted diagrams of one connected Schur class,
equal keys are exactly the same component of `Γ(P)`.  The Olson-Harris composition theorem is
`hOH`. -/
theorem componentKeyClassifies (hOH : OlsonHarrisComposition) : ComponentKeyClassifies := by
  refine ⟨fun F _ χ χ' h h' => h.key_eq h', fun P F H hF hH => ?_⟩
  constructor
  · rintro ⟨χ, χ', h, h', hk⟩
    exact (component_key_iff hOH F.2 H.2 h h').mp hk
  · intro hr
    obtain ⟨χ, h⟩ := exists_isSourceMinimal_of_rooted hF
    obtain ⟨χ', h'⟩ := exists_isSourceMinimal_of_rooted hH
    exact ⟨χ, χ', h, h', (component_key_iff hOH F.2 H.2 h h').mpr hr⟩

end SkewGluing
