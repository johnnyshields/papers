import SkewGluing.NecessityReduction.Statements
import SkewGluing.NecessityReduction.Presentation
import SkewGluing.NecessityReduction.Connectivity
import SkewGluing.NecessityReduction.Reduction
import SkewGluing.NecessityReduction.Examples

/-!
# Reduction of composition necessity

Formalizes `shields-2026-skew-gluing.tex`, «Reduction of composition necessity»
(`sec:necessity-reduction`, `thm:connectivity-reduction`, `thm:necessity-reduction`).

* `NecessityReduction/Statements.lean`: `GluingStatement` (`thm:gluing`), the chart score
  (`eq:chart-score`), source-minimal charts, the component key (`eq:component-key`),
  `SourceMinimalDomination` (`thm:source-minimal-domination`), `ComponentKeyClassifies`
  (`prop:component-key`), and (TR), (RI) on a connected Schur class.
* `NecessityReduction/Presentation.lean`: left-associated composition presentations,
  correspondence up to transported rotation, complete source-minimal towers and their existence,
  reversal families, forward composition and reversal along corresponding presentations.
* `NecessityReduction/Connectivity.lean`: `thm:connectivity-reduction` on the concrete connected
  Schur class, and the remark after it.
* `NecessityReduction/Reduction.lean`: `thm:necessity-reduction`, all three implications.
* `NecessityReduction/Examples.lean`: checks on the paper's examples.

The hypotheses taken are `OlsonHarrisComposition`, `GluingStatement`,
`SourceMinimalDomination` and `ComponentKeyClassifies`; `SkewGluing.MainTheorems` discharges
them by `olsonHarrisComposition`, `gluing`, `source_minimal_domination` and `component_key`.

Sorry-free.
-/
