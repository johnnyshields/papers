import SkewGluing.MainTheorems
import SkewGluing.AntitransposeMixed
import SkewGluing.FoldSupplied
import SkewGluing.FoldSupplied.HypAnti
import SkewGluing.FoldSupplied.HypOrdinary
import SkewGluing.FoldSupplied.HypEmpty
import SkewGluing.FoldSupplied.HypMixed
import SkewGluing.Decoder
import SkewGluing.CellCriterion

/-!
# Axiom guard

Formalizes `shields-2026-skew-gluing.tex`, «Introduction» (`sec:introduction`): the
check that every headline declaration of the development depends only on the three standard
axioms `propext`, `Classical.choice` and `Quot.sound`, so that none rests on `sorryAx`, on an
added `axiom`, or on `Lean.ofReduceBool`.

Each `#guard_msgs in #print axioms X` below fails the build if the axioms of `X` change.  The
guarded declarations are the theorems of `SkewGluing.MainTheorems` and the main declaration of
every lemma, proposition, corollary and theorem of the paper, together with the declarations
that discharge the literature inputs (`reinerRowInvariants`, `barekatIrreducibility`,
`schurInvolution_schur_transpose`, `aeval_cellSchur_skewDiagram_all`) and the Olson-Harris
composition theorem (`olsonHarrisComposition`).

This module is not imported by the root `SkewGluing`.

Sorry-free.
-/

-- `thm:gluing`
/-- info: 'SkewGluing.gluing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.gluing

-- `thm:gluing` (fork form)
/-- info: 'SkewGluing.gluing_fork_of_edges' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.gluing_fork_of_edges

-- `prop:gluing-divisible`
/-- info: 'SkewGluing.gluing_divisible' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.gluing_divisible

-- `lem:rotation-components`
/-- info: 'SkewGluing.rotation_components_cliques' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.rotation_components_cliques

-- `thm:source-minimal-domination`
/-- info: 'SkewGluing.source_minimal_domination' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.source_minimal_domination

-- `prop:component-key`
/-- info: 'SkewGluing.component_key' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.component_key

-- `thm:connectivity-reduction`
/-- info: 'SkewGluing.connectivity_reduction_class' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.connectivity_reduction_class

-- `thm:necessity-reduction`
/-- info: 'SkewGluing.necessity_reduction_tfae' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.necessity_reduction_tfae

-- `eq:nonminimal-fiber`
/-- info: 'SkewGluing.nonminimal_fiber_example' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.nonminimal_fiber_example

-- composition and reversal (Olson-Harris, as consumed by `prop:gluing-divisible`)
/-- info: 'SkewGluing.olsonHarris_compose_and_reverse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.olsonHarris_compose_and_reverse

-- `lem:gluing-local` (1)
/-- info: 'SkewGluing.MarkedInner.IsLegal.gluing_local_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.gluing_local_one

-- `lem:gluing-local` (2)
/-- info: 'SkewGluing.MarkedInner.IsLegal.gluing_local_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.gluing_local_two

-- `lem:gluing-local` (3), connectedness
/-- info: 'SkewGluing.MarkedInner.IsLegal.isConnectedSkew_compose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.isConnectedSkew_compose

-- `lem:gluing-local` (3), windows
/-- info: 'SkewGluing.MarkedInner.IsLegalNonempty.windows_determine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegalNonempty.windows_determine

-- `lem:gluing-coding`
/-- info: 'SkewGluing.MarkedInner.IsLegalNonempty.gluing_coding_periodic' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegalNonempty.gluing_coding_periodic

-- `lem:gluing-mark-locality`
/-- info: 'SkewGluing.mark_locality' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.mark_locality

-- `cor:gluing-mark-transfer`
/-- info: 'SkewGluing.MarkedInner.IsLegalNonempty.mark_transfer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegalNonempty.mark_transfer

-- `lem:gluing-equal`
/-- info: 'SkewGluing.Chart.IsProperLegal.equal_periods_same_fiber' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.IsProperLegal.equal_periods_same_fiber

-- `lem:gluing-equal`, structure
/-- info: 'SkewGluing.Chart.IsProperLegal.equal_periods_cases' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.IsProperLegal.equal_periods_cases

-- `lem:gluing-aligned`
/-- info: 'SkewGluing.MarkedInner.IsLegal.aligned' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegal.aligned

-- `prop:gluing-divisible`, chart form
/-- info: 'SkewGluing.MarkedInner.divisible' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.divisible

-- `lem:gluing-periods` (i)
/-- info: 'SkewGluing.PeriodWords.periods_one_hole' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.PeriodWords.periods_one_hole

-- `lem:gluing-periods` (ii)
/-- info: 'SkewGluing.PeriodWords.periods_two_holes' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.PeriodWords.periods_two_holes

-- `lem:gluing-periods` (iii)
/-- info: 'SkewGluing.PeriodWords.periods_full_two_holes' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.PeriodWords.periods_full_two_holes

-- `lem:gluing-row-action`, `eq:gluing-row-action`
/-- info: 'SkewGluing.cellProfile_rowMark_compose' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.cellProfile_rowMark_compose

-- `lem:gluing-row-action`, converse
/-- info: 'SkewGluing.MarkedInner.IsRowMark.cellProfile_compose' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsRowMark.cellProfile_compose

-- `lem:gluing-row-transport`
/-- info: 'SkewGluing.liftAny_bijOn_schurClass' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.liftAny_bijOn_schurClass

-- `lem:gluing-lines` (1)
/-- info: 'SkewGluing.Chart.IsProperLegal.coprime_periods_line' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.IsProperLegal.coprime_periods_line

-- `lem:gluing-lines` (2)
/-- info: 'SkewGluing.Chart.IsProperLegal.exists_chart_of_line' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.IsProperLegal.exists_chart_of_line

-- `lem:gluing-lines`, forks glue
/-- info: 'SkewGluing.HasCommonFinalFactor.of_line_inner' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.HasCommonFinalFactor.of_line_inner

-- `lem:gluing-small`, first assertion
/-- info: 'SkewGluing.Chart.IsProperRoot.exists_small_root_gcd' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.IsProperRoot.exists_small_root_gcd

-- `lem:gluing-small`, least period
/-- info: 'SkewGluing.SmallOverlap.exists_least_small_root_dvd' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.SmallOverlap.exists_least_small_root_dvd

-- `lem:gluing-ordinary-drift`
/-- info: 'SkewGluing.OrdinaryPair.ordinary_drift' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.OrdinaryPair.ordinary_drift

-- `prop:gluing-ordinary-fold`
/-- info: 'SkewGluing.OrdinaryPair.exists_gcd_root' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.OrdinaryPair.exists_gcd_root

-- `lem:gluing-collision`
/-- info: 'SkewGluing.gluing_collision' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.gluing_collision

-- `lem:gluing-incompatible`
/-- info: 'SkewGluing.TwoRoots.gluing_incompatible' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.TwoRoots.gluing_incompatible

-- `prop:gluing-mixed-fold`
/-- info: 'SkewGluing.gluing_mixed_fold' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.gluing_mixed_fold

-- `cor:least-root-period`
/-- info: 'SkewGluing.least_root_period' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.least_root_period

-- `cor:least-root-period`, general clause
/-- info: 'SkewGluing.Chart.IsSourceMinimal.period_dvd' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.IsSourceMinimal.period_dvd

-- `prop:component-key`, independence of the chart
/-- info: 'SkewGluing.Chart.IsSourceMinimal.key_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.IsSourceMinimal.key_eq

-- `prop:component-key`, classification
/-- info: 'SkewGluing.component_key_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.component_key_iff

-- cited: Reiner–Shaw–van Willigenburg row invariants
/-- info: 'SkewGluing.reinerRowInvariants' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.reinerRowInvariants

-- cited: Barekat–Reiner–van Willigenburg irreducibility
/-- info: 'SkewGluing.barekatIrreducibility' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.barekatIrreducibility

-- `ι(s_D) = s_{Dᵗ}` (`sec:minimal-fibers`, component keys)
/-- info: 'SkewGluing.schurInvolution_schur_transpose' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.schurInvolution_schur_transpose

-- tableau form of `s_D` (`sec:gluing`, profiles and Jacobi–Trudi)
/-- info: 'SkewGluing.aeval_cellSchur_skewDiagram_all' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.aeval_cellSchur_skewDiagram_all

-- cited: Olson-Harris composition (`sec:gluing`)
/-- info: 'SkewGluing.olsonHarrisComposition' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.olsonHarrisComposition

-- `lem:gluing-coding`: antitransposition keeps the outer, and the case-(c) interface from it
/-- info: 'SkewGluing.MarkedInner.antitranspose_compose_of_isLegal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.antitranspose_compose_of_isLegal

/-- info: 'SkewGluing.MarkedInner.IsLegalNonempty.interface_c_of_antitranspose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegalNonempty.interface_c_of_antitranspose

/-- info: 'SkewGluing.MarkedInner.IsLegalNonempty.caps_c_wq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.IsLegalNonempty.caps_c_wq

-- `ge:ordinary-fold`, `ge:empty-fold`, and the lift through `lem:gluing-aligned`
/-- info: 'SkewGluing.FoldSupplied.lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.lift

/-- info: 'SkewGluing.FoldSupplied.exists_lifted_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.exists_lifted_chart

/-- info: 'SkewGluing.FoldSupplied.empty_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.empty_fold

/-- info: 'SkewGluing.FoldSupplied.empty_fold_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.empty_fold_lift

/-- info: 'SkewGluing.FoldSupplied.ordinary_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.ordinary_fold

/-- info: 'SkewGluing.FoldSupplied.ordinary_fold_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.ordinary_fold_lift

/-- info: 'SkewGluing.FoldSupplied.OrdCtx.exists_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.OrdCtx.exists_chart

/-- info: 'SkewGluing.FoldSupplied.OrdWords.emptyWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.OrdWords.emptyWords

/-- info: 'SkewGluing.FoldSupplied.OrdCtx.slotWords_a_big' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.OrdCtx.slotWords_a_big

/-- info: 'SkewGluing.FoldSupplied.OrdCtx.slotWords_b_big' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.OrdCtx.slotWords_b_big

/-- info: 'SkewGluing.FoldSupplied.OrdCtx.slotWords_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.OrdCtx.slotWords_small

/-- info: 'SkewGluing.FoldSupplied.IsLegalNonempty.ordWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.IsLegalNonempty.ordWords

/-- info: 'SkewGluing.Chart.IsProperLegal.inner_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.Chart.IsProperLegal.inner_card_lt

/-- info: 'SkewGluing.Chart.IsProperLegal.inner_card_lt_of_chartOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.Chart.IsProperLegal.inner_card_lt_of_chartOf

/-- info: 'SkewGluing.Chart.IsProperLegal.outer_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.Chart.IsProperLegal.outer_card_lt

/-- info: 'SkewGluing.Chart.IsProperLegal.outer_card_lt_of_chartOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.Chart.IsProperLegal.outer_card_lt_of_chartOf

/-- info: 'SkewGluing.MarkedInner.decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.MarkedInner.decoder

/-- info: 'SkewGluing.MarkedInner.decoder_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.MarkedInner.decoder_exists

/-- info: 'SkewGluing.MarkedInner.decoder_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.MarkedInner.decoder_sizes

/-- info: 'SkewGluing.MarkedInner.decoder_of_cut_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.MarkedInner.decoder_of_cut_windows

/-- info: 'SkewGluing.MarkedInner.IsLegal.compose_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.MarkedInner.IsLegal.compose_native

/-- info: 'SkewGluing.MarkedInner.IsLegal.compose_ports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.MarkedInner.IsLegal.compose_ports

/-- info: 'SkewGluing.MarkedInner.IsLegal.hwd_compose_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.MarkedInner.IsLegal.hwd_compose_private

/-- info: 'SkewGluing.cell_criterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.cell_criterion

/-- info: 'SkewGluing.cell_criterion_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.cell_criterion_anti

/-- info: 'SkewGluing.CellCriterionData.slotGeom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.CellCriterionData.slotGeom

/-- info: 'SkewGluing.ordinary_block_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.ordinary_block_formula

/-- info: 'SkewGluing.FoldSupplied.ordinary_fold_of_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.ordinary_fold_of_roots

/-- info: 'SkewGluing.FoldSupplied.empty_fold_of_partner_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.empty_fold_of_partner_root

/-- info: 'SkewGluing.FoldSupplied.mixed_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.mixed_fold

/-- info: 'SkewGluing.FoldSupplied.mixed_fold_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.mixed_fold_lift

/-- info: 'SkewGluing.FoldSupplied.MixCtx.foldData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.MixCtx.foldData

/-- info: 'SkewGluing.FoldSupplied.mixed_class_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.mixed_class_hyps

/-- info: 'SkewGluing.FoldSupplied.mixed_fold_of_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewGluing.FoldSupplied.mixed_fold_of_roots
