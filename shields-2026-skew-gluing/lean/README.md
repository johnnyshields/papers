# Lean 4 formalization — Local common-factor gluing and reduction of composition necessity for skew Schur functions

Formalizes `shields-2026-skew-gluing.tex` against Mathlib (`leanprover/lean4:v4.34.1`,
Mathlib `v4.34.1`, namespace `SkewGluing`).  **The development is unconditional: no `sorry` and no
project axiom anywhere in the tree**, and every result below reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.  The results the paper takes from
other works and consumes are proved here as well: the composition theorem for marks satisfying
Hypotheses I–IV [1, Thms. 5.3.9, 5.3.10], the row and overlap invariants of Schur-equal connected
diagrams [2, Cor. 8.11], irreducibility of connected skew Schur functions [3, Thm. 1], and the
transpose identity `ι(s_D) = s_{Dᵗ}`.

The paper proves that every connected component of the common-factor graph of a skew Schur class
is a clique, and that each rooted component is the fiber of any source-minimal chart at any of its
vertices, so that a source-minimal marked inner and outer Schur function form a key classifying
the component.  It then shows that global connectivity of the rotation-augmented graph is
equivalent to rigidity at chartless diagrams together with equality of keys for rooted mates, and
that these two assertions are equivalent to composition-and-reversal necessity.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

## Result coverage

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.  A row
marked **⚠️ Partial** or **❌ Missing** below reflects the state of the Lean formalization, not of
the paper.

Every Lean name in this section and the next is pinned to the standard axiom footprint by a
`#guard_msgs` in `SkewGluing/AxiomCheck.lean`, or reaches one that is.  The unconditional forms of
the main results are in `SkewGluing/MainTheorems.lean`.

| Where | Result | Status | Paper | Lean |
| --- | --- | --- | --- | --- |
| §2 Thm 2.2 | Every component of every common-factor graph is a clique; the fork form | ✅ Full | `thm:gluing` | `gluing`, `gluing_fork_of_edges` |
| §2 Cor 2.6 | Composites with one mixed inner and outers of equal span carry the same legal marks of each width up to the period, none at the period | ✅ Full | `cor:gluing-mark-transfer` | `MarkedInner.IsLegalNonempty.mark_transfer`, `IsLegalNonempty.mark_transfer_of_cellSchur_eq` |
| §2 Prop 2.9 | Divisible periods: the coarse inner factors through the fine one, the coarse chart reassociates, and its fiber lies in the fine fiber | ✅ Full | `prop:gluing-divisible` | `gluing_divisible`, `MarkedInner.divisible`, `MarkedInner.exists_inner_factor` |
| §2 | Two ordinary roots of nondividing periods have a proper legal period-`g` root | ✅ Full | `prop:gluing-ordinary-fold` | `OrdinaryPair.exists_gcd_root` |
| §2 | Two same-case mixed roots of nondividing periods have a proper legal period-`g` root; singleton at remainder one, the hook at gcd two | ✅ Full | `prop:gluing-mixed-fold` | `gluing_mixed_fold` |
| §3 Thm 3.2 | Every proper-chart fiber through `F` lies in the source-minimal fiber, which is the component of `F` in `Γ` and in `Γ⁺` | ✅ Full | `thm:source-minimal-domination` | `source_minimal_domination`, `Chart.IsSourceMinimal.fiber_subset`, `Chart.IsSourceMinimal.component_eq` |
| §3 Cor 3.3 | Without line inners the least proper period divides every proper period; the row `(7)` shows the qualification is needed | ✅ Full | `cor:least-root-period` | `least_root_period`, `Chart.IsSourceMinimal.period_dvd`, `row_seven_least_period` |
| §3 Prop 3.4 | The key is independent of the source-minimal chart and classifies components; the involution in it cannot be dropped | ✅ Full | `prop:component-key` | `component_key`, `Chart.IsSourceMinimal.key_eq`, `component_key_iff`, `gauge_necessity` |
| §4 Thm 4.1 | Connectivity of the augmented and quotient graphs, common final factors for all nonrotation pairs, and (TR) with (RI) are equivalent | ✅ Full | `thm:connectivity-reduction` | `connectivity_reduction_class`, `disjoint_cliques_remark` |
| §4 Thm 4.2 | Composition-and-reversal necessity, (TR) and (RI) in every class, and exhaustion by every complete source-minimal tower are equivalent | ✅ Full | `thm:necessity-reduction` | `necessity_reduction_tfae`, `Presentation.exists_isCompleteTower` |

## Structural coverage

| Where | Item | Status | Paper | Lean |
| --- | --- | --- | --- | --- |
| §2 Eq 2.1 | Cell offsets of the composition, with supplemental copies | ✅ Full | `eq:gluing-offsets` | `MarkedInner.origin`, `MarkedInner.compose` |
| §2 Def 2.1 | Common final factor, common-factor graph, fiber | ✅ Full | `def:gluing-graph` | `HasCommonFinalFactor`, `classGraph`, `fiber`, `fiberClass` |
| §2 Fig 1 | The chart of the figure | ✅ Full | `fig:chart` | `chartFigureInner` |
| §2 Eq 2.2 | Diagonal bits and heights; the diagonal criterion and bit-word reconstruction | ✅ Full | `eq:gluing-bits` | `bitA`, `bitB`, `height`, `isConnectedSkew_iff_diagonal`, `exists_unique_connectedSkew_of_bits` |
| §2 Lem 2.3 | Local structure of a legal mark: full intersections, thin middles, private singletons, middle phases, justification, windows, span law, connected composites | ✅ Full | `lem:gluing-local` | `MarkedInner.IsLegal.gluing_local_one`, `IsLegal.gluing_local_two`, `IsLegal.isConnectedSkew_compose`, `IsLegalNonempty.windows_determine`, `span_compose` |
| §2 Eq 2.3, 2.4 | Outer profile and the case-(d) height formula | ✅ Full | `eq:gluing-profile`, `eq:gluing-mixed-profile` | `profM`, `profS`, `IsLegalNonempty.mixed_profile` |
| §2 (Lem 2.3) | Fixed-chart injectivity | ✅ Full | `lem:gluing-local` | `IsLegal.injective_compose` |
| §2 Lem 2.4 | Boundary words are `q`-periodic off the exceptional residues | ✅ Full | `lem:gluing-coding`, `eq:gluing-holes` | `IsLegalNonempty.gluing_coding_periodic`, `holesA`, `holesB` |
| §2 Eq 2.6–2.8 | Caps, case-(d) and case-(c) interfaces, ordinary endpoints | ✅ Full | `eq:gluing-caps`, `eq:gluing-interface`, `eq:gluing-ordinary-endpoints` | `IsLegalNonempty.caps_a`, `IsLegalNonempty.caps_b`, `IsLegalNonempty.caps_c`, `IsLegalNonempty.caps_d`, `IsLegalNonempty.interface_d`, `IsLegalNonempty.interface_c`, `IsLegalNonempty.ordinary_endpoints_a` |
| §2 (Lem 2.4) | Antitransposition takes a case-(d) chart to a case-(c) chart with the same outer and phases; the case-(c) interface by that route | ✅ Full | `lem:gluing-coding` | `MarkedInner.antitranspose_compose_of_isLegal`, `MarkedInner.IsLegalNonempty.interface_c_of_antitranspose` |
| §2 (Lem 2.4) | Case (c): \(A_w=0\), \(A_q=1\) | ✅ Full | `lem:gluing-coding` | `MarkedInner.IsLegalNonempty.caps_c_wq` |
| §2 Lem 2.5 | Legal marks below the period are decided by two windows; the windows cannot be narrowed | ✅ Full | `lem:gluing-mark-locality` | `mark_locality`, `mark_locality_middle_hatMark` |
| §2 Lem 2.7 | Equal periods give the same fiber; the antitransposition gauge | ✅ Full | `lem:gluing-equal`, `eq:gluing-gauge` | `Chart.IsProperLegal.equal_periods_same_fiber`, `Chart.IsProperLegal.equal_periods_cases`, `compose_antitranspose_gauge`, `fiber_gauge` |
| §2 Lem 2.8 | Reassociation through a lower mark, including the walk and the nested count | ✅ Full | `lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-walk-signs`, `eq:gluing-nested-count` | `MarkedInner.IsLegal.aligned`, `IsReassociation`, `walk_signs`, `alD_NC_all` |
| §2 Lem 2.10 | Periods of words with holes | ✅ Full | `lem:gluing-periods` | `PeriodWords.periods_one_hole`, `PeriodWords.periods_two_holes`, `PeriodWords.periods_full_two_holes` |
| §2 Lem 2.11, Eq 2.13 | The row mark is legal and acts on profiles affinely; the converse | ✅ Full | `lem:gluing-row-action`, `eq:gluing-row-action` | `rowMark_isLegal`, `cellProfile_rowMark_compose`, `MarkedInner.IsRowMark.cellProfile_compose` |
| §2 Lem 2.12 | Row transport bijects Schur classes | ✅ Full | `lem:gluing-row-transport` | `liftAny_bijOn_schurClass`, `Profile.schur_lift_eq_iff` |
| §2 Lem 2.13 | Coprime periods force line inners; every mate of a line-inner diagram carries it; forks there glue | ✅ Full | `lem:gluing-lines` | `Chart.IsProperLegal.coprime_periods_line`, `Chart.IsProperLegal.exists_chart_of_line`, `HasCommonFinalFactor.of_line_inner` |
| §2 Lem 2.14, Eq 2.14 | Small overlaps: the gcd root of the same width; least small-root period | ✅ Full | `lem:gluing-small`, `eq:gluing-singleton` | `Chart.IsProperRoot.exists_small_root_gcd`, `SmallOverlap.exists_least_small_root_dvd`, `SmallOverlap.SingletonTable` |
| §2 | Gcd data, drift and pinches for two ordinary roots | ✅ Full | `lem:gluing-ordinary-drift`, `eq:gluing-gcd-data`, `eq:gluing-pinches`, `eq:gluing-pinch-equations` | `OrdinaryPair.ordinary_drift`, `GcdData`, `DriftConclusion`, `OrdinaryPair.pinch_equations` |
| Appendix, Ordinary cap data | Slot condition, original mark heights, singleton phase table and cap budgets for the selected compatible gauge | ✅ Full | `app:gluing-fold-data`, `eq:gluing-ordinary-slot`, `eq:gluing-original-ordinary-mark` | `OrdinaryDrift.SlotScalars`, `ordFold_original_mark_heights`, `OrdinaryPair.singleton_table`, `OrdinaryDrift.GcdPair.cap_budgets` |
| §2 Lem 2.17, 2.18 | Phase collision; incompatible mixed pairs | ✅ Full | `lem:gluing-collision`, `lem:gluing-incompatible` | `gluing_collision`, `TwoRoots.gluing_incompatible` |
| §2 | Mixed projected phases and cap budgets | ✅ Full | `eq:gluing-mixed-phases` | `MixFoldPair.Gen.phases_exact` |
| Appendix, Mixed cap data | Retained heights, the original mixed mark, and the outer of the lifted mixed chart | ✅ Full | `app:gluing-fold-data`, `eq:gluing-mixed-heights`, `eq:gluing-original-mixed-mark`, `eq:gluing-mixed-inverse` | `MixFoldPair.Gen.inner_heights`, `mixFold_original_mark_heights`, `mixFoldOuter` |
| §3 (head) | The three-cell hook class: two isolated vertices, one rotation orbit | ✅ Full | `sec:minimal-fibers` | `cellSchur_eq_hook_iff`, `hook_class_graph` |
| §3 Lem 3.1 | Components of the rotation-augmented and quotient graphs are cliques | ✅ Full | `lem:rotation-components` | `rotation_components_cliques` |
| §3 Eq 3.1, 3.2 | Chart score; component key | ✅ Full | `eq:chart-score`, `eq:component-key` | `Chart.score`, `Chart.key`, `KeyStep` |
| §3 Eq 3.3 | The nonminimal fiber | ✅ Full | `eq:nonminimal-fiber` | `nonminimal_fiber_example`, `NonminimalFiber.X_not_mem_coarse_fiber` |
| §2 (setting) | `s_D` of a diagram; agreement with the tableau skew Schur function | ✅ Full | `sec:gluing` | `cellSchur`, `Profile.schur`, `aeval_cellSchur_skewDiagram_all` |
| §2 (cited input) | Schur-equal connected diagrams share rows, row lengths and overlaps | ✅ Full | `lem:gluing-row-transport` | `reinerRowInvariants` |
| §2 (cited input) | Connected skew Schur functions are irreducible | ✅ Full | `lem:gluing-row-transport` | `barekatIrreducibility` |
| §3 (cited input) | `ι(s_D) = s_{Dᵗ}` | ✅ Full | `eq:component-key` | `schurInvolution_schur_transpose` |
| §2 (cited input) | Composition and reversal under Hypotheses I–IV | ✅ Full | `def:gluing-graph` | `olsonHarrisComposition`, `cellSchur_compose_eq`, `cellSchur_compose_eq_rotate_compose`, `fiber_isClique` |
| §2 | The fold of a supplied inner lifts to the original parent by aligned composition | ✅ Full | `lem:gluing-aligned`, `prop:gluing-ordinary-fold`, `prop:gluing-mixed-fold` | `FoldSupplied.lift`, `FoldSupplied.exists_lifted_chart` |
| §2 | Empty residue fold of a supplied inner (row or column outer, retained words, both areas strict) | ✅ Full | `ge:empty-fold` | `FoldSupplied.empty_fold`, `FoldSupplied.lineOuter_zero`, `FoldSupplied.lineOuter_one` |
| §2 | Empty fold of a supplied empty inner lifted to the parent, the periodicity of the completed words derived from the partner root | ✅ Full | `lem:gluing-small`, `ge:empty-fold` | `FoldSupplied.empty_fold_of_partner_root`, `FoldSupplied.empty_partner_periodic`, `FoldSupplied.common_value_of_heights`, `FoldSupplied.empty_fold_lift` |
| §2 | Ordinary residue fold of a supplied inner, every remainder and both gauges | ✅ Full | `ge:ordinary-fold` | `FoldSupplied.ordinary_fold`, `FoldSupplied.OrdCtx.exists_chart`, `FoldSupplied.OrdCtx.slotWords_a_big`, `FoldSupplied.OrdCtx.slotWords_b_big`, `FoldSupplied.OrdCtx.slotWords_small`, `FoldSupplied.OrdWords.emptyWords` |
| §2 | Ordinary fold applied to the supplied inner of the first root and lifted, the class hypotheses derived from the two roots | ✅ Full | `prop:gluing-ordinary-fold`, `lem:gluing-periods` | `FoldSupplied.ordinary_fold_of_roots`, `FoldSupplied.ordinary_transport`, `FoldSupplied.fullOrEmptyOff_col`, `FoldSupplied.fullOrEmptyOff_row`, `FoldSupplied.ordinary_fold_lift` |
| §2 | Mixed residue fold of a supplied inner, every width range (the word data of the folded root derived from the case-(d) copy relation, the block formula with two exceptional classes and charge `-1`), applied to the supplied inner of the first root and lifted to the original parent, the class hypotheses derived from the two roots; case (c) by rotation | ✅ Full | `ge:mixed-fold`, `prop:gluing-mixed-fold`, `lem:gluing-periods` | `FoldSupplied.mixed_fold`, `FoldSupplied.MixCtx.foldData`, `FoldSupplied.MixCtx.win`, `FoldSupplied.mixed_class_hyps`, `FoldSupplied.mixed_fold_lift`, `FoldSupplied.mixed_fold_of_roots` |
| §2 | Both factors of a proper chart have strictly fewer cells than its parent | ✅ Full | `ge:decoder` | `Chart.IsProperLegal.inner_card_lt`, `Chart.IsProperLegal.outer_card_lt` |
| §2 | The compiler: a composite repeats the native words of its inner at every nonvariable position, reads the outer's closed words at the variable slots of each attachment case, and has the outer's heights on the private diagonals | ✅ Full | `ge:eq:ports`, `ge:eq:sample` | `Xw`, `Yw`, `hwd`, `natPos`, `portDecode`, `MarkedInner.IsLegal.compose_native`, `MarkedInner.IsLegal.compose_ports`, `MarkedInner.IsLegal.hwd_compose_private` |
| §2 | Recovery of the outer from the generic words: a unique connected outer with the sampled heights, strictly smaller factors for span at least two, and the inner itself at span one | ✅ Full | `ge:decoder` | `MarkedInner.decoder`, `MarkedInner.decoder_exists`, `MarkedInner.decoder_sizes` |
| §2 | Two actual cut windows covering the words reconstruct the parent | ✅ Full | `ge:remark:cut` | `MarkedInner.decoder_of_cut_windows` |
| §2 | Ordinary cell criterion: bit recursions, heights and contacts give a full legal ordinary mark with the stated copies, in both gauges | ✅ Full | `ge:cell-criterion` | `CellCriterionData`, `cell_criterion`, `cell_criterion_anti`, `CellCriterionData.slotGeom` |
| §2 | Block formula for the height sums of the completed native row and column words | ✅ Full | `ge:eq:ordinary-block` | `ordinary_block_formula` |

## Differences from paper

| § | Item | Lean declaration | Module | Description |
|---|---|---|---|---|
| §2 | Lem 2.3 `lem:gluing-local` | `IsLegalNonempty.thin_lower`, `IsLegalNonempty.phases_lt`, `IsLegalNonempty.injective_ord` | `Local.Tails`, `Local.Middle`, `Local.Injective` | the paper's first-diagonal and endpoint arguments are replaced by reading the side of each tail and the private rows directly off the composite |
| §2 | Lem 2.4 `lem:gluing-coding` | `IsLegalNonempty.caps_b`, `IsLegalNonempty.periodExcept_c`, `IsLegalNonempty.interface_c` | `Coding.Caps`, `Coding.CaseC` | case (b) is read directly and case (c) by rotation, where the paper uses antitransposition for both |
| §2 | Lem 2.4 `lem:gluing-coding` | `MarkedInner.antitranspose_compose_mixed` | `AntitransposeMixed` | the paper asserts that antitransposition keeps the outer; here the main copies match under a reflection of each diagonal of the outer, and every supplemental copy either lies in a copy already present or sits at a diagonal end, where the reflection exchanges the two cases' supplemental copies |
| §2 | Lem 2.5 `lem:gluing-mark-locality` | `mark_locality` | `MarkLocality` | Hypothesis III is transferred by gluing connected skew diagrams along a shared diagonal rather than clause by clause |
| §2 | Cor 2.6 `cor:gluing-mark-transfer` | `IsLegalNonempty.no_mark_of_width_period_d` | `MarkTransfer` | the clause at `u = q` reads the southeast rows directly, with no comparison of bit sums and no split at `r = 1` |
| §2 | Lem 2.7 `lem:gluing-equal` | `IsLegal.equal_periods_cases` | `EqualPeriods` | at width zero only the horizontal edge reading is a legal mark, and the vertical one enters as a fiber identity |
| §2 | Lem 2.8 `lem:gluing-aligned` | `MarkedInner.exists_lowerMark_ordinary_proof`, `MarkedInner.ordinary_edge_displacement_proof`, `MarkedInner.MixedEta.Setup.legal_lowerMark` | `Aligned.OrdinaryLower`, `Aligned.OrdinaryEdge`, `Aligned.MixedEta` | maximality is immediate for a lower copy defined as the full intersection, the edge displacement is read from the end caps, and case (b) of the inner goes by rotation |
| §2 | Lem 2.10 `lem:gluing-periods` | `related_of_gcd_dvd`, `periods_full_two_holes` | `PeriodWords.Core`, `PeriodWords` | one gcd-cycle argument for every case, and two lost cyclic edges excluded by comparing multiples of the period instead of forcing `Q = 2p` |
| §2 | Lem 2.13 `lem:gluing-lines` | `Chart.IsProperLegal.exists_chart_of_column`, `HasCommonFinalFactor.of_line_inner` | `Lines.Mates` | the column case goes through antitransposition, and the fork clause does not use the two fork edges |
| §2 | Lem 2.14 `lem:gluing-small` | `SmallOverlap.drift_class_const`, `Chart.IsProperRoot.exists_singletonRoot_gcd` | `SmallOverlap.DriftClass`, `SmallOverlap.SmallFinal` | the drift is shown constant by a block count instead of comparing signs of consecutive drifts, and case (c) goes by rotation |
| §2; appendix, Ordinary cap data | `prop:gluing-ordinary-fold`, `app:gluing-fold-data` | `OrdinaryPair.exists_gcd_root`, `OrdinaryFold.emptyMarkH_period` | `OrdinaryFold`, `OrdinaryFold.Empty` | Lean constructs the root directly from the parent words for every remainder; the paper applies the native fold to an actual supplied inner and then aligned composition to its original outer.  The appendix gives the compatible gauge, singleton phase table and cap formulas |
| §2; appendix, Mixed cap data | `prop:gluing-mixed-fold`, `app:gluing-fold-data` | `mixFold_exists_root_d`, `mixFold_inner_heights` | `MixedFold`, `MixedFold.MarkHeights` | Lean constructs the full intersection mark and the outer directly from parent words; the paper folds an actual supplied inner and lifts by aligned composition.  The appendix describes the retained copies and outer of that actual chart |
| §2; appendix | `prop:gluing-ordinary-fold`, `lem:gluing-small` (supplied inner) | `FoldSupplied.ordinary_fold_of_roots`, `FoldSupplied.empty_fold_of_partner_root` | `FoldSupplied.Ordinary`, `FoldSupplied.HypOrdinary`, `FoldSupplied.HypAnti`, `FoldSupplied.HypEmpty` | the ordinary fold of the supplied inner is built from the slot form of the inner's words through `SlotWords.exists_root`, not from the cell criterion and `ge:decoder`; the class hypotheses are read off the generic bits of the parent on the first `p`-window, with the residue-zero values read at the actual step `p` |
| §2 | `prop:gluing-mixed-fold` (supplied inner) | `FoldSupplied.mixed_fold_of_roots` | `FoldSupplied.Mixed*`, `FoldSupplied.HypMixed` | the mixed fold of the supplied inner is built from the case-(d) word facts of the inner through `MixFoldFold.exists_chart`, not from the cell criterion and `ge:decoder`; the class hypotheses are read off the generic bits of the parent on the first `p`-window, with the residue-zero value read at the actual step `p`, and case (c) is the rotated comparison |
| §2 | `ge:decoder` | `MarkedInner.decoder_exists`, `MarkedInner.decoder_sizes` | `Decoder` | the sampled heights come from comparing the parent with a composite on a reference outer of the same span, whose block height increments are computed by the compiler; the phases of the empty mark are taken to be `(0, 0)`, and the nonvariable-slot hypothesis is stated by the position map `natPos` into the native closed words |
| §2 | `ge:cell-criterion` | `cell_criterion`, `CellCriterionData.slotGeom` | `CellCriterion` | the mark is obtained by checking the diagonal data `SlotGeom` of the ordinary fold on the content-normalized translate of `K`, so maximality, connectedness of both removals and the absence of hatted adjacency come from `SlotGeom.mark_isLegal` rather than from the content-separation argument; the copies are stated as diagonal sets in absolute contents |
| §2 | `ge:eq:ordinary-block` | `ordinary_block_formula` | `CellCriterion` | stated for the indicator words of the completed native row and column sets, with the class conditions as periodicity off one residue per word |
| §3 | head of `sec:minimal-fibers` | `cellSchur_eq_hook_iff` | `CellSchur` | irreducibility and the row invariants identify the two hooks directly, without the homogeneity count |
| §3 | Lem 3.1 `lem:rotation-components` | `RotationData.componentsAreCliques_quotient` | `GraphTheory` | cliqueness of the quotient is deduced from that of the augmented graph through reachability |
| §4 | Thm 4.1 `thm:connectivity-reduction` | `KeyedRotationData.connectivity_reduction` | `GraphTheory` | statements (3) and (4) are shown equivalent directly |
| §4 | Thm 4.2 `thm:necessity-reduction` | `Presentation.Corresponds.rotationMates_or_hasCommonFinalFactor` | `NecessityReduction.Presentation` | trivial stages are absorbed along the induction instead of being removed in advance |

## Differences from cited works

The composition theorem of [1] is proved in `SkewGluing/OlsonHarris/` along the source's
route — Murnaghan–Nakayama for one power sum, the kernel of the shape algebra, the edge and the
corner case — with these departures:

| Source result | Lean declaration | Module | Description |
|---|---|---|---|
| Murnaghan–Nakayama, derivation form (thesis Cor. 5.1.15) | `Plan.pDeriv_cellSchur_left` | `OlsonHarris.Plan.MurnaghanNakayama` | the Jacobi–Trudi determinant is differentiated column by column, instead of the Hall inner product |
| Kernel of the shape algebra (thesis Thm. 5.2.2) | `KernelAux.linearIndependent_ferrersSchur` | `OlsonHarris.Plan.Kernel.Independence` | linear independence of the Schur functions by a degree count, instead of orthonormality |
| Edge case (thesis Thm. 5.4.1, Lemmas 5.4.2–5.4.5) | `Plan.leftRibbons_copies_proof`, `Plan.EdgeRibbon.exists_model` | `OlsonHarris.Plan.EdgeCase.EdgeRibbon` | the border word of the composite replaces the loose-end-ribbon argument |
| Edge case (thesis Lemma 5.4.3) | `Plan.cellSchur_copies_sdiff_liftRibbon_proof` | `OlsonHarris.Plan.EdgeCase.EsDiff` | the pieces left by removing key ribbons are computed in diagonal coordinates and separated by content distance |
| Edge case (thesis Lemma 5.4.4) | `Plan.content_mem_hatMiddleFin` | `OlsonHarris.Plan.EdgeCase.Kill` | the hat factors span fewer than `q` diagonals, so no ribbon of size `mq` fits, for every legal mark |
| Corner case (thesis Lemma 5.5.8) | `Plan.Corner.corner_lift_remainder_proof` | `OlsonHarris.Plan.CornerCase.Crem` | the remainder is computed on every diagonal at once instead of one box at a time |
| Corner case (thesis Lemmas 5.5.10, 5.5.11) | `Plan.Corner.corner_lift_height_sign_proof` | `OlsonHarris.Plan.CornerCase.CSign` | heights come from the profile of the rotated composite, `ξ(D) = ξ(D*)` by a telescoping sum, and the northbound count of `A` is taken in its southeast form, which is what holds for ribbons removed on the left |

Row invariants [2, Cor. 8.11] are proved by an extremal-monomial
argument on the Jacobi–Trudi determinant (`reinerRowInvariants`), and irreducibility [3, Thm. 1]
follows the corrigendum's induction directly over `ℚ`
(`barekatIrreducibility`).

## Dependencies

This development depends on modules in the repository-wide `_lean_shared/` tree, outside the
paper's `lean/` directory.

| Component | Used by | Description |
|---|---|---|
| `Shields.Combinatorics.Young.ElementarySymmetric` | `DualEvaluation`, for `Shields.elemHom` | Elementary symmetric functions as column skew Schur functions; extracted from `edrei-spectral-classification` |
| `Shields.Combinatorics.Young.LGVOddTableau` | `DualEvaluation`, for `Shields.skewJacobiTrudi` | Jacobi–Trudi over a mixed alphabet, giving the dual Jacobi–Trudi identity at zero even variables; extracted from `edrei-spectral-classification` |
| `Shields.Combinatorics.Young.LGVTableau` | `SchurBridge`, for `Shields.jacobiTrudiDet_eq_skewSchur` | Lindström–Gessel–Viennot with semistandard tableaux: the Jacobi–Trudi determinant is the tableau skew Schur polynomial; extracted from `edrei-spectral-classification` |
| `Shields.Combinatorics.Young.SkewSchurPolynomial` | `Transpose`, for `Shields.skewSchur` and `Shields.skewCells` | Skew Young diagrams and skew Schur polynomials; extracted from `edrei-spectral-classification` and `zero-reconstruction-edrei` |
| `Shields.LinearAlgebra.Matrix.DesnanotJacobi` | `Irreducibility`, for `Shields.desnanot_jacobi` | Desnanot–Jacobi condensation; extracted from `zero-reconstruction-edrei`, `exterior-sinc-hierarchies` and `edrei-spectral-classification` |
| `Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions` | `DualEvaluation`, for `newtonGirard_eh`, `hsymm_algebraicIndependent`, `hsymm`, `esymm` | Complete and elementary symmetric polynomials, Newton–Girard, algebraic independence of the complete ones.  Vendored from facebookresearch/algebraic-combinatorics (Fabian Gloeckle, GitHub `faabian`), a formalization of Grinberg's *An Introduction to Algebraic Combinatorics* |

## License

Code is made available under the MIT license (see `LICENSE.txt`), or as otherwise noted in the
comments of the file.  The vendored modules under `_lean_shared/Vendor` are the latter: each keeps
its upstream header.

This directory is also subject to the patent and trademark terms in the LICENSE.txt at the root of
the repository.

## References

1. N. Olson-Harris, *Some applications of combinatorial Hopf algebras to integro-differential
   equations and symmetric function identities*, Ph.D. thesis, University of Waterloo, 2024.
   [hdl:10012/20710](https://hdl.handle.net/10012/20710)
2. V. Reiner, K. M. Shaw and S. van Willigenburg, *Coincidences among skew Schur functions*,
   Adv. Math. **216** (2007), 118–152. [doi:10.1016/j.aim.2007.05.006](https://doi.org/10.1016/j.aim.2007.05.006)
3. F. Barekat, V. Reiner and S. van Willigenburg, *Corrigendum to "Coincidences among skew Schur
   functions"*, Adv. Math. **220** (2009), 1655–1656.
   [doi:10.1016/j.aim.2008.10.010](https://doi.org/10.1016/j.aim.2008.10.010)

Refer to the paper for references.
