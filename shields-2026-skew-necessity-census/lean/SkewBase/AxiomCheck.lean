import SkewBase.CellSetConnected
import SkewBase.CellSetPresentation
import SkewBase.CellSetProfile
import SkewBase.CellSetSchur
import SkewBase.ChartSize
import SkewBase.Examples
import SkewBase.ForwardGeneration
import SkewBase.Induction
import SkewBase.Keys
import SkewBase.JacobiTrudiEval
import SkewBase.ProfileCensus
import SkewBase.RowOverlaps
import SkewBase.SchurEqualConnected
import SkewBase.ShiftedDeterminant
import SkewBase.SearchesNormalize

/-!
# Axiom guard

Formalizes `shields-2026-skew-base-computational.tex`: the check that every headline declaration
of the development depends only on the three standard axioms `propext`, `Classical.choice` and
`Quot.sound`, so that none rests on `sorryAx`, on an added `axiom`, or on `Lean.ofReduceBool`.

Each `#guard_msgs in #print axioms X` below fails the build if the axioms of `X` change.

This module is not imported by the root `SkewBase`.

Sorry-free.
-/

-- `lem:size` (cells of the composite)
/-- info: 'SkewBase.card_compose_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.card_compose_ge

-- `lem:size`
/-- info: 'SkewBase.size_of_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.size_of_proper

-- `lem:size` (`q ≥ 2`)
/-- info: 'SkewBase.two_le_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.two_le_period

-- `lem:size` (`|D| ≤ |F| / 2`)
/-- info: 'SkewBase.two_mul_card_outer_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.two_mul_card_outer_le

-- `lem:size` (`|D| ≤ 17`)
/-- info: 'SkewBase.card_outer_le_seventeen' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.card_outer_le_seventeen

-- `lem:inner-size` (outer with two contents)
/-- info: 'SkewBase.inner_size_of_two_le_span' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.inner_size_of_two_le_span

-- `lem:inner-size`
/-- info: 'SkewBase.inner_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.inner_size

-- `lem:inner-size` (`|E| ≤ 23`)
/-- info: 'SkewBase.card_inner_le_23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.card_inner_le_23

-- `sec:keys` (cost of a proper legal chart)
/-- info: 'SkewGluing.Chart.cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Chart.cost_eq

-- `def:key` (marked inner up to translation and rotation)
/-- info: 'SkewGluing.MarkedInner.orbit_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.orbit_eq_iff

-- `def:key`
/-- info: 'SkewGluing.MarkedInner.orbit_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.orbit_symm

-- `def:key`
/-- info: 'SkewGluing.MarkedInner.orbit_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.orbit_trans

-- `prop:induction` (a common key gives charts with equal inner and outer)
/-- info: 'SkewGluing.exists_charts_of_mem_keySet_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.exists_charts_of_mem_keySet_inter

-- `prop:induction` (a common key is a common final factor)
/-- info: 'SkewBase.hasCommonFinalFactor_of_common_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasCommonFinalFactor_of_common_key

-- `prop:induction`, from common final factors
/-- info: 'SkewBase.necessityUpTo_of_commonFinalFactorsUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.necessityUpTo_of_commonFinalFactorsUpTo

-- `prop:induction`
/-- info: 'SkewBase.necessityUpTo_of_commonKeysUpTo' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.necessityUpTo_of_commonKeysUpTo

-- `thm:census`, abstract form
/-- info: 'SkewBase.census_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.census_eq

-- `thm:census`, for profiles
/-- info: 'SkewBase.census_eq_schurClasses' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.census_eq_schurClasses

-- `eq:jt`, evaluation commutes with the determinant
/-- info: 'SkewBase.evalAt_schurZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.evalAt_schurZ

-- `eq:jt`, the determinant over `ℤ` and over `ℚ`
/-- info: 'SkewBase.map_schurZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.map_schurZ

-- `eq:jt`, equality over `ℤ` and over `ℚ`
/-- info: 'SkewBase.schurZ_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.schurZ_eq_iff

-- `lem:invariants`, rows and overlaps of Schur-equal diagrams
/-- info: 'SkewGluing.reinerRowInvariants' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.reinerRowInvariants

-- `lem:invariants`, rotation invariance of `s_F`
/-- info: 'SkewGluing.Profile.schur_rotate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Profile.schur_rotate

-- non-vacuity of the size bounds
/-- info: 'SkewBase.figureChart_isProperLegal' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.figureChart_isProperLegal

-- `lem:copies` (iii), `N_F = N_D q + w`
/-- info: 'SkewBase.span_compose_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.span_compose_eq

-- `lem:copies` (iii), `w = N_F mod q`
/-- info: 'SkewBase.width_eq_span_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.width_eq_span_mod

-- `lem:copies` (iii), `N_E = q + w`
/-- info: 'SkewBase.span_inner_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.span_inner_eq

-- forward generation, `thm:searches`
/-- info: 'SkewBase.mem_forwardGeneration_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_forwardGeneration_iff

-- forward generation, `thm:searches`
/-- info: 'SkewBase.mem_forwardGeneration_of_isChartOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_forwardGeneration_of_isChartOf

-- `lem:invariants` for profiles
/-- info: 'SkewBase.AnyProfile.shard_invariant_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.AnyProfile.shard_invariant_eq

-- `lem:copies` (i), contents of the copy origins
/-- info: 'SkewGluing.MarkedInner.content_origin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.content_origin

-- `lem:copies` (i), contents of a copy
/-- info: 'SkewBase.contents_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.contents_copy

-- `lem:copies` (i), contents of a supplemental copy
/-- info: 'SkewBase.content_mem_supplemental' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.content_mem_supplemental

-- `lem:copies` (i), cells of a copy
/-- info: 'SkewBase.content_mem_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.content_mem_copy

-- `lem:copies` (ii), origins on one content
/-- info: 'SkewBase.origin_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.origin_mem_iff

-- `lem:copies` (ii), case (c)
/-- info: 'SkewBase.origin_mem_iff_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.origin_mem_iff_c

-- `lem:copies` (ii), case (d)
/-- info: 'SkewBase.origin_mem_iff_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.origin_mem_iff_d

-- `lem:copies` (ii), origin as `c(d) v + k e`
/-- info: 'SkewBase.origin_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.origin_eq_smul

-- `lem:copies` (i), contents of `E`
/-- info: 'SkewBase.content_bounds_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.content_bounds_E

-- `lem:copies` (i), contents of `W₋`
/-- info: 'SkewBase.content_bounds_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.content_bounds_W

-- `lem:copies` (i), contents of `W₊`
/-- info: 'SkewBase.content_bounds_upper' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.content_bounds_upper

-- `lem:bands` (ii), cells on a private content
/-- info: 'SkewBase.mem_compose_private_content' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_compose_private_content

-- `lem:bands` (ii), by rows
/-- info: 'SkewBase.mem_compose_private_row' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_compose_private_row

-- `lem:copies` (ii), rows of the origins
/-- info: 'SkewBase.origin_rows_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.origin_rows_iff

-- `lem:bands` (ii), the run of rows
/-- info: 'SkewBase.mem_compose_private_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_compose_private_iff

-- `lem:bands` (ii), private contents are contents
/-- info: 'SkewBase.mem_contents_private' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_contents_private

-- `lem:bands` (ii), least row
/-- info: 'SkewBase.diagLo_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.diagLo_private

-- `lem:bands` (ii), greatest row
/-- info: 'SkewBase.diagHi_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.diagHi_private

-- `lem:bands` (ii), height
/-- info: 'SkewBase.height_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.height_private

-- `cor:outer`, `eq:private` heights
/-- info: 'SkewBase.private_height_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.private_height_eq

-- `cor:outer`, `eq:private` offsets
/-- info: 'SkewBase.private_row_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.private_row_eq

-- normalized outer
/-- info: 'SkewBase.sw_zero_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sw_zero_facts

-- origin of the least cell
/-- info: 'SkewBase.origin_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.origin_zero

-- `lem:bands` (i), bottom band
/-- info: 'SkewBase.mem_compose_lower_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_compose_lower_iff

-- `lem:bands` (i), top band
/-- info: 'SkewBase.mem_compose_upper_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_compose_upper_iff

-- `cor:outer`, `κ_0`
/-- info: 'SkewBase.originRowLo_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.originRowLo_zero

-- `lem:heights`
/-- info: 'SkewBase.heightRecursion_of_isConnectedSkew' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.heightRecursion_of_isConnectedSkew

-- `lem:heights`, diagram of its diagonals
/-- info: 'SkewBase.eq_diagramOfRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.eq_diagramOfRows

-- `lem:heights`, normalized generated outer
/-- info: 'SkewBase.sw_diagramOfRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sw_diagramOfRows

-- `lem:heights`, `h(0) = 1`
/-- info: 'SkewBase.height_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.height_zero

-- `lem:heights`, cells of the generated outer
/-- info: 'SkewBase.mem_diagramOfRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_diagramOfRows

-- `lem:heights`, pointwise rows
/-- info: 'SkewBase.diagramOfRows_congr' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.diagramOfRows_congr

-- `thm:searches`, search S sound
/-- info: 'SkewBase.searchS_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.searchS_sound

-- `thm:searches`, search B sound
/-- info: 'SkewBase.searchB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.searchB_sound

-- `def:searches`, `N_D` of search S
/-- info: 'SkewBase.outerSpanS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.outerSpanS_eq

-- `thm:searches`, search S complete
/-- info: 'SkewBase.searchS_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.searchS_complete

-- `thm:searches`, search B complete
/-- info: 'SkewBase.searchB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.searchB_complete

-- `lem:bands` (i), the inner from the two bands
/-- info: 'SkewBase.bandInner_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.bandInner_eq

-- `lem:bands` (i), the bands agree
/-- info: 'SkewBase.bandsAgree_compose' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.bandsAgree_compose

-- `lem:bands` (i), the translation of the top band
/-- info: 'SkewBase.topShift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.topShift_eq

-- `lem:bands` (i), bottom band is `E` below `q`
/-- info: 'SkewBase.bottomBand_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.bottomBand_eq

-- `lem:bands` (i), top band is `E` from `w`
/-- info: 'SkewBase.topBand_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.topBand_eq

-- `cor:outer`, outer in case (a)
/-- info: 'SkewBase.eq_corOuterA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.eq_corOuterA

-- `cor:outer`, outer in case (b)
/-- info: 'SkewBase.eq_corOuterB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.eq_corOuterB

-- `lem:copies` (ii), the copies lie in `F`
/-- info: 'SkewBase.copiesInF_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.copiesInF_compose

-- `lem:heights`, the outer is generated
/-- info: 'SkewBase.mem_heightCandidates' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_heightCandidates

-- `eq:private`, heights independent of `w'`
/-- info: 'SkewBase.privateHeightsAgree_compose' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.privateHeightsAgree_compose

-- `eq:private`, offsets independent of `w'`
/-- info: 'SkewBase.privateRowsAgree_compose' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.privateRowsAgree_compose

-- `eq:private`, heights of the outer
/-- info: 'SkewBase.privateHeight_eq_height' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.privateHeight_eq_height

-- `eq:private`, offsets of the outer
/-- info: 'SkewBase.privateRow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.privateRow_eq

-- `thm:searches`, the inner is a subdiagram
/-- info: 'SkewBase.E_subset_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.E_subset_compose

-- translation of the inner
/-- info: 'SkewBase.compose_translate_inner' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.compose_translate_inner

-- normalized composite
/-- info: 'SkewBase.sw_compose_of_sw_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sw_compose_of_sw_zero

-- normalized representative of a chart
/-- info: 'SkewBase.exists_normalized_chart' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.exists_normalized_chart

-- `thm:searches`, search S returns exactly the proper charts
/-- info: 'SkewBase.searchS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.searchS_eq

-- `thm:searches`, search B returns exactly the proper charts
/-- info: 'SkewBase.searchB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.searchB_eq

-- `thm:searches`, search S, up to translation
/-- info: 'SkewBase.exists_searchS_of_isChartOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.exists_searchS_of_isChartOf

-- `thm:searches`, search B, up to translation
/-- info: 'SkewBase.exists_searchB_of_isChartOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.exists_searchB_of_isChartOf

-- search B, normalized inner
/-- info: 'SkewBase.sw_bandInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sw_bandInner

-- search S, normalized outer
/-- info: 'SkewBase.sw_of_mem_heightCandidates' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sw_of_mem_heightCandidates

-- search B, normalized outer (a)
/-- info: 'SkewBase.sw_corOuterA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sw_corOuterA

-- search B, normalized outer (b)
/-- info: 'SkewBase.sw_corOuterB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sw_corOuterB

-- legality under translation of the inner
/-- info: 'SkewGluing.MarkedInner.isLegal_translate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.MarkedInner.isLegal_translate

-- `thm:searches`, search S returns the figure chart
/-- info: 'SkewBase.figureChart_mem_searchS' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.figureChart_mem_searchS

-- `thm:searches`, search B returns the figure chart
/-- info: 'SkewBase.figureChart_mem_searchB' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.figureChart_mem_searchB

-- `lem:invariants`, a zero block forces a vanishing determinant
/-- info: 'SkewBase.det_eq_zero_of_zero_block' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.det_eq_zero_of_zero_block

-- `lem:invariants`, Jacobi–Trudi determinant with a subscript too small
/-- info: 'SkewBase.betaDetOf_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.betaDetOf_eq_zero

-- `lem:invariants`, determinant of the matrix of powers `X^{k_i - ζ_j}`
/-- info: 'SkewBase.det_powMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.det_powMatrix

-- `lem:invariants`, Cauchy–Binet expansion of the shifted determinant
/-- info: 'SkewBase.det_shiftEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.det_shiftEntry

-- `lem:invariants`, strictly decreasing maximal selection
/-- info: 'SkewBase.maxSel_strictAnti' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.maxSel_strictAnti

-- `lem:invariants`, complementary minor of the maximal selection
/-- info: 'SkewBase.betaDetOf_maxSel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.betaDetOf_maxSel

-- `lem:invariants`, degree and leading coefficient of the shifted determinant
/-- info: 'SkewBase.shifted_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.shifted_coeff

-- `lem:invariants`, the shift homomorphism on `h_a`
/-- info: 'SkewBase.shiftHom_hh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.shiftHom_hh

-- `lem:invariants`, degree and leading coefficient of the image of `s_D` (RSvW Thm. 8.10)
/-- info: 'SkewBase.BetaRows.shiftHom_schur_natDegree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.shiftHom_schur_natDegree

-- `lem:invariants`, `s_D` determines `s_{D̂}` (RSvW Thm. 8.10)
/-- info: 'SkewBase.BetaRows.schur_hat_eq_of_schur_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.schur_hat_eq_of_schur_eq

-- `lem:invariants`, overlaps of `D̂` (RSvW Lemma 8.5)
/-- info: 'SkewBase.BetaRows.overlaps_hat' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.overlaps_hat

-- `lem:invariants`, `ρ^{(1)}` from the skew Schur function (RSvW Prop. 6.2(ii))
/-- info: 'SkewBase.BetaRows.rowOverlaps_one_eq_of_schur_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.rowOverlaps_one_eq_of_schur_eq

-- `lem:invariants`, every `ρ^{(k)}` from the skew Schur function (RSvW Cor. 8.11)
/-- info: 'SkewBase.BetaRows.rowOverlaps_eq_of_schur_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.rowOverlaps_eq_of_schur_eq

-- `lem:invariants`, overlaps are numbers of shared columns (RSvW Def. 8.2)
/-- info: 'SkewBase.BetaRows.overlap_eq_ncard' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.overlap_eq_ncard

-- `lem:invariants`, `ρ^{(1)}` of a profile
/-- info: 'SkewGluing.Profile.rowOverlapPartition_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Profile.rowOverlapPartition_one

-- `lem:invariants`, `ρ^{(2)}` of a profile
/-- info: 'SkewGluing.Profile.rowOverlapPartition_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Profile.rowOverlapPartition_two

-- `lem:invariants`, every `ρ^{(k)}` of Schur-equal connected diagrams
/-- info: 'SkewGluing.Profile.rowOverlapPartition_eq_of_schur_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Profile.rowOverlapPartition_eq_of_schur_eq

-- `lem:invariants`, a set of consecutive-pair elements is an interval
/-- info: 'SkewBase.finset_run_of_card' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.finset_run_of_card

-- `lem:invariants`, a diagram Schur-equal to a connected one is connected
/-- info: 'SkewBase.BetaRows.connected_of_schur_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.connected_of_schur_eq

-- `lem:invariants`, Schur-equal diagrams have equal area
/-- info: 'SkewBase.BetaRows.area_eq_of_schur_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.area_eq_of_schur_eq

-- `lem:invariants`, area of a diagram Schur-equal to a connected one
/-- info: 'SkewBase.BetaRows.area_eq_of_schur_eq_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.area_eq_of_schur_eq_profile

-- `lem:invariants`, `ρ^{(1)}` of the diagram of a profile
/-- info: 'SkewGluing.Profile.rowOverlaps_one_toBetaRows' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Profile.rowOverlaps_one_toBetaRows

-- `lem:invariants`, `ρ^{(2)}` of the diagram of a profile
/-- info: 'SkewGluing.Profile.rowOverlaps_two_toBetaRows' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewGluing.Profile.rowOverlaps_two_toBetaRows

-- `lem:invariants`, row overlaps counted on cells: row lengths are `ρ^{(1)}`
/-- info: 'SkewBase.rowLengths_eq_overlapPartition_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.rowLengths_eq_overlapPartition_one

-- `lem:invariants`, the area of a cell set is the sum of its row lengths
/-- info: 'SkewBase.card_eq_sum_rowLengths' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.card_eq_sum_rowLengths

-- `lem:invariants`, the cells of beta lists form a skew set
/-- info: 'SkewBase.BetaRows.isSkew_cells' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.isSkew_cells

-- `lem:invariants`, consecutive rows sharing columns are edge-connected
/-- info: 'SkewBase.BetaRows.isEdgeConnected_cells' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.isEdgeConnected_cells

-- `lem:invariants`, columns shared by `k` rows, on cells and on beta lists
/-- info: 'SkewBase.BetaRows.sharedColumns_cells' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.sharedColumns_cells

-- `lem:invariants`, translation invariance of shared columns
/-- info: 'SkewBase.sharedColumns_translate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sharedColumns_translate

-- `lem:invariants`, translation invariance of `ρ^{(k)}`
/-- info: 'SkewBase.overlapPartition_translate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.overlapPartition_translate

-- `lem:invariants`, `ρ^{(k)}` of cells and of beta lists
/-- info: 'SkewBase.BetaRows.overlapPartition_cells' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.overlapPartition_cells

-- `lem:invariants`, the diagram of a profile has the Schur function of the profile
/-- info: 'SkewBase.hasSchur_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasSchur_profile

-- `lem:invariants`, a cell-set diagram Schur-equal to a connected one is connected,
-- with the same area, row lengths, gaps and `ρ^{(k)}`
/-- info: 'SkewBase.isConnectedSkew_of_hasSchur_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.isConnectedSkew_of_hasSchur_eq

-- `lem:invariants`, the beta lists presenting a skew cell set
/-- info: 'SkewBase.cells_presentation' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.cells_presentation

-- `lem:invariants`, every skew cell set has a skew Schur function
/-- info: 'SkewBase.exists_hasSchur_of_isSkew' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.exists_hasSchur_of_isSkew

-- `lem:profiles`, a chain of cells crosses between adjacent rows by a vertical step
/-- info: 'SkewBase.exists_shared_column_of_reach' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.exists_shared_column_of_reach

-- `lem:profiles`, the diagram of a profile: its rows, its contents, its row lengths and shared
-- columns
/-- info: 'SkewBase.mem_cells_profile_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_cells_profile_iff

/-- info: 'SkewBase.mem_cells_profile_iff_content' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.mem_cells_profile_iff_content

/-- info: 'SkewBase.exists_cell_row_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.exists_cell_row_profile

/-- info: 'SkewBase.row_of_mem_cells_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.row_of_mem_cells_profile

/-- info: 'SkewBase.sharedColumns_one_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sharedColumns_one_profile

/-- info: 'SkewBase.sharedColumns_two_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.sharedColumns_two_profile

-- `lem:profiles`, every profile gives a connected diagram
/-- info: 'SkewBase.isConnectedSkew_cells_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.isConnectedSkew_cells_profile

/-- info: 'SkewBase.hasProfile_cells' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasProfile_cells

/-- info: 'SkewBase.HasProfile.isConnectedSkew' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.HasProfile.isConnectedSkew

/-- info: 'SkewBase.HasProfile.translated' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.HasProfile.translated

-- `lem:profiles`, the row lengths and gaps of a diagram with a profile
/-- info: 'SkewBase.HasProfile.sharedColumns_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.HasProfile.sharedColumns_one

/-- info: 'SkewBase.HasProfile.sharedColumns_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.HasProfile.sharedColumns_two

-- `lem:profiles`, every connected diagram has a profile
/-- info: 'SkewBase.BetaRows.exists_profile_cells' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.exists_profile_cells

/-- info: 'SkewBase.exists_hasProfile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.exists_hasProfile

-- `lem:profiles`, the profile of a diagram is unique and the diagram is determined by it
/-- info: 'SkewBase.profile_eq_of_cells_eq_translate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.profile_eq_of_cells_eq_translate

/-- info: 'SkewBase.hasProfile_unique' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasProfile_unique

/-- info: 'SkewBase.eq_translate_of_hasProfile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.eq_translate_of_hasProfile

/-- info: 'SkewBase.hasProfile_profileOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasProfile_profileOf

/-- info: 'SkewBase.profileOf_eq_of_hasProfile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.profileOf_eq_of_hasProfile

/-- info: 'SkewBase.profileOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.profileOf

-- `lem:profiles`, connected diagrams up to translation are the profiles
/-- info: 'SkewBase.translationSetoid' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.translationSetoid

/-- info: 'SkewBase.profileEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.profileEquiv

-- `eq:jt`, empty end rows of a Jacobi–Trudi determinant, and the beta lists of a presentation
/-- info: 'SkewBase.betaDet_first_empty' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.betaDet_first_empty

/-- info: 'SkewBase.betaDet_last_empty' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.betaDet_last_empty

/-- info: 'SkewBase.betaDet_pad' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.betaDet_pad

/-- info: 'SkewBase.BetaRows.beta_of_cells_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.BetaRows.beta_of_cells_eq

-- `eq:jt`, the skew Schur function of a connected cell set does not depend on the presentation
/-- info: 'SkewBase.hasSchur_eq_of_hasProfile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasSchur_eq_of_hasProfile

/-- info: 'SkewBase.hasSchur_iff_of_hasProfile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasSchur_iff_of_hasProfile

/-- info: 'SkewBase.hasSchur_unique' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasSchur_unique

/-- info: 'SkewBase.schurOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.schurOf

/-- info: 'SkewBase.hasSchur_iff_eq_schurOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.hasSchur_iff_eq_schurOf

-- `eq:jt`, the contents of the diagram of a profile and `N_F = x_1 = ∑ r_i - ∑ g_i`

/-- info: 'SkewBase.contents_cells_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.contents_cells_profile

/-- info: 'SkewBase.span_cells_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.span_cells_profile

/-- info: 'SkewBase.xi_zero_eq_sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.xi_zero_eq_sum

/-- info: 'SkewBase.HasProfile.span_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.HasProfile.span_eq

-- `lem:profiles`, rotation reverses both sequences of the profile

/-- info: 'SkewBase.rotate_cells_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.rotate_cells_profile

/-- info: 'SkewBase.HasProfile.rotated' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms SkewBase.HasProfile.rotated
