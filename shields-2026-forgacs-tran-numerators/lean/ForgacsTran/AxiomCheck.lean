/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.Main
import ForgacsTran.Dominance
import ForgacsTran.DominanceCellPartition
import ForgacsTran.PhaseStateDichotomy
import ForgacsTran.Reduction
import ForgacsTran.LinearCase
import ForgacsTran.Necessity
import ForgacsTran.SignAlternation
import ForgacsTran.ClusterContour
import ForgacsTran.EventualDegree
import ForgacsTran.LaurentReduction
import ForgacsTran.Attractor
import ForgacsTran.AttractorBranch
import ForgacsTran.AttractorExpansion
import ForgacsTran.QuadraticDefect
import ForgacsTran.Geometry
import ForgacsTran.DenominatorSequence
import ForgacsTran.AttractorPole
import ForgacsTran.AttractorCoeff
import ForgacsTran.AngularBookkeeping
import ForgacsTran.FTBranchSine
import ForgacsTran.FTBranchProp1
import ForgacsTran.FTBranchAngleBound
import ForgacsTran.FTBranchAngle
import ForgacsTran.QuadraticCase
import ForgacsTran.PhaseCount
import ForgacsTran.FTGeometryAssembly
import ForgacsTran.CubicWitness
import ForgacsTran.CubicWitnessCluster
import ForgacsTran.CubicWitnessInterior
import ForgacsTran.CubicWitnessComposition
import ForgacsTran.CubicPhaseSign
import ForgacsTran.UpperClusterWitness
import ForgacsTran.JointWitness
import ForgacsTran.FTBranchExistence
import ForgacsTran.FTBranchMonotone
import ForgacsTran.FTBranchCritical
import ForgacsTran.FTBranchPencil
import ForgacsTran.FTBranchFunction
import ForgacsTran.FTBranchEndpoint
import ForgacsTran.FTBranchRegularity
import ForgacsTran.FTBranchDeriv
import ForgacsTran.FTBranchTauDeriv
import ForgacsTran.FTMinModulus
import ForgacsTran.FTGeometryExtraction
import ForgacsTran.EndpointRegularity
import ForgacsTran.PoleExpansion
import ForgacsTran.ContourRemainder
import ForgacsTran.Cluster
import ForgacsTran.Amplitude
import ForgacsTran.ViewingAngle
import ForgacsTran.PhaseVariation
import ForgacsTran.WeightedDominance
import ForgacsTran.EndpointDominance
import ForgacsTran.DominanceFT
import ForgacsTran.MainClauses
import ForgacsTran.MainComposition
import ForgacsTran.ClauseThree
import ForgacsTran.ClauseThreeComposition
import ForgacsTran.ClauseThreeMonomial
import ForgacsTran.Consequences
import ForgacsTran.ConsequencesComposition
import ForgacsTran.Sharpness
import ForgacsTran.QuadraticWitness
import ForgacsTran.ClauseThreeWitness
import ForgacsTran.ClauseThreeDefect
import ForgacsTran.ClauseThreeReduction
import ForgacsTran.ClauseThreeQuadraticRay
import ForgacsTran.ClauseThreeRayRemainder
import ForgacsTran.FTBranchZMono
import ForgacsTran.FTBranchLimitPoint
import ForgacsTran.FTBranchGap
import ForgacsTran.FTBranchZRate
import ForgacsTran.FTBranchUpper
import ForgacsTran.FTBranchUpperRefutation
import ForgacsTran.FTBranchLemma5
import ForgacsTran.FTClusterSupply
import ForgacsTran.FTGeometryBranch
import ForgacsTran.PhaseVariationSupply
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.FTMinModulus.PrincipalGap
import ForgacsTran.FTGeometryClosure
import ForgacsTran.AttractorRate
import ForgacsTran.AttractorIndexShift
import ForgacsTran.CubicPhaseDerivative
import ForgacsTran.FTMinModulus.ArgumentCone
import ForgacsTran.EquidistributionCounts
import ForgacsTran.FTMinModulus.RealCritical
import ForgacsTran.CubicMain
import ForgacsTran.SimpleEndpoint
import ForgacsTran.CubicEquidistribution
import ForgacsTran.SimpleWitness
import ForgacsTran.FTGeometryBoundary
import ForgacsTran.EndpointBranch
import ForgacsTran.EndpointPackage
import ForgacsTran.PhaseSupplyProducer
import ForgacsTran.EndpointSeparation
import ForgacsTran.EndpointUpperBinders
import ForgacsTran.EndpointLowerChart
import ForgacsTran.EndpointUpperGap
import ForgacsTran.EndpointCollision
import ForgacsTran.EndpointUpperGeneralN
import ForgacsTran.WeightedDominanceBranchOne
import ForgacsTran.EndpointCofactorBound
import ForgacsTran.EndpointLowerRhoOne
import ForgacsTran.PencilArcSymmetry
import ForgacsTran.RhoOneEndpointFactorization
import ForgacsTran.LowerSeparationNormalized
import ForgacsTran.LowerSeparationQuotient
import ForgacsTran.AmplitudeBand
import ForgacsTran.PhaseBranchSplit
import ForgacsTran.PhaseVariationBlocks
import ForgacsTran.RhoOneDominanceComposition
import ForgacsTran.EndpointUpperOne
import ForgacsTran.EndpointUpperOneBinders
import ForgacsTran.InteriorBranchSeparation
import ForgacsTran.WeightedDominanceBranch
import ForgacsTran.EndpointUpperPackage
import ForgacsTran.BranchCurvature
import ForgacsTran.BranchAmplitude
import ForgacsTran.PhaseDerivativeBound
import ForgacsTran.BranchInteriorC1
import ForgacsTran.BranchStrongClock
import ForgacsTran.BranchClockSpacing
import ForgacsTran.AngularDiscrepancy
import ForgacsTran.MainFT
import ForgacsTran.AngularDiscrepancyFT
import ForgacsTran.AngularBlocks
import ForgacsTran.QuotientDerivBound
import ForgacsTran.InteriorSeparation
import ForgacsTran.InteriorSupply
import ForgacsTran.CubicBranchBridge
import ForgacsTran.CubicInteriorRemainder
import ForgacsTran.CubicClockSpacing
import ForgacsTran.PrincipalSimple
import ForgacsTran.PrincipalSimpleBranch
import ForgacsTran.FTGeometryCone

/-!
# Axiom regression guard

A build-time check that the development stays sorry-free and axiom-clean.  Each
`#guard_msgs in #print axioms …` pins the axiom footprint of a headline result to
Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.  If a
`sorry` or a stray `axiom` ever creeps into a dependency, the reported footprint
changes and `#guard_msgs` turns the mismatch into a build error — so `lake build`
fails rather than silently degrading the "axiom-free" claim.

The guards cover the elementary and combinatorial spine, the Forgacs--Tran branch of
`thm:FT-geometry`, the pole expansion and dominance chain, all three clauses of
`thm:main`, the `sec:conclusion` consequences, and every witness -- a witness matters
here because it is what stops a conditional theorem being vacuous, so a `sorry`
reaching one would be as invisible, and as bad, as a `sorry` in a headline result.

## How coverage is measured, and why the guard list is shorter than the declaration list

`#print axioms` reports the axioms of a declaration's **whole transitive cone**, so a guard on
one result already pins every declaration that result consumes.  Coverage is therefore

    "which declarations lie outside every guarded cone"

and **not** "which declarations are not directly named here".  The two differ by a lot, and in
the direction that manufactures work: measured over the six `FTBranch*` modules, 88
declarations carried 0 direct guards between them, of which 50 were already covered, 38 were
not, and only **15** of those 38 were terminals -- guarding the terminals pinned the other 23.
`FTBranchValue` needed nothing at all: ten declarations, no guard of its own, every one inside
a guarded cone.  A zero in a "guarded" column is a count of direct guards, never a measure of
coverage.

Redoing the measurement:

## Main statements

* Strip `/- -/` (nested) and `--` comments **before** extracting the dependency edges.  A name
  mentioned in a docstring is not a use, and counting one creates a spurious edge that makes a
  declaration look covered when it is not -- the unsafe direction.  A *missed* edge (dot
  notation, `@[simp]` firing by no name at all) only over-guards, which is safe.
* Guard the terminals of the uncovered subgraph, then **re-run reachability from
  `guarded + new`** and check nothing is left.  Without that closure step the minimal set is an
  estimate rather than a fact.
* A `private` declaration is **not addressable** here at all -- `#print axioms` cannot name it.
  Transitive coverage through its consumers is the only route, and the absent guard is not a
  gap.  `QuadraticCase.quadPoly_coeff` is the instance on record.  A private declaration that
  **nothing consumes** is therefore unpinnable outright: no guard can name it and none can
  reach it, so a `sorry` there would be invisible to this file.  Sweep for the pattern with
  "private and used nowhere" and resolve each hit by deleting it or giving it a consumer --
  never by inventing a caller so a guard becomes reachable, which puts a declaration in the
  tree whose only purpose is to be pinned.

## Implementation notes

Count the guards with an **anchored** pattern -- `^#print axioms`, or equivalently
`^#guard_msgs in$`.  The unanchored `#print axioms` is wrong *in this file specifically*,
because the paragraphs above name the command in prose: it reports three more than there are.
That is not an accident of wording.  Any document that records a pattern contains that pattern,
so a self-describing artifact is exactly where a naive count breaks first, and here it will stay
broken as long as the method is written down.

Count the **deduplicated** names, not the lines: `grep -oP '^#print axioms \K\S+' | sort -u |
wc -l`.  A duplicate guard is functionally harmless -- both copies pass -- but it inflates the
one number this file exists to make trustworthy, and it arises *naturally*: two lanes guarding
the same headline result is what a well-covered tree looks like, not a mistake either of them
made.  Two were found this way (`ft_compact_uniform_separation`, `ft_geometry_endpoint_gaps`),
and note that the **anchored** count -- the fix for the previous trap -- reports them happily.
The signal is the disagreement between the anchored count and the deduplicated one, so check
that the line count, the unique-name count and `^#guard_msgs in$` all three agree.

And carry the previous count forward and diff it.  A wrong coverage number looks like a right
one -- it is close, it is plausible, and it moves in the direction such numbers move -- so
disagreement with its own history is the only tell it has.  The inflated `344` above was caught
that way and by nothing else.

A guard claim also carries a time.  This file gates on the whole tree, so it is red whenever any
lane is mid-write, and every guard in it is unenforced while it is: measured red and green
within twenty-five seconds of each other more than once.  Report the build with a timestamp, or
do not report it.

Because the `sec:reduction`--`sec:dominance` analytic inputs are bundled as the `FTInputs`
hypothesis
(`Bridge`) rather than posited as global axioms, even `main_bound` and
`main_bound_interval` report only the standard three: the analytic dependence is
in their *type*, not the ambient axiom set.

## Tags

axiom footprint, regression guard, sorry-free
-/

-- This file is not a Mathlib module and carries no Mathlib copyright header;
-- the package's `mathlibStandardSet` would emit one warning per guard, and
-- `#guard_msgs` captures it, so every guard below would fail on a message that
-- says nothing about an axiom footprint.
set_option linter.style.header false

-- Each guard's docstring has to reproduce `#print axioms` output byte for byte,
-- so it cannot be wrapped; and the file is one guard per pinned declaration, so
-- its length is the count of what is pinned rather than a structural problem.
-- `0` disables the length check rather than naming a bound, which would have to
-- be re-typed every time a guard lands.
set_option linter.style.longLine false
set_option linter.style.longFile 0

open ForgacsTran

-- `subsec:proof` — the counting engine and its wrappers
-- (plus the `sec:geometry` interval/ray inclusions).
/-- info: 'ForgacsTran.exceptionalRoots_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exceptionalRoots_card_le

/-- info: 'ForgacsTran.le_card_roots_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms le_card_roots_filter

/-- info: 'ForgacsTran.ftInterval_subset_posRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftInterval_subset_posRay

-- `sec:dominance`, `thm:weighted-dominance` — the elementary uniform
-- bookkeeping the analytic inputs are run through.
/-- info: 'ForgacsTran.exp_le_pow_of_one_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_le_pow_of_one_add_le

/-- info: 'ForgacsTran.inv_pow_le_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inv_pow_le_exp_neg

/-- info: 'ForgacsTran.cluster_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster_sum_le

/-- info: 'ForgacsTran.exists_gap_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_gap_threshold

/-- info: 'ForgacsTran.exists_cluster_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_cluster_threshold

/-- info: 'ForgacsTran.endpoint_inv_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_inv_pow_le

/-- info: 'ForgacsTran.endpoint_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_pow_le

/-- info: 'ForgacsTran.interior_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_ratio_le

/-- info: 'ForgacsTran.dominance_of_quarters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dominance_of_quarters

-- `sec:reduction` — numerator as initial data, and eventual-degree upper bound.
/-- info: 'ForgacsTran.initial_data_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_data_unique

/-- info: 'ForgacsTran.eventual_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_natDegree_le

-- `subsec:linear-case`, `prop:linear-case` — the excluded elementary case.
/-- info: 'ForgacsTran.linCoeffPoly_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linCoeffPoly_recurrence

/-- info: 'ForgacsTran.linCoeffPoly_exceptional_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linCoeffPoly_exceptional_eq

/-- info: 'ForgacsTran.linCoeffPoly_exceptional_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linCoeffPoly_exceptional_card_le

-- `sec:introduction` — necessity of the numerator dependence, which the
-- paper argues inline in the introduction rather than as a numbered proposition.
/-- info: 'ForgacsTran.exceptional_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exceptional_unbounded

/-- info: 'ForgacsTran.dvd_exceptional_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_exceptional_le

-- Analytic bundle: consistency witness (Bridge).
/-- info: 'ForgacsTran.ftInputsWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftInputsWitness

/-- info: 'ForgacsTran.ftInputs_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftInputs_nonempty

-- Analytic bundle: degree bound derived from the `sec:reduction` recurrence, not assumed (Bridge).
/-- info: 'ForgacsTran.FTInputs.ofRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTInputs.ofRecurrence

-- `sec:introduction` `thm:main` — the headline theorem, with no custom axioms.
/-- info: 'ForgacsTran.main_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound

/-- info: 'ForgacsTran.main_bound_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_interval

/-- info: 'ForgacsTran.main_bound_ofRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_ofRecurrence

/-- info: 'ForgacsTran.interior_distinct_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_distinct_count

-- `linCoeffPoly_ne_zero` lies outside the transitive closure of the guards above, so it is guarded
-- explicitly: without this, a `sorry` there would leave every other guard green.
/-- info: 'ForgacsTran.linCoeffPoly_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linCoeffPoly_ne_zero

/-- info: 'ForgacsTran.linCoeffPoly_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linCoeffPoly_unique

/-- info: 'ForgacsTran.denomConv_dlin_linCoeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denomConv_dlin_linCoeffPoly

/-- info: 'ForgacsTran.ftRay_subset_posRay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRay_subset_posRay

-- `subsec:proof`, `prop:angular-discrepancy` — the intermediate-value count that turns
-- the dominance sign pattern into a supply of distinct interior zeros, and the
-- `FTInputs` constructor that consumes it.
/-- info: 'ForgacsTran.exists_interiorZeros_of_alternating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interiorZeros_of_alternating

/-- info: 'ForgacsTran.FTInputs.ofSignAlternation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTInputs.ofSignAlternation

-- `sec:geometry`, `lem:contour-separation` — the retained cluster contour,
-- invariant under the internal splitting or collision of the roots.
/-- info: 'ForgacsTran.analyticOnNhd_clusterIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms analyticOnNhd_clusterIntegrand

/-- info: 'ForgacsTran.circleIntegral_cluster_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms circleIntegral_cluster_indep

/-- info: 'ForgacsTran.circleIntegral_cluster_indep_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms circleIntegral_cluster_indep_poly

/-- info: 'ForgacsTran.cluster_indep_hypotheses_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster_indep_hypotheses_nonvacuous

-- `sec:reduction`, `prop:initial-data` — the bijection between proper
-- numerators and polynomial initial data, both halves.
/-- info: 'ForgacsTran.exists_denomConv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_denomConv_eq

/-- info: 'ForgacsTran.initialDataEquivFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initialDataEquivFin

-- `sec:reduction`, `lem:eventual-degree` — the attainment half, and the
-- nonvanishing of `thm:main` clause 2 that comes out of the same top
-- coefficient.  The `_of_positive_zeros` pair states both on the paper's own
-- data, with `Q'(0) != 0` discharged from `eq:Q-hypotheses` rather than assumed.
/-- info: 'ForgacsTran.eventual_natDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_natDegree_eq

/-- info: 'ForgacsTran.eventual_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_ne_zero

/-- info: 'ForgacsTran.lambdaQ_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lambdaQ_eq_sum

/-- info: 'ForgacsTran.eventual_natDegree_eq_of_positive_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_natDegree_eq_of_positive_zeros

/-- info: 'ForgacsTran.eventual_ne_zero_of_positive_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_ne_zero_of_positive_zeros

-- `sec:reduction`, `eq:denominator-coordinate-ring` and `lem:laurent-reduction`
-- — the coordinate ring of the denominator curve, the canonical factorization
-- and its uniqueness, the division identity, and the reduced coefficient
-- formula with its index shift.
/-- info: 'ForgacsTran.denomCoordRingEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denomCoordRingEquiv

/-- info: 'ForgacsTran.exists_canonical_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_canonical_factorization

/-- info: 'ForgacsTran.canonical_factorization_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonical_factorization_unique

/-- info: 'ForgacsTran.exists_canonical_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_canonical_division

/-- info: 'ForgacsTran.reduction_coeff_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reduction_coeff_eventually

/-- info: 'ForgacsTran.natDegree_laurentWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_laurentWeight_le

/-- info: 'ForgacsTran.exact_eventual_degree_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_eventual_degree_shift

/-- info: 'ForgacsTran.reduced_tail_linear_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reduced_tail_linear_combination

-- `subsec:isolated-attractors`, `cor:panel-B-attractor` — the certificate for
-- the explicit panel-B data, and the steps it runs through.
/-- info: 'ForgacsTran.panelP_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelP_natDegree

/-- info: 'ForgacsTran.panelP_coeff_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelP_coeff_top

/-- info: 'ForgacsTran.panelP_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelP_ne_zero

/-- info: 'ForgacsTran.panelB64_two_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelB64_two_zeros

/-- info: 'ForgacsTran.exists_panelRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_panelRoot

/-- info: 'ForgacsTran.vieta_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vieta_separation

/-- info: 'ForgacsTran.spectral_ratio_lt_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectral_ratio_lt_third

/-- info: 'ForgacsTran.panelB_attractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelB_attractor

-- `subsec:isolated-attractors`, `prop:isolated-dominant-cancellation` — the
-- dominant-root branch and the coefficient extraction at a simple pole.  These
-- are ingredients; the proposition itself is not assembled from them here.
/-- info: 'ForgacsTran.deriv_ftBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_ftBranch

/-- info: 'ForgacsTran.exists_root_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_root_branch

/-- info: 'ForgacsTran.taylorCoeff_inv_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_inv_sub

/-- info: 'ForgacsTran.coeff_of_simple_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coeff_of_simple_pole

-- `subsec:intro-main`, `thm:main` clause 2 — both parts derived: the interval
-- bound, and the nonvanishing it used to assume.
/-- info: 'ForgacsTran.main_bound_interval_ofRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_interval_ofRecurrence

-- `rem:quadratic-case` — the cited third-party count and its instantiation.
-- The general lemma takes the weight and the orthogonal system as ordinary
-- hypotheses, both of which `quadFavard_orthogonal` discharges outright, so the
-- defect bound reports the standard three like everything else.
/-- info: 'ForgacsTran.card_oddOrderRoots_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_oddOrderRoots_ge

/-- info: 'ForgacsTran.card_oddOrderRoots_linearCombination_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_oddOrderRoots_linearCombination_ge

/-- info: 'ForgacsTran.quadFavard_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadFavard_orthogonal

/-- info: 'ForgacsTran.quadReduced_card_outside_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadReduced_card_outside_le

/-- info: 'ForgacsTran.ftCoeffPoly_quadratic_card_interior_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCoeffPoly_quadratic_card_interior_ge

/-- info: 'ForgacsTran.quadReduced_card_interior_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadReduced_card_interior_ge

/-! ### Results landed since the first sixty-four guards -/

-- `thm:FT-geometry` -- the Forgacs--Tran branch: the angle system, its unique
-- solution, and the strict monotonicity of the modulus along the arc.
/-- info: 'ForgacsTran.exists_unique_ftAngleSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unique_ftAngleSystem

/-- info: 'ForgacsTran.exists_unique_ftAngleSystem_pencil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unique_ftAngleSystem_pencil

/-- info: 'ForgacsTran.exists_unique_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unique_ftTau

/-- info: 'ForgacsTran.not_exists_ftAngleSystem_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_exists_ftAngleSystem_of_le

/-- info: 'ForgacsTran.ftTau_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTau_strictAnti

/-- info: 'ForgacsTran.existsUnique_neg_root_ftCriticalReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms existsUnique_neg_root_ftCriticalReal

/-- info: 'ForgacsTran.exists_ftBranch_real_on_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranch_real_on_arc

/-- info: 'ForgacsTran.exists_ftDen_root_on_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftDen_root_on_arc

/-- info: 'ForgacsTran.ftBranchAt_of_arc_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchAt_of_arc_principal

/-- info: 'ForgacsTran.continuousAt_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousAt_ftTau

/-- info: 'ForgacsTran.ftTau_le_div_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTau_le_div_cos

/-- info: 'ForgacsTran.ftPencilIm_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPencilIm_eq_zero

-- `thm:FT-geometry`, regularity -- the branch is differentiable in the angular
-- parameter, which is what `eq:phase-derivative-bound` is read off.
/-- info: 'ForgacsTran.hasDerivAt_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftTau

/-- info: 'ForgacsTran.hasDerivAt_ftBranchPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchPoint

/-- info: 'ForgacsTran.hasDerivAt_ftBranchAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchAngle

/-- info: 'ForgacsTran.hasDerivAt_ftBranchAngle_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchAngle_principal

/-- info: 'ForgacsTran.hasDerivAt_ftAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngle

/-- info: 'ForgacsTran.hasDerivAt_ftAngleSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngleSum

/-- info: 'ForgacsTran.hasDerivAt_ftAngle_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngle_tau

-- `thm:FT-geometry`, the minimum-modulus property -- the principal pair is the
-- closest root pair to the origin along the arc.
/-- info: 'ForgacsTran.one_lt_norm_zeta_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_lt_norm_zeta_iff

/-- info: 'ForgacsTran.norm_zeta_eq_norm_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_zeta_eq_norm_div

/-- info: 'ForgacsTran.strictMonoOn_negDivPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strictMonoOn_negDivPow

/-- info: 'ForgacsTran.sin_numerator_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_numerator_nonneg

/-- info: 'ForgacsTran.eval_div_pow_eq_of_isRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_div_pow_eq_of_isRoot

-- `eq:endpoint-linear-gap` and the uniform separation -- our own extractions from
-- the endpoint expansion of Forgacs--Tran [Prop. 3], not assumed.
/-- info: 'ForgacsTran.ft_endpoint_linear_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_endpoint_linear_gap

/-- info: 'ForgacsTran.ft_endpoint_fixed_gap_of_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_endpoint_fixed_gap_of_pointwise

/-- info: 'ForgacsTran.ft_compact_uniform_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_compact_uniform_separation

-- `sec:geometry` -- the endpoint expansions the separation is extracted from.
/-- info: 'ForgacsTran.finiteEndpoint_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteEndpoint_expansion

/-- info: 'ForgacsTran.exists_infiniteEndpoint_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_infiniteEndpoint_form

/-- info: 'ForgacsTran.endpoint_root_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_root_identity

/-- info: 'ForgacsTran.infiniteEndpoint_z_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infiniteEndpoint_z_asymptotic

-- `prop:isolated-dominant-cancellation` -- the contour-separated pole expansion and
-- its remainder bound.
/-- info: 'ForgacsTran.taylorCoeff_div_poleExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_div_poleExpansion

/-- info: 'ForgacsTran.taylorCoeff_poleRem_eq_contour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_poleRem_eq_contour

/-- info: 'ForgacsTran.exists_cluster_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_cluster_expansion

/-- info: 'ForgacsTran.exists_poleRem_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_poleRem_bound

/-- info: 'ForgacsTran.norm_contourRemainder_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_contourRemainder_le

/-- info: 'ForgacsTran.exists_contour_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_contour_const

-- `sec:geometry` -- the retained cluster and its residue ratios.
/-- info: 'ForgacsTran.tendsto_residue_ratio_cluster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_residue_ratio_cluster

/-- info: 'ForgacsTran.norm_residue_ratio_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_residue_ratio_limit

/-- info: 'ForgacsTran.exists_lower_cluster_gap_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_lower_cluster_gap_coeff

/-- info: 'ForgacsTran.eventually_cluster_amplitude_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_cluster_amplitude_le

-- `eq:amplitude-zero-count`, `eq:W-def` -- the principal residue amplitude.
/-- info: 'ForgacsTran.amplitude_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amplitude_zero_count

/-- info: 'ForgacsTran.principal_pair_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms principal_pair_contribution

/-- info: 'ForgacsTran.tendsto_residue_ftAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_residue_ftAmp

/-- info: 'ForgacsTran.amplitude_local_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amplitude_local_zero

-- `lem:viewing-angle` -- Radon's bound on a branch of the viewing angle.
/-- info: 'ForgacsTran.viewing_angle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms viewing_angle_bound

/-- info: 'ForgacsTran.viewing_angle_bound_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms viewing_angle_bound_arc

/-- info: 'ForgacsTran.viewing_angle_bound_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms viewing_angle_bound_regular

/-- info: 'ForgacsTran.viewing_angle_bound_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms viewing_angle_bound_polar

/-- info: 'ForgacsTran.hasDerivAt_polarAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_polarAngle

-- `cor:linear-phase-variation`, `eq:linear-phase-variation` -- the phase variation is
-- linear in `deg B_N` with constants free of the numerator.
/-- info: 'ForgacsTran.linear_phase_variation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linear_phase_variation

/-- info: 'ForgacsTran.linear_phase_variation_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linear_phase_variation_regular

/-- info: 'ForgacsTran.phase_variation_le_laurentWeight_of_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_variation_le_laurentWeight_of_arc

/-- info: 'ForgacsTran.numeratorUniform_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numeratorUniform_of_le

/-- info: 'ForgacsTran.numeratorUniform_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numeratorUniform_natDegree_le

-- `thm:weighted-dominance`, `eq:dominance-bound` -- principal-pair dominance on the
-- retained range of `eq:retained-range`.
/-- info: 'ForgacsTran.exists_interior_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interior_dominance

/-- info: 'ForgacsTran.exists_endpoint_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_dominance

/-- info: 'ForgacsTran.exists_dominance_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_dominance_threshold

/-- info: 'ForgacsTran.exists_endpoint_dominance_of_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_dominance_of_split

/-- info: 'ForgacsTran.exists_upper_endpoint_dominance_of_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_endpoint_dominance_of_split

/-- info: 'ForgacsTran.ftPrincipalAmp_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipalAmp_lower_bound

/-- info: 'ForgacsTran.weighted_dominance_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_of_windows

/-- info: 'ForgacsTran.weighted_dominance_ftCoeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_ftCoeffPoly

/-- info: 'ForgacsTran.weighted_dominance_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_of_branch

-- `thm:main` clauses 1 and 2 -- the interior zero set built rather than assumed, and
-- both `exceptionalRoots` bounds off it.
/-- info: 'ForgacsTran.exists_interiorZeros_ftInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interiorZeros_ftInterval

/-- info: 'ForgacsTran.interior_distinct_count_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_distinct_count_of_dominance

/-- info: 'ForgacsTran.main_bound_interval_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_interval_of_dominance

/-- info: 'ForgacsTran.main_bound_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_of_dominance

/-- info: 'ForgacsTran.main_clauses_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_clauses_of_dominance

/-- info: 'ForgacsTran.ftBranchData_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchData_of_dominance

/-- info: 'ForgacsTran.main_of_ftBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_of_ftBranch

/-- info: 'ForgacsTran.main_of_ftDominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_of_ftDominance

/-- info: 'ForgacsTran.main_of_ftBranch_of_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_of_ftBranch_of_geometry

-- `thm:main` clause 3, `prop:angular-discrepancy` -- the numerator-uniform defect, and
-- the phase supply derived from `eq:dominance-bound` rather than assumed.
/-- info: 'ForgacsTran.exists_phaseZeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phaseZeros

/-- info: 'ForgacsTran.exists_phaseZeros_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phaseZeros_sum

/-- info: 'ForgacsTran.angular_distinct_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_distinct_lower

/-- info: 'ForgacsTran.exists_interiorZeros_of_phaseSupply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interiorZeros_of_phaseSupply

/-- info: 'ForgacsTran.phaseSupply_of_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phaseSupply_of_chain

/-- info: 'ForgacsTran.numeratorUniform_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numeratorUniform_defect

/-- info: 'ForgacsTran.clauseThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clauseThree

/-- info: 'ForgacsTran.stripSign_eq_zpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stripSign_eq_zpow

/-- info: 'ForgacsTran.ftRemainder_eq_abs_principal_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRemainder_eq_abs_principal_gap

/-- info: 'ForgacsTran.sign_at_phase_point_of_ftDominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_at_phase_point_of_ftDominance

/-- info: 'ForgacsTran.phaseSupply_of_ftChainGeom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phaseSupply_of_ftChainGeom

/-- info: 'ForgacsTran.clauseThree_of_ftGeometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clauseThree_of_ftGeometry

/-- info: 'ForgacsTran.ftAmp_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmp_X_pow

/-- info: 'ForgacsTran.ftCoeffPoly_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCoeffPoly_X_pow

-- `sec:conclusion` -- equidistribution, the angular clock, and the numerator's clock
-- correction.
/-- info: 'ForgacsTran.equidistribution_of_angular_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equidistribution_of_angular_discrepancy

/-- info: 'ForgacsTran.angular_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_clock

/-- info: 'ForgacsTran.local_clock_spacing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms local_clock_spacing

/-- info: 'ForgacsTran.angular_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_rigidity

/-- info: 'ForgacsTran.numerator_clock_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numerator_clock_correction

/-- info: 'ForgacsTran.angular_discrepancy_of_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_discrepancy_of_counts

/-- info: 'ForgacsTran.equidistribution_of_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equidistribution_of_counts

/-- info: 'ForgacsTran.angular_clock_of_bracketing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_clock_of_bracketing

/-- info: 'ForgacsTran.ft_angular_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_angular_discrepancy

/-- info: 'ForgacsTran.ft_equidistribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_equidistribution

/-- info: 'ForgacsTran.ft_angular_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_angular_clock

/-- info: 'ForgacsTran.ft_angular_clock_numeratorUniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_angular_clock_numeratorUniform

/-- info: 'ForgacsTran.ft_clock_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_clock_correction

-- `rem:quadratic-case`, sharpness of the canonical division threshold.
/-- info: 'ForgacsTran.canonical_division_threshold_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonical_division_threshold_sharp

/-- info: 'ForgacsTran.natDegree_lt_of_lateWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_lt_of_lateWeight

-- The witnesses.  These are what stop the conditional theorems above being vacuous,
-- so a `sorry` reaching one of them would be as invisible, and as bad, as a `sorry`
-- in a headline result.
/-- info: 'ForgacsTran.dominanceSupply_cheb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dominanceSupply_cheb

/-- info: 'ForgacsTran.exists_interiorZeros_cheb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interiorZeros_cheb

/-- info: 'ForgacsTran.quad_ftRemainder_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quad_ftRemainder_eq_zero

/-- info: 'ForgacsTran.witness_ftBranchData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_ftBranchData

/-- info: 'ForgacsTran.witness_main_clauses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_main_clauses

/-- info: 'ForgacsTran.witness_dominance_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_dominance_pow

/-- info: 'ForgacsTran.witness_ftChainGeom_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_ftChainGeom_pow

/-- info: 'ForgacsTran.witness_phaseSupply_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_phaseSupply_pow

/-- info: 'ForgacsTran.witness_clauseThree_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_clauseThree_uniform


-- `thm:FT-geometry` — the assembly.  Every result below is a composition over
-- named hypotheses standing for `Forgacs2017RationalDenominator`'s lemmas, so
-- the cited half sits in each theorem's *type* and not in the axiom set.

/-- info: 'ForgacsTran.ft_principal_pair_of_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_principal_pair_of_norm_le

/-- info: 'ForgacsTran.ft_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry

/-- info: 'ForgacsTran.ft_geometry_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_unbounded

/-- info: 'ForgacsTran.ft_geometry_compact_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_compact_separation

/-- info: 'ForgacsTran.ft_geometry_endpoint_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_endpoint_gaps

-- `eq:principal-pair` differentiated on the arc, and the interior hypothesis of
-- `weighted_dominance_of_branch` discharged from it.
/-- info: 'ForgacsTran.hasDerivAt_ftPrincipal_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftPrincipal_ftTau

/-- info: 'ForgacsTran.ftPrincipal_hasDerivAt_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_hasDerivAt_of_subset

-- `thm:FT-geometry`'s hypothesis set is inhabited, so the conditional theorem is
-- not conditional on a set nothing can meet.
/-- info: 'ForgacsTran.ft_geometry_hypotheses_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_hypotheses_satisfiable

-- `ft_geometry`'s `hbranch` and `hτpos`, discharged at the branch's own data.
/-- info: 'ForgacsTran.ft_branch_root_and_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_branch_root_and_pos

-- `thm:main` clause 3 in the exceptional-count idiom -- the defect decomposed, with
-- `C_0` and `C_1` bound before the numerator, and `deg B_N` shown unbounded so the
-- `C_1` term is exercised (`eq:canonical-Laurent-factorization`).
/-- info: 'ForgacsTran.exceptionalRoots_numeratorUniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exceptionalRoots_numeratorUniform

/-- info: 'ForgacsTran.clauseThree_exceptionalRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clauseThree_exceptionalRoots

/-- info: 'ForgacsTran.exceptionalRoots_numeratorUniform_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exceptionalRoots_numeratorUniform_witness

/-- info: 'ForgacsTran.laurentWeight_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms laurentWeight_X_pow

/-- info: 'ForgacsTran.natDegree_laurentWeight_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_laurentWeight_X_pow

/-- info: 'ForgacsTran.natDegree_laurentWeight_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_laurentWeight_unbounded

-- `thm:main` clause 2(i) composed for a proper bivariate numerator
-- (`eq:reduction-coeff` + `lem:eventual-degree`), and clause 3 with it discharged.
/-- info: 'ForgacsTran.laurentWeight_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms laurentWeight_one

/-- info: 'ForgacsTran.eventual_coeffPoly_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_coeffPoly_ne_zero

/-- info: 'ForgacsTran.eventual_coeffPoly_ne_zero_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_coeffPoly_ne_zero_nonvacuous

/-- info: 'ForgacsTran.exceptionalRoots_numeratorUniform_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exceptionalRoots_numeratorUniform_of_ne_zero

-- `rem:degree-attainment` in clause 3's vocabulary: the onset is not a function of
-- `deg B_N`, so it must stay inside the quantifier over numerators.
/-- info: 'ForgacsTran.laurentWeight_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms laurentWeight_C

/-- info: 'ForgacsTran.natDegree_lateWeightPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_lateWeightPoly

/-- info: 'ForgacsTran.onset_not_uniform_in_natDegree_laurentWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms onset_not_uniform_in_natDegree_laurentWeight

-- The monomial shift at non-constant modulus, which is what an `r > 1` witness needs
-- (`eq:principal-decomposition`); the `tau = 1` form covers the Favard pencil alone.
/-- info: 'ForgacsTran.ftRemainder_X_pow_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRemainder_X_pow_of_pos

-- The `r > 1` branch of `thm:FT-geometry`: a pencil whose principal modulus is not
-- constant, which `rem:quadratic-case`'s Favard pencil cannot exhibit.
/-- info: 'ForgacsTran.rayTau_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rayTau_pos

/-- info: 'ForgacsTran.rayZ_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rayZ_mul_sq

/-- info: 'ForgacsTran.rayTau_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rayTau_mul

/-- info: 'ForgacsTran.rayDen_eval_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rayDen_eval_principal

/-- info: 'ForgacsTran.ray_exp_sub_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_exp_sub_cos

/-- info: 'ForgacsTran.ray_derivative_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_derivative_eval

/-- info: 'ForgacsTran.ray_ftAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_ftAmp

/-- info: 'ForgacsTran.ray_norm_ftAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_norm_ftAmp

/-- info: 'ForgacsTran.ray_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_polar

-- The concrete branch a `weighted_dominance_of_branch` witness is being built on.
/-- info: 'ForgacsTran.ftDen_cubicQ_eval_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftDen_cubicQ_eval_principal

-- `Forgacs2017RationalDenominator` Lemmas 3--4 and Prop. 1, the branch monotonicity
-- `thm:FT-geometry`'s `hzmono` is supplied from, and the angle identification its
-- Prop. 1 closes on.  The first is consumed by the Prop. 1 chain, so its footprint
-- is load-bearing for work outside its own module.
/-- info: 'ForgacsTran.ftBranchZ_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchZ_strictMonoOn

/-- info: 'ForgacsTran.ftProp1_angle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftProp1_angle_eq

-- `sec:consequences` -- the interior decomposition the discrepancy bound runs on.
/-- info: 'ForgacsTran.interior_cos_decomposition_on_subarc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_cos_decomposition_on_subarc

-- `Forgacs2017RationalDenominator` Prop. 3 Case 2, and the two primitives it is
-- built from: the `rho`-th-root localization, and the passage from a first-order
-- bound on the branch radius' derivative to the second-order rate.
/-- info: 'ForgacsTran.cluster_normalized_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster_normalized_expansion

/-- info: 'ForgacsTran.exists_root_of_unity_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_root_of_unity_close

/-- info: 'ForgacsTran.abs_sub_linear_le_of_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_sub_linear_le_of_deriv_bound

-- `Forgacs2017RationalDenominator` Lemma 6 at the lower endpoint, and its two
-- witnesses.  The second reaches `(deg Q, r) = (2,1)`, which `thm:FT-geometry`
-- excludes because `tau` is constant there -- the limit statement still holds,
-- and the witness is what stops that being an assertion rather than a fact.
/-- info: 'ForgacsTran.exists_tendsto_ftBranchZ_arc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftBranchZ_arc_zero

/-- info: 'ForgacsTran.exists_tendsto_ftBranchZ_arc_zero_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftBranchZ_arc_zero_nonvacuous

/-- info: 'ForgacsTran.exists_tendsto_ftBranchZ_arc_zero_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftBranchZ_arc_zero_quadratic

-- `lem:amplitude-divisor`, the remaining displays.  `eq:amplitude-zero-count` and
-- `eq:W-local-zero` are guarded above; these are the first sentence, the endpoint
-- form in its three shapes, the subarc form, and `eq:phase-derivative-bound`.
/-- info: 'ForgacsTran.ftAmp_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmp_eq_zero_iff

/-- info: 'ForgacsTran.amplitude_endpoint_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amplitude_endpoint_form

/-- info: 'ForgacsTran.amplitude_endpoint_form_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amplitude_endpoint_form_origin

/-- info: 'ForgacsTran.amplitude_endpoint_form_of_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amplitude_endpoint_form_of_order

/-- info: 'ForgacsTran.exists_amplitude_factor_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_amplitude_factor_on

/-- info: 'ForgacsTran.exists_phase_derivative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phase_derivative_bound

/-- info: 'ForgacsTran.exists_phase_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phase_window

/-- info: 'ForgacsTran.exists_unique_phase_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unique_phase_zero

/-- info: 'ForgacsTran.exists_unique_phase_zero_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unique_phase_zero_nonvacuous

/-- info: 'ForgacsTran.hasDerivAt_ftContourRem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftContourRem

/-- info: 'ForgacsTran.norm_smul_ftContourRemDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_smul_ftContourRemDeriv_le

/-- info: 'ForgacsTran.exists_amplitude_floor_on_subarc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_amplitude_floor_on_subarc

/-- info: 'ForgacsTran.exists_tau_slope_bound_on_subarc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tau_slope_bound_on_subarc

/-- info: 'ForgacsTran.strictMonoOn_ftPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strictMonoOn_ftPhase

/-- info: 'ForgacsTran.phase_cos_deriv_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_cos_deriv_pos

/-- info: 'ForgacsTran.phase_cos_sign_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_cos_sign_change

/-- info: 'ForgacsTran.principal_term_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms principal_term_cos

/-- info: 'ForgacsTran.exists_polar_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_polar_phase

/-- info: 'ForgacsTran.local_clock_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms local_clock_rate

/-- info: 'ForgacsTran.exists_two_consecutive_phase_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_two_consecutive_phase_zeros

/-- info: 'ForgacsTran.exists_two_consecutive_phase_zeros_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_two_consecutive_phase_zeros_nonvacuous

/-- info: 'ForgacsTran.ray_denominator_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_denominator_recurrence

/-- info: 'ForgacsTran.ray_coeffPoly_on_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_coeffPoly_on_arc

/-- info: 'ForgacsTran.ray_ftRemainder_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_ftRemainder_eq_zero

-- `lem:amplitude-divisor`'s endpoint multiplicity `k`.  `rootMultiplicity_ftCritical`
-- makes `k - 1` a fact about the `z`-free `E`; these evaluate it at a zero of `Q`,
-- giving `k = rho`, and give the `2` that the paper's `max` guards.
/-- info: 'ForgacsTran.ftCritical_factor_of_rootFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCritical_factor_of_rootFactor

/-- info: 'ForgacsTran.rootMultiplicity_ftDen_eq_of_rootFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootMultiplicity_ftDen_eq_of_rootFactor

/-- info: 'ForgacsTran.two_le_rootMultiplicity_ftDen_of_ftCritical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_le_rootMultiplicity_ftDen_of_ftCritical

-- `lem:amplitude-divisor`, the `k <= 2` half at the upper endpoint with `r = 1`:
-- what a triple root would force, and the positivity that forbids it.  The first
-- guard's message wraps -- it is written from the probe, not from a neighbour.
/-- info: 'ForgacsTran.eval_derivative_two_eq_zero_of_three_le_rootMultiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_two_eq_zero_of_three_le_rootMultiplicity

/-- info: 'ForgacsTran.posShiftProd_deriv_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms posShiftProd_deriv_pos

/-- info: 'ForgacsTran.abs_le_of_abs_sin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_le_of_abs_sin_le

/-- info: 'ForgacsTran.phase_quantization_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_quantization_error

/-- info: 'ForgacsTran.phase_quantization_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_quantization_identity

-- `lem:amplitude-divisor`, `k = 2` at the finite upper endpoint, closed: the
-- direct-form positivity induction, the connector to the pencil numerator, and
-- the result the two combine to.
/-- info: 'ForgacsTran.negShiftProd_deriv_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negShiftProd_deriv_sign

/-- info: 'ForgacsTran.eval_derivative_two_ftRootPolyReal_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_two_ftRootPolyReal_ne_zero

/-- info: 'ForgacsTran.eval_derivative_two_ftRootPoly_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_two_ftRootPoly_ne_zero

/-- info: 'ForgacsTran.rootMultiplicity_ftDen_le_two_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootMultiplicity_ftDen_le_two_of_nonpos

/-- info: 'ForgacsTran.phase_mvt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_mvt_bound

/-- info: 'ForgacsTran.phase_taylor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_taylor_bound

-- `lem:amplitude-divisor` at the lower endpoint: the smallest zero of `Q'` sits
-- strictly between the smallest two distinct zeros of `Q`.  One gap of Rolle plus
-- the uniform-sign nonvanishing below it -- no degree count, no distinctness.
/-- info: 'ForgacsTran.exists_eval_derivative_eq_zero_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_eval_derivative_eq_zero_between

/-- info: 'ForgacsTran.eval_derivative_ne_zero_of_lt_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_ne_zero_of_lt_roots

/-- info: 'ForgacsTran.hasDerivAt_im_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_im_logDeriv

/-- info: 'ForgacsTran.exists_phase_second_derivative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phase_second_derivative_bound

/-- info: 'ForgacsTran.exists_phase_taylor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phase_taylor_bound

-- The r > 1 witness: PhaseSupply on a pencil whose principal modulus is not constant,
-- and the count it delivers (thm:main clause 3, prop:angular-discrepancy).
/-- info: 'ForgacsTran.ray_ftPrincipalAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_ftPrincipalAmp

/-- info: 'ForgacsTran.ray_polar_ftPrincipal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_polar_ftPrincipal

/-- info: 'ForgacsTran.rayZ_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rayZ_strictMonoOn

/-- info: 'ForgacsTran.rayZ_mem_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rayZ_mem_Ioi

/-- info: 'ForgacsTran.ftCoeffPoly_mem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCoeffPoly_mem_range

/-- info: 'ForgacsTran.witness_ftChainGeom_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_ftChainGeom_ray

/-- info: 'ForgacsTran.witness_dominance_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_dominance_ray

/-- info: 'ForgacsTran.witness_phaseSupply_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_phaseSupply_ray

/-- info: 'ForgacsTran.witness_clauseThree_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_clauseThree_ray


-- The log-derivative of a root product, `P'(t) = P(t) * S1(t)` at a non-root.
-- One application of `Polynomial.derivative_prod`; the first of the two
-- identities `lem:amplitude-divisor`'s lower endpoint runs on.
/-- info: 'ForgacsTran.eval_derivative_eq_mul_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_eq_mul_logDeriv

-- `HasDerivAt` through a `Multiset` sum -- absent from Mathlib at the pin, where
-- `HasDerivAt.sum` is `Finset`-only.  Reusable on its own, and what lets a root
-- product be differentiated with multiplicity.
/-- info: 'ForgacsTran.hasDerivAt_multiset_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_multiset_sum

/-- info: 'ForgacsTran.ft_local_strong_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_local_strong_clock

/-- info: 'ForgacsTran.ft_local_strong_clock_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_local_strong_clock_rate

/-- info: 'ForgacsTran.ft_local_strong_clock_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_local_strong_clock_nonvacuous

-- `lem:amplitude-divisor` at the lower endpoint: the second log-derivative
-- identity, obtained by differentiating the first rather than by a leave-two-out
-- sum, and the three-inequality contradiction it feeds.
/-- info: 'ForgacsTran.eval_derivative_two_eq_mul_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_two_eq_mul_logDeriv

/-- info: 'ForgacsTran.not_triple_root_of_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_triple_root_of_interior

/-- info: 'ForgacsTran.eval_eq_zero_of_re_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_eq_zero_of_re_eq_zero

/-- info: 'ForgacsTran.re_scaled_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_scaled_eq_zero

/-- info: 'ForgacsTran.ftCoeffPoly_eval_eq_zero_of_phase_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCoeffPoly_eval_eq_zero_of_phase_zero

-- Connector (4): the critical point lies in the first gap.  IVT between the
-- smallest zero of `Q`, where `E = x1*Q'(x1) < 0`, and the smallest zero of `Q'`,
-- where `E = -r*Q > 0`.
/-- info: 'ForgacsTran.exists_ftCritical_zero_in_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftCritical_zero_in_gap

/-- info: 'ForgacsTran.eval_derivative_neg_at_smallest_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_neg_at_smallest_root

/-- info: 'ForgacsTran.isolated_dominant_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isolated_dominant_cancellation

/-- info: 'ForgacsTran.exists_amplitude_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_amplitude_factorization

/-- info: 'ForgacsTran.exists_uniform_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_uniform_expansion

/-- info: 'ForgacsTran.exists_unique_root_nearby' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unique_root_nearby

/-- info: 'ForgacsTran.taylorCoeff_div_ftDen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_div_ftDen

/-- info: 'ForgacsTran.div_ftDen_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms div_ftDen_eq

/-- info: 'ForgacsTran.ftCoeffPoly_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCoeffPoly_eq

/-- info: 'ForgacsTran.norm_ftCoeff_sub_amp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_ftCoeff_sub_amp_le

/-- info: 'ForgacsTran.factoredOn_ftDen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms factoredOn_ftDen

-- Connector (4) wired: the critical point in the first gap with no zero of `Q'`
-- assumed -- Rolle supplies it, the sign lemmas fix the three signs, IVT closes.
/-- info: 'ForgacsTran.eval_neg_in_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_neg_in_gap

/-- info: 'ForgacsTran.exists_ftCritical_zero_in_first_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftCritical_zero_in_first_gap

-- The r > 1 witness over weights of every degree: deg B varies on the ray too, and the
-- clause-3 constants stay put (thm:main clause 3).
/-- info: 'ForgacsTran.ray_polar_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_polar_pow

/-- info: 'ForgacsTran.ray_ftRemainder_pow_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ray_ftRemainder_pow_eq_zero

/-- info: 'ForgacsTran.witness_ftChainGeom_ray_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_ftChainGeom_ray_pow

/-- info: 'ForgacsTran.witness_phaseSupply_ray_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_phaseSupply_ray_pow

/-- info: 'ForgacsTran.witness_clauseThree_ray_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_clauseThree_ray_pow


-- Connector (1): the sign split at an interior point.  The interval is used here
-- and nowhere else -- it is what puts exactly one term of each sum on the far
-- side.  Both rewrites are unconditional.
/-- info: 'ForgacsTran.logDeriv_split_in_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logDeriv_split_in_gap

/-- info: 'ForgacsTran.panelDen_eq_ftDen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelDen_eq_ftDen

/-- info: 'ForgacsTran.panelDenQ_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelDenQ_eval_zero

-- `subsec:proof`, `prop:angular-discrepancy` -- the phase count.  The helpers it runs
-- on (`exists_phase_points`, `exists_phase_points_of_length`,
-- `alternating_of_consecutive_signs`, `principal_sign_at_phase_point`) are covered
-- transitively by `exists_interiorZeros_of_dominance` and are not guarded again.
/-- info: 'ForgacsTran.exists_interiorZeros_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interiorZeros_of_dominance

/-- info: 'ForgacsTran.count_add_card_le_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms count_add_card_le_natDegree

/-- info: 'ForgacsTran.phase_alternating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_alternating

/-- info: 'ForgacsTran.card_le_count_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_le_count_filter

/-- info: 'ForgacsTran.card_le_natDegree_of_isRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_le_natDegree_of_isRoot


-- `rem:quadratic-case` and the `deg Q = 2`, `r = 1` geometry `thm:FT-geometry` excludes.
-- The recurrence machinery (`quadFavard_add_two`, `quadFavard_monic_natDegree`,
-- `quadFavard_eval_eq_zero_iff`, `quad_tau_facts`, `quadRoot_angle_mem`) is covered
-- transitively by the results below.
/-- info: 'ForgacsTran.quadDen_eval_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadDen_eval_principal

/-- info: 'ForgacsTran.quadDen_eq_sq_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadDen_eq_sq_lower

/-- info: 'ForgacsTran.quadDen_eq_sq_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadDen_eq_sq_upper

/-- info: 'ForgacsTran.quadratic_z_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadratic_z_strictMonoOn

/-- info: 'ForgacsTran.card_Ioo_ge_of_card_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_Ioo_ge_of_card_Icc

/-- info: 'ForgacsTran.quad_denominator_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quad_denominator_recurrence

/-- info: 'ForgacsTran.quadFavard_eval_eq_coeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadFavard_eval_eq_coeffPoly

/-- info: 'ForgacsTran.quadFavard_roots_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadFavard_roots_card

/-- info: 'ForgacsTran.quadFavard_interlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadFavard_interlace

/-- info: 'ForgacsTran.quadFavard_root_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadFavard_root_mem_Ioo


-- Connector (2): the triple-root obstruction at general `r`.  One statement, two
-- proofs -- the `r = 1` case holds for a different reason, because N-subtraction
-- makes `X^(r-2) * X^2 = X^r` false there.  The message wraps; written from the
-- probe.
/-- info: 'ForgacsTran.eval_derivative_two_relation_of_three_le_rootMultiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_two_relation_of_three_le_rootMultiplicity

-- Connector (3): the pencil numerator over R and over C.  Everything crosses
-- through `derivative_map` and `eval2_at_apply`; no analysis.
/-- info: 'ForgacsTran.ftRootPoly_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRootPoly_eq_map

/-- info: 'ForgacsTran.eval_iterate_derivative_ftRootPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_iterate_derivative_ftRootPoly

/-- info: 'ForgacsTran.relations_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relations_ofReal

-- `thm:FT-geometry`, the angle system.  These four are the terminals of the part of
-- `FTBranchAngle` no guarded result reaches; the other nine uncovered declarations in it
-- are in their cones.
/-- info: 'ForgacsTran.continuous_ftArccot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuous_ftArccot

/-- info: 'ForgacsTran.ftAngle_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAngle_ratio

/-- info: 'ForgacsTran.tendsto_ftArccot_atBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftArccot_atBot

/-- info: 'ForgacsTran.tendsto_ftArccot_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftArccot_atTop


-- `thm:FT-geometry`, the angle bound (Forgacs--Tran's (17) and their Case 1).
/-- info: 'ForgacsTran.card_le_one_of_lt_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_le_one_of_lt_pi

/-- info: 'ForgacsTran.ftPhaseWeight_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPhaseWeight_zero

/-- info: 'ForgacsTran.sin_two_pi_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_two_pi_sub


-- `thm:FT-geometry`, the Prop. 1 chain.  `ftProp1_nonstrict_insufficient` records that the
-- nonstrict hypothesis does not suffice, so it is a deliverable rather than a helper.
/-- info: 'ForgacsTran.ftBranchAt_of_arc_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchAt_of_arc_range

/-- info: 'ForgacsTran.ftChordProd_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftChordProd_pos

/-- info: 'ForgacsTran.ftProp1_nonstrict_insufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftProp1_nonstrict_insufficient


-- `thm:FT-geometry`, the sine inequalities behind the angle bound.
/-- info: 'ForgacsTran.abs_sin_nat_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_sin_nat_mul_le

/-- info: 'ForgacsTran.sin_nat_mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_nat_mul_lt

/-- info: 'ForgacsTran.sin_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_sum_le


-- The assembly: `Forgacs2017RationalDenominator` Case 2 at rho = 1.  The two
-- log-derivative identities, the split, and the three-inequality contradiction
-- spent together.  No interlacing and no location of any zero of `Q''`.
/-- info: 'ForgacsTran.not_relations_in_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_relations_in_gap

-- The wrapper: `lem:amplitude-divisor`'s `k <= 2` at the lower endpoint, rho = 1,
-- at the paper's own objects.  `hgt` encodes rho = 1 in the statement -- a second
-- copy of the smallest root would sit in the erased multiset and would have to
-- exceed `t`, which it cannot.
/-- info: 'ForgacsTran.not_three_le_rootMultiplicity_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_three_le_rootMultiplicity_of_gap

/-- info: 'ForgacsTran.panelDenomCoeff_eq_ftDenom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelDenomCoeff_eq_ftDenom

/-- info: 'ForgacsTran.denomConv_panelP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denomConv_panelP

-- The upper endpoint: a unimodular limit is invisible to the modulus.  This is
-- what carries the lower-endpoint modulus chain to `r > 1`, where the small roots
-- go to 0 along the r-th roots of -1 and the complex expansion about 1 is false.
/-- info: 'ForgacsTran.abs_norm_sub_one_add_re_mul_le_of_unimodular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_norm_sub_one_add_re_mul_le_of_unimodular

/-! ### Tree-wide cone sweep

The terminals of every part of the tree no other guard reaches, module by module.  Each
was probed individually; every declaration below them is pinned transitively and is not
guarded again.  See the cone method above for how the set was computed and verified. -/

-- `Amplitude`
/-- info: 'ForgacsTran.ftAmp_eq_div_gDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmp_eq_div_gDeriv

/-- info: 'ForgacsTran.im_logDeriv_eq_phase_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms im_logDeriv_eq_phase_deriv

-- `AngularBookkeeping`
/-- info: 'ForgacsTran.card_blocks_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_blocks_le

/-- info: 'ForgacsTran.image_Ioo_eq_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms image_Ioo_eq_Ioo

-- `AttractorCoeff`
/-- info: 'ForgacsTran.panelP_denomConv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelP_denomConv

/-- info: 'ForgacsTran.panelP_leadingCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelP_leadingCoeff

-- `AttractorPole`
/-- info: 'ForgacsTran.rootMultiplicity_monomial_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootMultiplicity_monomial_mul

-- `ClauseThree`
/-- info: 'ForgacsTran.card_amplitudeZeros_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_amplitudeZeros_le

-- `Cluster`
/-- info: 'ForgacsTran.clusterOmega_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_injOn

/-- info: 'ForgacsTran.clusterOmega_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_re

/-- info: 'ForgacsTran.norm_cluster_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_cluster_root

-- `Consequences`
/-- info: 'ForgacsTran.c1_prefactor_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c1_prefactor_two_sided

/-- info: 'ForgacsTran.clock_correction_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clock_correction_of_const

/-- info: 'ForgacsTran.clock_denominator_term_indep_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clock_denominator_term_indep_of_weight

/-- info: 'ForgacsTran.exists_c1_interior_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_c1_interior_remainder_bound

/-- info: 'ForgacsTran.exists_unique_zero_near_phase_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unique_zero_near_phase_point

-- `ContourRemainder`
/-- info: 'ForgacsTran.norm_smul_contourRemainder_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_smul_contourRemainder_le

/-- info: 'ForgacsTran.principal_decomposition_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms principal_decomposition_of_pair

-- `DenominatorSequence`
/-- info: 'ForgacsTran.existsUnique_ftH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms existsUnique_ftH

/-- info: 'ForgacsTran.exists_reduced_tail_linear_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_reduced_tail_linear_combination

-- `EndpointDominance`
/-- info: 'ForgacsTran.endpoint_remainder_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_remainder_split

/-- info: 'ForgacsTran.interior_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_remainder_bound

-- `EndpointRegularity`
/-- info: 'ForgacsTran.leadingCoeff_ne_zero_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leadingCoeff_ne_zero_independent

/-- info: 'ForgacsTran.leadingCoeff_ratio_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leadingCoeff_ratio_pow_eq_one

/-- info: 'ForgacsTran.z_endpoint_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms z_endpoint_order

-- `EventualDegree`
/-- info: 'ForgacsTran.leadCoeffPoly_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leadCoeffPoly_natDegree_le

-- `LaurentReduction`
/-- info: 'ForgacsTran.clearedRestrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clearedRestrict_eq

/-- info: 'ForgacsTran.denomCoordRingEquiv_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denomCoordRingEquiv_mk

/-- info: 'ForgacsTran.eventual_natDegree_le_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventual_natDegree_le_shift

-- `Main`
/-- info: 'ForgacsTran.main_bound_ofBivariateNumerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_ofBivariateNumerator

-- `PhaseVariation`
/-- info: 'ForgacsTran.phase_variation_le_laurentWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_variation_le_laurentWeight

-- `QuadraticCase`
/-- info: 'ForgacsTran.quadFavard_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadFavard_zero

-- `QuadraticDefect`
/-- info: 'ForgacsTran.quadReduced_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quadReduced_natDegree

-- `Reduction`
/-- info: 'ForgacsTran.initialDataEquivFin_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initialDataEquivFin_apply

/-- info: 'ForgacsTran.initialDataEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initialDataEquiv_apply

-- `Sharpness`
/-- info: 'ForgacsTran.exists_lateDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_lateDrop

/-- info: 'ForgacsTran.reduced_degree_bound_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reduced_degree_bound_attained

-- `ViewingAngle`
/-- info: 'ForgacsTran.stripSign_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stripSign_ne_zero

/-- info: 'ForgacsTran.strip_lineViewingAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strip_lineViewingAngle

/-- info: 'ForgacsTran.viewing_angle_bound_line_le_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms viewing_angle_bound_line_le_pi

-- `WeightedDominance`
/-- info: 'ForgacsTran.exists_window_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_window_threshold


-- Prop. 3 Case 2, the principal leg closed: the branch's tau-rate transferred to
-- the principal point's expansion, with no hypothesis about tau assumed.
/-- info: 'ForgacsTran.exists_principal_expansion_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_principal_expansion_of_branch

-- `thm:FT-geometry`, identifying the endpoint limit.  These pin the branch radius
-- at the lower endpoint of the arc, which is what the `k` identification under
-- `lem:amplitude-divisor` rests on: at a repeated smallest zero the limit IS that
-- zero, and at a simple one it is a critical point strictly inside the first gap.
/-- info: 'ForgacsTran.tendsto_ftTau_nhdsGT_zero_of_repeated_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftTau_nhdsGT_zero_of_repeated_min

/-- info: 'ForgacsTran.exists_tendsto_ftTau_lt_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftTau_lt_second

/-- info: 'ForgacsTran.ftTau_lt_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTau_lt_of_lt

/-- info: 'ForgacsTran.exists_bound_ftTau_sub_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_ftTau_sub_linear

/-! ### Cone sweep, second pass

The terminals in the modules that had been quiet for half an hour or more.  Left for their
owners: the modules under active edit at the time (`CubicWitness`, `FTMinModulus`,
`FTBranchGap`, `DominanceFT`) -- a guard naming a declaration mid-rename breaks the build
for every lane, not just the one renaming it. -/

-- `ConsequencesComposition`
/-- info: 'ForgacsTran.abs_phase_cos_deriv_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_phase_cos_deriv_lower

/-- info: 'ForgacsTran.count_lower_of_phase_turning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms count_lower_of_phase_turning

/-- info: 'ForgacsTran.eventually_phase_cos_deriv_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_phase_cos_deriv_gap

/-- info: 'ForgacsTran.ftWindow_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftWindow_subset

/-- info: 'ForgacsTran.transported_error_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transported_error_deriv_bound

-- `FTBranchCritical`
/-- info: 'ForgacsTran.exists_ftCriticalReal_root_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftCriticalReal_root_between

-- `FTBranchEndpoint`
/-- info: 'ForgacsTran.exists_tendsto_ftTau_nhdsGT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftTau_nhdsGT_zero

/-- info: 'ForgacsTran.exists_tendsto_ftTau_r_one_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftTau_r_one_witness

/-- info: 'ForgacsTran.ftArcPoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftArcPoint_zero

-- `FTBranchExistence`
/-- info: 'ForgacsTran.not_exists_ftAngleSystem_two_two_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_exists_ftAngleSystem_two_two_zero

-- `FTBranchFunction`
/-- info: 'ForgacsTran.ftTau_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTau_eq_of

-- `FTBranchLimitPoint`
/-- info: 'ForgacsTran.tendsto_ftTau_slope_nhdsGT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftTau_slope_nhdsGT_zero

-- `FTBranchRegularity`
/-- info: 'ForgacsTran.continuousAt_ftTau_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousAt_ftTau_principal

/-- info: 'ForgacsTran.differentiableOn_ftTau_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differentiableOn_ftTau_principal

/-- info: 'ForgacsTran.ftTauDeriv_neg_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTauDeriv_neg_principal

/-- info: 'ForgacsTran.hasDerivAt_ftBranchPoint_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchPoint_principal

-- `FTBranchZMono`
/-- info: 'ForgacsTran.ftBranchZ_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchZ_strictAntiOn

-- `Geometry`
/-- info: 'ForgacsTran.eval_ftDen_ne_zero_of_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ftDen_ne_zero_of_norm_eq

/-- info: 'ForgacsTran.re_le_cos_pi_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_le_cos_pi_div

-- `PoleExpansion`
/-- info: 'ForgacsTran.hasDerivAt_ftContourRem_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftContourRem_comp

/-- info: 'ForgacsTran.taylorCoeff_poleRem_eq_ftContourRem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_poleRem_eq_ftContourRem

-- `DominanceFT` -- the last two terminals outside a cone in a settled module.
/-- info: 'ForgacsTran.exists_interior_amplitude_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interior_amplitude_data

/-- info: 'ForgacsTran.ftRemainder_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRemainder_split

/-- info: 'ForgacsTran.panelB64_eq_restriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelB64_eq_restriction

/-- info: 'ForgacsTran.panelB64_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelB64_eq_zero_iff

-- The lower half of the first-gap location: every positive zero of `E` lies
-- strictly above the smallest zero of `Q` when that zero is simple.
-- `FTBranchGap.exists_tendsto_ftTau_lt_second` is the upper half.
/-- info: 'ForgacsTran.lt_of_ftCritical_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lt_of_ftCritical_eval_eq_zero

/-- info: 'ForgacsTran.exists_bound_ftBranchZ_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_ftBranchZ_pow

/-- info: 'ForgacsTran.isBigO_ftBranchZ_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isBigO_ftBranchZ_pow

-- The crude member bound: `‖z‖ = O(d^rho)` turns into `‖t - x1‖ = O(d)` through
-- `norm_cluster_root`, by taking rho-th roots.  This is the gate on Case 2's
-- member leg, and it is why the exponent has to be exact.
/-- info: 'ForgacsTran.norm_sub_le_of_z_pow_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_sub_le_of_z_pow_bound

-- `CubicWitness` -- the terminals of its uncovered cone.
/-- info: 'ForgacsTran.continuousOn_cubicZ_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousOn_cubicZ_complex

/-- info: 'ForgacsTran.cubicQ_eval_zero_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicQ_eval_zero_ne

/-- info: 'ForgacsTran.cubicTau_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTau_neg

/-- info: 'ForgacsTran.cubicTau_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTau_strictAntiOn

/-- info: 'ForgacsTran.cubicZ_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicZ_zero

/-- info: 'ForgacsTran.existsUnique_cubicTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms existsUnique_cubicTau

/-- info: 'ForgacsTran.ftPrincipal_cubicTau_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_cubicTau_zero

/-- info: 'ForgacsTran.mem_cubicRootSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_cubicRootSet_iff


-- The member leg assembled per member: the z-free two-root identity gives an
-- exact rho-th root of unity, the principal expansion is rotated by it, and the
-- rotated direction is named -- so the member's index is produced, not assumed.
/-- info: 'ForgacsTran.exists_member_expansion_of_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_member_expansion_of_roots

/-- info: 'ForgacsTran.panelClearedRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelClearedRestrict

/-- info: 'ForgacsTran.exists_tendsto_ftTau_mem_first_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftTau_mem_first_gap

/-- info: 'ForgacsTran.lt_of_tendsto_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lt_of_tendsto_ftTau

-- The cluster index is unique once delta is small: two directions sit
-- `‖alpha_w - alpha_w'‖ * delta` apart while the error is `C * delta^2`.  This is
-- what makes a labelling well defined, and what the family step needs on top of.
/-- info: 'ForgacsTran.clusterAlpha_index_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterAlpha_index_unique

/-- info: 'ForgacsTran.panelBrat_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelBrat_coeff_zero

/-- info: 'ForgacsTran.clearedRestrict_panel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clearedRestrict_panel

/-- info: 'ForgacsTran.panelNbi_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelNbi_proper

/-- info: 'ForgacsTran.panelLaurent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelLaurent

-- The Rouche model for the cluster: `F(u) = c1 u^rho + c0`.  Its roots are simple
-- exactly when `c0 != 0`, which is the strengthening of the z-rate from
-- `‖z‖ = O(d^rho)` to `z/d^rho -> z0 != 0`.  A rho-fold root at the origin would
-- put every cluster direction at the same point.
/-- info: 'ForgacsTran.model_root_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_root_simple

/-- info: 'ForgacsTran.model_roots_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_roots_distinct

-- The Rouche perturbation, decomposed exactly: `D - M` is two increments, each
-- bounded by a lemma built for the lower-endpoint ratio and reused unchanged.
/-- info: 'ForgacsTran.norm_pencil_sub_model_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_pencil_sub_model_le

/-- info: 'ForgacsTran.exists_tendsto_ftBranchZ_div_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftBranchZ_div_pow

/-- info: 'ForgacsTran.swapVars_panelNbi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swapVars_panelNbi

/-- info: 'ForgacsTran.panelNbi_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelNbi_natDegree

/-- info: 'ForgacsTran.panelReductionCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelReductionCoeff

/-- info: 'ForgacsTran.tendsto_ftTau_nhdsLT_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftTau_nhdsLT_upper

/-- info: 'ForgacsTran.tendsto_pow_mul_ftBranchZ_nhdsLT_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_pow_mul_ftBranchZ_nhdsLT_upper

/-- info: 'ForgacsTran.tendsto_ftBranchZ_div_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftBranchZ_div_pow

-- The witness counts are unbounded -- `M/r - C` says nothing in `N` while `C >= M/r`,
-- so this is the statement that the clause-3 conclusion is non-trivial and not merely
-- non-empty (`prop:angular-discrepancy`, `eq:angular-distinct-lower`).
/-- info: 'ForgacsTran.witness_clauseThree_uniform_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_clauseThree_uniform_unbounded

/-- info: 'ForgacsTran.witness_clauseThree_ray_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_clauseThree_ray_unbounded


-- `thm:FT-geometry`/`thm:weighted-dominance` at the witness pencil.  The two
-- block statements are the load-bearing ones: each asserts a whole binder group
-- at ONE assignment, so each certifies that the hypothesis set is *inhabited*
-- rather than that its members are individually provable.  A `sorry` reaching
-- either would make a joint-satisfiability claim vacuous, which is worse than no
-- claim -- it reads as exactly the evidence it would fail to be.
/-- info: 'ForgacsTran.cubicWitness_retainedSet_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicWitness_retainedSet_block

/-- info: 'ForgacsTran.cubicWitness_upperRetainedSet_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicWitness_upperRetainedSet_block

/-- info: 'ForgacsTran.cubicTau_endpoint_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTau_endpoint_identity

-- `Forgacs2017RationalDenominator` Lemma 5, both halves: the negative zero at
-- `r = 1`, and every zero of their `R` real.
/-- info: 'ForgacsTran.card_roots_ftCriticalReal_ftRootPolyReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_roots_ftCriticalReal_ftRootPolyReal

/-- info: 'ForgacsTran.ft_local_strong_clock_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_local_strong_clock_composed

-- `Forgacs2017RationalDenominator` Prop. 3 Case 2 at the branch: the cluster's
-- members produced and expanded with no hypothesis about the branch, and the
-- same at one concrete pencil.  The witness is what makes the joint
-- satisfiability of the five composed windows a fact rather than a signature, so
-- a `sorry` reaching it would make that claim vacuous.
/-- info: 'ForgacsTran.cluster_normalized_expansion_at_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster_normalized_expansion_at_branch

/--
info: 'ForgacsTran.cluster_normalized_expansion_at_branch_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cluster_normalized_expansion_at_branch_nonvacuous

-- The model rate is a value for `z_0` rather than a restriction on the pencil.
/-- info: 'ForgacsTran.exists_model_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_model_rate

/-- info: 'ForgacsTran.tendsto_ftTau_div_nhdsLT_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftTau_div_nhdsLT_upper

/-- info: 'ForgacsTran.ft_local_strong_clock_on_FM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_local_strong_clock_on_FM

-- Cone sweep, third pass.  What the second pass left for their owners: the four
-- modules that were under active edit then, plus what Case 3 has since added.
-- Each guard is written from its own probe rather than copied -- two of these
-- names are long enough that `#print axioms` wraps the message across three
-- lines, and a copied single-line form fails.

-- `CubicWitness`: the witness pencil's closed-form radius and its two endpoint values.
/-- info: 'ForgacsTran.cubicTau_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTau_closed_form

/-- info: 'ForgacsTran.cubicTau_pi_div_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTau_pi_div_four

/-- info: 'ForgacsTran.cubicTau_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTau_pi_div_two

-- `FTBranchLemma5`: the degrees of the real critical and root polynomials.
/-- info: 'ForgacsTran.natDegree_ftCriticalReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_ftCriticalReal

/-- info: 'ForgacsTran.natDegree_ftRootPolyReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_ftRootPolyReal

-- `FTBranchUpper`: the upper endpoint's three limits, including the complex endpoint form.
/-- info: 'ForgacsTran.tendsto_arctan_div_nhdsNE_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_arctan_div_nhdsNE_zero

/--
info: 'ForgacsTran.tendsto_ftArcPoint_pow_mul_ftBranchZ_nhdsLT_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms tendsto_ftArcPoint_pow_mul_ftBranchZ_nhdsLT_upper

/-- info: 'ForgacsTran.tendsto_ftArccot_mul_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftArccot_mul_atTop

-- `FTBranchZRate`: the elementary limit the rescaled `z` rate is built on.
/-- info: 'ForgacsTran.tendsto_sin_div_nhdsGT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_sin_div_nhdsGT_zero

-- `FTMinModulus`: the magnitude comparison, the `z`-free relations, Case 3's Rouche step and the
-- two second-order estimates it needs.
/-- info: 'ForgacsTran.continuousOn_ftBranchZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousOn_ftBranchZ

/-- info: 'ForgacsTran.exists_ftDen_root_near_origin_model_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftDen_root_near_origin_model_root

/-- info: 'ForgacsTran.exists_second_order_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_second_order_bound

/-- info: 'ForgacsTran.exists_upper_ratio_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_ratio_bound

/-- info: 'ForgacsTran.exists_upper_ratio_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_ratio_close

/--
info: 'ForgacsTran.ftCritical_eval_eq_zero_of_two_le_rootMultiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ftCritical_eval_eq_zero_of_two_le_rootMultiplicity

/-- info: 'ForgacsTran.ftCritical_eval_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCritical_eval_neg

/-- info: 'ForgacsTran.negDivPow_lt_of_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negDivPow_lt_of_mem_Ioo

/-- info: 'ForgacsTran.norm_eval_posRootPoly_le_of_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_posRootPoly_le_of_norm_eq

/-- info: 'ForgacsTran.norm_eval_posRootPoly_lt_of_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_posRootPoly_lt_of_norm_eq

/-- info: 'ForgacsTran.norm_one_add_pow_sub_linear_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_one_add_pow_sub_linear_le

/-- info: 'ForgacsTran.norm_sub_le_of_prod_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_sub_le_of_prod_le

/-- info: 'ForgacsTran.prod_norm_sub_le_of_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_norm_sub_le_of_norm_le

/-- info: 'ForgacsTran.second_deriv_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms second_deriv_relation

/-- info: 'ForgacsTran.tendsto_ftBranchZ_atTop_of_tendsto_ftTau_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftBranchZ_atTop_of_tendsto_ftTau_zero

/-- info: 'ForgacsTran.tendsto_ftBranchZ_upper_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftBranchZ_upper_pi

/-- info: 'ForgacsTran.cubicWitness_interior_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicWitness_interior_geometry

/-- info: 'ForgacsTran.cubicWitness_nonprincipalCluster_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicWitness_nonprincipalCluster_block

/-- info: 'ForgacsTran.cubicRootSet_erase_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicRootSet_erase_pair

/-- info: 'ForgacsTran.cubicThird_ne_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicThird_ne_principal

-- `Amplitude`: the `HasRealCoeffs` closure lemmas.  Dotted names, which is why
-- they were outside every cone without appearing in the census -- the coverage
-- report could not see them to count them.
/-- info: 'ForgacsTran.HasRealCoeffs.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.add

/-- info: 'ForgacsTran.HasRealCoeffs.derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.derivative

/-- info: 'ForgacsTran.HasRealCoeffs.eval_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.eval_conj

/-- info: 'ForgacsTran.HasRealCoeffs.ftDen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.ftDen

/-- info: 'ForgacsTran.exists_bound_ftTau_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_ftTau_upper

/-- info: 'ForgacsTran.hasDerivAt_cubicClusterRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_cubicClusterRatio

/-- info: 'ForgacsTran.hasDerivAt_cubicClusterRatioDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_cubicClusterRatioDeriv

/-- info: 'ForgacsTran.abs_cubicClusterRatioDeriv2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_cubicClusterRatioDeriv2_le

/-- info: 'ForgacsTran.cubicCluster_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicCluster_taylor

/-- info: 'ForgacsTran.cubicClusterRatio_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicClusterRatio_zero

/-- info: 'ForgacsTran.cubicClusterRatioDeriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicClusterRatioDeriv_zero

/-- info: 'ForgacsTran.clusterOmega_three_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_three_two

/-- info: 'ForgacsTran.cubicCluster_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicCluster_coeff

/-- info: 'ForgacsTran.cubicThird_div_cubicTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicThird_div_cubicTau

/-- info: 'ForgacsTran.cubicCluster_hexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicCluster_hexp

/-- info: 'ForgacsTran.cubicWitness_cluster_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicWitness_cluster_block

/-- info: 'ForgacsTran.upperCluster_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperCluster_taylor

/-- info: 'ForgacsTran.upperCluster_hexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperCluster_hexp

/-- info: 'ForgacsTran.upperWitness_expansion_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperWitness_expansion_block

/-- info: 'ForgacsTran.abs_upperClusterRatioDeriv2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_upperClusterRatioDeriv2_le

/-- info: 'ForgacsTran.upperClusterRatioDeriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperClusterRatioDeriv_zero

/-- info: 'ForgacsTran.card_upperRootSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_upperRootSet

/-- info: 'ForgacsTran.upperRootSet_erase_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperRootSet_erase_pair

/-- info: 'ForgacsTran.norm_upperNonprincipal_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_upperNonprincipal_div

/-- info: 'ForgacsTran.upperWitness_cluster_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperWitness_cluster_block

/-- info: 'ForgacsTran.upperDen_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperDen_eval

/-- info: 'ForgacsTran.upperDen_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperDen_eval_eq_zero_iff

/-- info: 'ForgacsTran.upperDen_deriv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperDen_deriv_ne_zero

/-- info: 'ForgacsTran.norm_lt_four_of_mem_upperRootSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_lt_four_of_mem_upperRootSet

-- `CubicWitnessInterior`: `hinterior` at the witness pencil, the forcing statement
-- that pins every admissible window family, and the check that the deleted set
-- leaves the arc non-empty.
/-- info: 'ForgacsTran.cubicTheta_forced_of_hinterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTheta_forced_of_hinterior

/-- info: 'ForgacsTran.cubicTheta_leaves_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTheta_leaves_room

/-- info: 'ForgacsTran.hasRealCoeffs_witB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasRealCoeffs_witB

/-- info: 'ForgacsTran.clusterOmega_three_two_ne_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_three_two_ne_principal

/-- info: 'ForgacsTran.clusterOmega_three_two_ne_principal_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_three_two_ne_principal_conj

/-- info: 'ForgacsTran.upperDen_eval_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperDen_eval_principal

/-- info: 'ForgacsTran.upperPrincipal_ne_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperPrincipal_ne_conj

/-- info: 'ForgacsTran.jointEta_sq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointEta_sq_add

/-- info: 'ForgacsTran.sum_cubes_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_cubes_factor

/-- info: 'ForgacsTran.jointDen_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointDen_eval

/-- info: 'ForgacsTran.jointDen_eval_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointDen_eval_eq_zero_iff

/-- info: 'ForgacsTran.card_jointRootSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_jointRootSet

/-- info: 'ForgacsTran.jointRootSet_erase_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointRootSet_erase_pair

/-- info: 'ForgacsTran.jointTau_lt_norm_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointTau_lt_norm_third

/-- info: 'ForgacsTran.jointRatio_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointRatio_reflect

/-- info: 'ForgacsTran.jointThird_div_jointTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointThird_div_jointTau

/-- info: 'ForgacsTran.jointCluster_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointCluster_taylor

/-- info: 'ForgacsTran.jointCluster_hexp_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointCluster_hexp_lower

/-- info: 'ForgacsTran.jointCluster_hexp_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointCluster_hexp_upper

/-- info: 'ForgacsTran.jointWitness_both_clusters_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointWitness_both_clusters_block

/-- info: 'ForgacsTran.upperQ_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upperQ_eval_zero

/-- info: 'ForgacsTran.jointQ_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointQ_eval_zero

/-- info: 'ForgacsTran.jointZ_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointZ_pos

/-- info: 'ForgacsTran.jointDen_deriv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointDen_deriv_ne_zero

/-- info: 'ForgacsTran.norm_lt_two_of_mem_jointRootSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_lt_two_of_mem_jointRootSet

/-- info: 'ForgacsTran.jointPrincipal_ne_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointPrincipal_ne_conj

-- `CubicWitnessComposition`: `thm:weighted-dominance` at the cubic pencil with
-- every binder discharged, and the two endpoint derivatives it is built on.
/-- info: 'ForgacsTran.cubic_weighted_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_weighted_dominance

/-- info: 'ForgacsTran.hasDerivWithinAt_cubicTau_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivWithinAt_cubicTau_zero

/-- info: 'ForgacsTran.hasDerivWithinAt_cubicTauUpper_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivWithinAt_cubicTauUpper_zero

/-- info: 'ForgacsTran.tendsto_one_sub_cubicThird_div_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_one_sub_cubicThird_div_complex

/-- info: 'ForgacsTran.jointTau_upper_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointTau_upper_endpoint

/-- info: 'ForgacsTran.ftPrincipal_jointTau_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_jointTau_upper

/-- info: 'ForgacsTran.no_upper_endpoint_datum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_upper_endpoint_datum

/-- info: 'ForgacsTran.jointTau_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointTau_zero

/-- info: 'ForgacsTran.ftPrincipal_jointTau_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_jointTau_zero

/-- info: 'ForgacsTran.jointZ_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointZ_zero

/-- info: 'ForgacsTran.one_le_rootMultiplicity_jointDen_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_le_rootMultiplicity_jointDen_zero

/-- info: 'ForgacsTran.eventually_jointDen_eval_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_jointDen_eval_principal

/-- info: 'ForgacsTran.exp_pi_div_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_pi_div_three

/-- info: 'ForgacsTran.jointEta_mul_principal_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointEta_mul_principal_dir

/-- info: 'ForgacsTran.norm_jointEta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_jointEta

/-- info: 'ForgacsTran.not_upper_endpoint_datum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_upper_endpoint_datum_ne_zero

/-- info: 'ForgacsTran.jointCritical_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointCritical_eval

/-- info: 'ForgacsTran.jointAmp_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointAmp_eval

/-- info: 'ForgacsTran.jointAmp_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointAmp_ratio

/-- info: 'ForgacsTran.tendsto_jointRatio_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_jointRatio_upper

/-- info: 'ForgacsTran.jointEta_eq_neg_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointEta_eq_neg_exp

/-- info: 'ForgacsTran.tendsto_joint_normalized_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_joint_normalized_quotient

/-- info: 'ForgacsTran.jointThird_upper_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointThird_upper_endpoint

/-- info: 'ForgacsTran.tendsto_jointTau_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_jointTau_upper

/-- info: 'ForgacsTran.tendsto_jointThird_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_jointThird_upper

/-- info: 'ForgacsTran.tendsto_jointPrincipal_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_jointPrincipal_upper

/-- info: 'ForgacsTran.tendsto_jointB_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_jointB_ratio

/-- info: 'ForgacsTran.tendsto_joint_one_sub_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_joint_one_sub_ratio

/-- info: 'ForgacsTran.jointRho_upper_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointRho_upper_eq

/-- info: 'ForgacsTran.jointZ_upper_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointZ_upper_unbounded

/-- info: 'ForgacsTran.no_upper_z_continuity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_upper_z_continuity

/-- info: 'ForgacsTran.jointTau_upper_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointTau_upper_eq

/-- info: 'ForgacsTran.jointTau_upper_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointTau_upper_le

/-- info: 'ForgacsTran.norm_lt_half_of_mem_jointRootSet_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_lt_half_of_mem_jointRootSet_upper

/-- info: 'ForgacsTran.jointDen_ne_zero_on_sphere_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointDen_ne_zero_on_sphere_upper

/-- info: 'ForgacsTran.sin_upper_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_upper_ge

/-- info: 'ForgacsTran.jointZ_upper_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointZ_upper_ge

/-- info: 'ForgacsTran.norm_jointDen_sphere_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_jointDen_sphere_ge

/-- info: 'ForgacsTran.exists_jointCbd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_jointCbd

/-- info: 'ForgacsTran.mul_sinc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_sinc

/-- info: 'ForgacsTran.continuousWithinAt_jointT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousWithinAt_jointT

/-- info: 'ForgacsTran.jointT_zero_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointT_zero_ne

/-- info: 'ForgacsTran.jointPrincipal_upper_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jointPrincipal_upper_eq

/-- info: 'ForgacsTran.eventually_jointDen_upper_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_jointDen_upper_root

/-- info: 'ForgacsTran.exists_jointAmp_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_jointAmp_floor

/-- info: 'ForgacsTran.joint_hn₁r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms joint_hn₁r

-- `CubicPhaseSign`: the descent that lets `ClauseThree`'s real-polynomial
-- statement reach this development's complex coefficient polynomial.  The whole
-- module is guarded rather than only its two results: the closure lemmas are
-- consumed through dot notation, which the cone scanner cannot see, so it lists
-- them as terminals and over-guarding is the safe direction.

/-- info: 'ForgacsTran.hasRealCoeffs_iff_mem_lifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasRealCoeffs_iff_mem_lifts

/-- info: 'ForgacsTran.HasRealCoeffs.exists_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.exists_real

/-- info: 'ForgacsTran.HasRealCoeffs.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.mul

/-- info: 'ForgacsTran.HasRealCoeffs.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.sub

/-- info: 'ForgacsTran.HasRealCoeffs.coeff_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.coeff_ofReal

/-- info: 'ForgacsTran.HasRealCoeffs.C_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.C_coeff

/-- info: 'ForgacsTran.HasRealCoeffs.C_inv_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasRealCoeffs.C_inv_coeff

/-- info: 'ForgacsTran.hasRealCoeffs_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasRealCoeffs_zero

/-- info: 'ForgacsTran.hasRealCoeffs_ftCoeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasRealCoeffs_ftCoeffPoly

/-! ### Case 3's four links, guarded after the lane that built them stopped

The chain from the `z`-free relation to `ζ_j = ν(1 + cδ) + O(δ²)`.  Guarded here
rather than left to the composition, because the instantiation that would consume
them is the one piece of Case 3 still outstanding -- so nothing else pins them. -/

/-- info: 'ForgacsTran.exists_ratio_second_order_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ratio_second_order_bound

/-- info: 'ForgacsTran.norm_nat_mul_sub_le_of_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_nat_mul_sub_le_of_pow_eq

/-- info: 'ForgacsTran.norm_sub_beta_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_sub_beta_mul_le

/-- info: 'ForgacsTran.norm_upper_member_expansion_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_upper_member_expansion_le

-- The real polynomial `ClauseThree`'s statements quantify over, produced in
-- general rather than by hand at one pencil.
/-- info: 'ForgacsTran.exists_real_ftCoeffPoly_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_real_ftCoeffPoly_of_real

/-- info: 'ForgacsTran.exists_real_ftCoeffPoly_family_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_real_ftCoeffPoly_family_of_real

-- `hsign` discharged at the cubic pencil rather than assumed.
/-- info: 'ForgacsTran.cubic_hsign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_hsign

-- `hz` at the witness: `z` is a function of the branch modulus alone, and
-- strictly monotone along the arc because both halves are.
/-- info: 'ForgacsTran.cubicZ_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicZ_strictMonoOn

-- The pencil's degree over `ℂ`, which is what discharges `ft_geometry`'s
-- exclusion of `(deg Q, r) = (2,1)` at the constructed branch.
/-- info: 'ForgacsTran.natDegree_ftRootPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_ftRootPoly

-- Four of `ft_geometry`'s seven analytic binders, produced from the admissible
-- class rather than assumed.
/-- info: 'ForgacsTran.ft_branch_supplies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_branch_supplies

-- `thm:FT-geometry` at the constructed branch: five binders discharged, and the
-- two that remain -- the upper-endpoint limit and the minimum-modulus gap --
-- stated about `ftTau`/`ftBranchZ` themselves.
/-- info: 'ForgacsTran.ft_geometry_at_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch

/-- info: 'ForgacsTran.ft_geometry_at_branch_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_unbounded

-- Why the quantization bounds of `eq:local-phase-quantization` are pointwise:
-- imposed on the whole window, the second one is met by nothing.
/-- info: 'ForgacsTran.not_forall_phase_near_second_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_forall_phase_near_second_point

-- `cor:linear-phase-variation`'s constants, produced from the arc's regularity
-- rather than assumed: the variation of an argument branch, the existence of the
-- constant, and `linear_phase_variation_regular`'s `hKvar` in its own shape.
/-- info: 'ForgacsTran.eVariationOn_polarAngle_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eVariationOn_polarAngle_le

/-- info: 'ForgacsTran.exists_eVariationOn_polarAngle_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_eVariationOn_polarAngle_le

/-- info: 'ForgacsTran.exists_tangent_angle_variation_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tangent_angle_variation_bound

-- The upper endpoint of the viewing arc, in both conventions of `eq:ab-def`:
-- the radius limit at `r = 1`, the uniform bound that makes it reachable, and
-- the two spectral-parameter limits `ft_geometry` asks for.
/-- info: 'ForgacsTran.ftTau_le_two_mul_of_lt_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTau_le_two_mul_of_lt_pi

/-- info: 'ForgacsTran.exists_tendsto_ftTau_nhdsLT_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftTau_nhdsLT_pi

/-- info: 'ForgacsTran.tendsto_ftBranchZ_atTop_arc_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftBranchZ_atTop_arc_end

/-- info: 'ForgacsTran.exists_tendsto_ftBranchZ_arc_end_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftBranchZ_arc_end_pi

-- `thm:FT-geometry` at the constructed branch with one analytic binder left,
-- in each convention.
/-- info: 'ForgacsTran.ft_geometry_at_branch_unbounded_of_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_unbounded_of_two_le

/-- info: 'ForgacsTran.ft_geometry_at_branch_of_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_of_three_le

-- The angle extraction: an arbitrary zero of the pencil is a branch point at some index,
-- which is what turns `Forgacs2017RationalDenominator` Prop. 1 into a statement about a
-- hypothetical zero.
/-- info: 'ForgacsTran.exists_ftAngleSum_index_of_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftAngleSum_index_of_root

-- Index monotonicity of the branch radius, which supplies the upper squeeze.
/-- info: 'ForgacsTran.ftTau_principal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTau_principal_le

-- The index condition is FALSE above `n = 2r`, so a statement carrying it over the whole
-- arc is vacuous there rather than merely unproved.
/-- info: 'ForgacsTran.not_arc_wide_of_two_mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_arc_wide_of_two_mul_lt

-- The same condition holds at and below `n = 2r`, which is what makes the bound sharp.
/-- info: 'ForgacsTran.ftBranchAt_arc_of_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchAt_arc_of_le_two_mul

-- `hmin` reduced to the argument condition `hcone`.
/-- info: 'ForgacsTran.ft_minModulus_at_branch_of_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_of_le_two_mul

-- `thm:FT-geometry` at the constructed branch with `hcone` the only analytic binder,
-- in the unbounded convention of `eq:ab-def`.
/-- info: 'ForgacsTran.ft_geometry_unbounded_at_branch_of_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_unbounded_at_branch_of_cone

-- `cor:panel-B-attractor`'s rate, read off `prop:isolated-dominant-cancellation`
-- rather than restated: the proposition applied at the panel, the geometric rate
-- in the `F_M` variable, and its conjugate half.
/-- info: 'ForgacsTran.panelB_isolated_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelB_isolated_cancellation

/-- info: 'ForgacsTran.panel_attractor_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panel_attractor_rate

/-- info: 'ForgacsTran.panel_attractor_rate_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panel_attractor_rate_conj

-- The orientation lemma: `F_M` is the `M`-th Taylor coefficient of the panel's
-- generating function at the origin.
/-- info: 'ForgacsTran.taylorCoeff_panel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_panel

-- The upper-endpoint radius limits are witnessed, so neither is vacuous.
/-- info: 'ForgacsTran.exists_tendsto_ftTau_nhdsLT_pi_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftTau_nhdsLT_pi_witness

/-- info: 'ForgacsTran.tendsto_ftTau_nhdsLT_arc_end_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftTau_nhdsLT_arc_end_witness

-- `ft_geometry_at_branch` with the minimum-modulus gap reduced to the argument
-- condition, in each convention of `eq:ab-def`.
/-- info: 'ForgacsTran.ft_geometry_at_branch_of_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_of_cone

/-- info: 'ForgacsTran.ft_geometry_at_branch_unbounded_of_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_unbounded_of_cone

-- `thm:FT-geometry` at the constructed branch in the FINITE upper-endpoint
-- convention of `eq:ab-def`, which is the one the tree's own witnesses use.
/-- info: 'ForgacsTran.ft_geometry_at_branch_of_cone_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_of_cone_pi

-- The principal-index squeeze, which is what removes the index condition rather
-- than weakening it.
/-- info: 'ForgacsTran.ftProp1_closing_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftProp1_closing_principal

/-- info: 'ForgacsTran.ft_minModulus_at_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch

-- The explicit coefficient recursion IS the solution of the defining
-- convolution -- the evaluable counterpart of `exists_denomConv_eq`, and general
-- in `Q`, `B` and `r` rather than special to the panel.
/-- info: 'ForgacsTran.denomConv_ftCoeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denomConv_ftCoeffPoly

-- `eq:reduction-coeff` with the panel's sequence named, and `cor:panel-B-attractor`
-- in the manuscript's own variable, both zeros of the conjugate pair.
/-- info: 'ForgacsTran.panelPC_eq_ftCoeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelPC_eq_ftCoeffPoly

/-- info: 'ForgacsTran.panelP_attractor_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelP_attractor_rate

/-- info: 'ForgacsTran.panelP_attractor_rate_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panelP_attractor_rate_conj

-- `eq:phase-derivative-bound` at the cubic pencil, in closed form: the phase
-- derivative is rational in the branch radius alone, so the bound is a constant
-- rather than a function of the subarc.
/-- info: 'ForgacsTran.im_cubicAmpLogDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms im_cubicAmpLogDeriv

/-- info: 'ForgacsTran.abs_im_cubicAmpLogDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_im_cubicAmpLogDeriv_le

-- `exists_phaseZeros`'s continuity and strict-monotonicity binders, discharged.
/-- info: 'ForgacsTran.cubic_phase_binders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_phase_binders

-- All five binders of `exists_phaseZeros` supplied at one pencil: the first
-- unconditional instance of the phase count in this tree.
/-- info: 'ForgacsTran.cubic_exists_phaseZeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_exists_phaseZeros

-- The argument condition `hcone`, and the pieces of it that are closed.
/-- info: 'ForgacsTran.negDivPow_ftTau_lt_ftBranchZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negDivPow_ftTau_lt_ftBranchZ

/-- info: 'ForgacsTran.negDivPow_lt_ftBranchZ_of_ftCritical_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negDivPow_lt_ftBranchZ_of_ftCritical_neg

-- The negative axis at even `r`, unconditionally and on the whole axis.
/-- info: 'ForgacsTran.no_neg_real_root_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_neg_real_root_of_even

-- At `r = 1`, `hcone` IS the absence of a real zero in the closed disk.
/-- info: 'ForgacsTran.cone_of_no_real_root_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cone_of_no_real_root_pi

-- The branch radius stays below the first positive critical point, reduced to one
-- nonvanishing statement.
/-- info: 'ForgacsTran.ftCritical_neg_below_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCritical_neg_below_ftTau

-- `Reduction`'s denominator coefficient and `AttractorPole`'s are the same
-- definition, which is why the two modules can be composed at all.
/-- info: 'ForgacsTran.ftDenCoeff_eq_ftDenom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftDenCoeff_eq_ftDenom

-- The retained range at the cubic pencil, as a membership test.
/-- info: 'ForgacsTran.mem_cubicRetained_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_cubicRetained_iff

-- The interior decomposition's error as a FUNCTION rather than a pointwise
-- existential -- determined, not chosen, so no choice principle is involved.
/-- info: 'ForgacsTran.exists_interior_cos_error_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interior_cos_error_function

-- Simplicity at the named point, which uniqueness-as-a-point does not give: a
-- double zero satisfies the `iff` clause too.
/-- info: 'ForgacsTran.rootMultiplicity_eq_one_of_factoredOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootMultiplicity_eq_one_of_factoredOn

-- The reflection, which Mathlib does not give for root multiplicity directly.
/-- info: 'ForgacsTran.map_conj_ftCoeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_conj_ftCoeffPoly

/-- info: 'ForgacsTran.rootMultiplicity_conj_ftCoeffPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootMultiplicity_conj_ftCoeffPoly

-- `prop:equidistribution`'s inner count, produced at the cubic pencil rather
-- than assumed.
/-- info: 'ForgacsTran.count_filter_lower_of_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms count_filter_lower_of_zeros

/-- info: 'ForgacsTran.count_filter_lower_of_subarc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms count_filter_lower_of_subarc

/-- info: 'ForgacsTran.cubic_count_filter_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_count_filter_lower

-- The critical polynomial factors as `-Sigma * Q` over the reals, with `Sigma`
-- increasing on each gap, so it has at most one zero per gap.  The monotonicity
-- is algebraic rather than a derivative sign.
/-- info: 'ForgacsTran.eval_ftCriticalReal_eq_neg_sigma_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ftCriticalReal_eq_neg_sigma_mul

/-- info: 'ForgacsTran.ftCritical_ne_zero_below_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCritical_ne_zero_below_ftTau

-- Their Lemma 5 on the negative axis, with the finite upper endpoint supplying
-- the floor the branch value stays under.
/-- info: 'ForgacsTran.negDivPow_neg_ne_ftBranchZ_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negDivPow_neg_ne_ftBranchZ_one

-- `hcone` discharged at `r = 1` with a simple smallest zero.
/-- info: 'ForgacsTran.cone_at_branch_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cone_at_branch_one

-- `Forgacs2017RationalDenominator` Props. 1--2 for the constructed branch, with
-- no analytic hypothesis.
/-- info: 'ForgacsTran.ft_minModulus_at_branch_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_one

-- `thm:FT-geometry` at the constructed branch, every binder supplied from the
-- admissible class: no `hbranch`, no `hmin`, no `hzb`, no `hcone`.
/-- info: 'ForgacsTran.ft_geometry_at_branch_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_pi

-- The coefficient sequence at the cubic pencil is honest: degree exactly `M`, so
-- a count against it is a count against a growing degree.
/-- info: 'ForgacsTran.natDegree_ftCoeffPoly_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_ftCoeffPoly_cubic

-- Interior zeros at the cubic pencil, unconditionally: a fixed positive fraction
-- of the degree, with no analytic hypothesis.
/-- info: 'ForgacsTran.cubic_interior_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_interior_zero_count

-- `thm:main` at the cubic pencil, reduced to one statement: the deleted windows
-- shrinking with `M`.
/-- info: 'ForgacsTran.cubic_main_bound_of_shrinkingWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_main_bound_of_shrinkingWindow

/-- info: 'ForgacsTran.cubic_ftInputs_of_shrinkingWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_ftInputs_of_shrinkingWindow

-- The interior supply with no deleted family in it, which is what makes the
-- window separable from the geometry for the first time.
/-- info: 'ForgacsTran.interior_data_of_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_data_of_geometry

-- Pencil-independent: `eq:dominance-bound` off any FIXED window upgrades to
-- windows of half-width `h/M`, given the interior data at one fixed radius.
/-- info: 'ForgacsTran.dominance_shrinking_of_fixed_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dominance_shrinking_of_fixed_window

/-- info: 'ForgacsTran.cubic_shrinkingWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_shrinkingWindow

-- `thm:main` at the cubic pencil, with no hypothesis: the first pencil with a
-- genuine amplitude divisor to reach it.
/-- info: 'ForgacsTran.cubic_bulk_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_bulk_count

/-- info: 'ForgacsTran.cubic_main_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_main_bound

/-- info: 'ForgacsTran.cubic_main_bound_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_main_bound_interval

-- The minimum-modulus assertion with no restriction on the multiplicity of the
-- smallest zero: the two cases are exhaustive, so the union carries neither
-- branch's extra binder.
/-- info: 'ForgacsTran.negDivPow_lt_ftBranchZ_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negDivPow_lt_ftBranchZ_pos

/-- info: 'ForgacsTran.ft_minModulus_at_branch_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_pi

-- The coverage witness: the simple-zero form's hypothesis is UNSATISFIABLE at
-- the cubic pencil, so the general form strictly reaches where it could not.
/-- info: 'ForgacsTran.cubic_min_not_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_min_not_simple

/-- info: 'ForgacsTran.ft_minModulus_at_branch_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_cubic

-- Why the cluster binders must be conditioned rather than relaxed: at rho = 1
-- the cluster direction is the division convention's zero, so
-- `clusterAlpha_ne_zero` is FALSE there rather than unproven.
/-- info: 'ForgacsTran.clusterAlpha_one_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterAlpha_one_eq_zero

/-- info: 'ForgacsTran.not_clusterAlpha_ne_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_clusterAlpha_ne_zero_one

-- And the endpoint exponent is wrong there too: `rho - 1` equals
-- `lem:amplitude-divisor`'s `k - 1` exactly when `2 <= rho`.
/-- info: 'ForgacsTran.hEp_false_of_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hEp_false_of_rho_one

-- `thm:weighted-dominance` with no multiplicity restriction: the cluster
-- hypotheses are conditioned on the cluster being inhabited.
/-- info: 'ForgacsTran.weighted_dominance_of_branch_any_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_of_branch_any_multiplicity

-- Both window counts at one `M`-free constant, off the shrinking window.
/-- info: 'ForgacsTran.cubic_window_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_window_counts

-- `prop:equidistribution` with both binders discharged: an unconditional
-- instance at the cubic pencil.
/-- info: 'ForgacsTran.cubic_equidistribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_equidistribution

-- `eq:angular-discrepancy` two-sided, off the same counts.
/-- info: 'ForgacsTran.cubic_angular_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_angular_discrepancy

/-- info: 'ForgacsTran.count_filter_lower_of_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms count_filter_lower_of_two

/-- info: 'ForgacsTran.mem_ftWindow_of_subarc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_ftWindow_of_subarc

-- A simple smallest zero, with the numerator vanishing ON the branch, so the
-- witness tests `lem:amplitude-divisor` rather than sidestepping it.
/-- info: 'ForgacsTran.witQ_smallest_zero_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witQ_smallest_zero_simple

/-- info: 'ForgacsTran.ftAmp_favB_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmp_favB_eq_zero_iff

-- The first deleted family in this tree that actually shrinks with `M`.
/-- info: 'ForgacsTran.favTheta_shrinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms favTheta_shrinks

/-- info: 'ForgacsTran.favWitness_hinterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms favWitness_hinterior

-- `thm:weighted-dominance` at a SIMPLE smallest zero, with no hypothesis: the
-- other multiplicity regime, and the conditioned binders discharged vacuously
-- because there is no cluster for them to be about.
/-- info: 'ForgacsTran.fav_weighted_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fav_weighted_dominance

/-- info: 'ForgacsTran.favRoots_erase_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms favRoots_erase_card

/-- info: 'ForgacsTran.favCbd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms favCbd

-- The `FTInputs` bundle built at the cubic pencil rather than posited.
/-- info: 'ForgacsTran.cubic_ftInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_ftInputs

-- The witness pencil's arithmetic: both endpoints are exact squares, so the
-- collision has multiplicity two at a turning point rather than at a zero of `Q`.
/-- info: 'ForgacsTran.ftDen_witQ_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftDen_witQ_lower_sq

/-- info: 'ForgacsTran.ftDen_witQ_upper_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftDen_witQ_upper_sq

/-- info: 'ForgacsTran.witQ_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witQ_factor

/-- info: 'ForgacsTran.witQ_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witQ_eval_one

/-- info: 'ForgacsTran.witQ_eval_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witQ_eval_neg_one

/-- info: 'ForgacsTran.favRoots_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms favRoots_ne_zero

/-- info: 'ForgacsTran.eval_ftCritical_ftRootPoly_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ftCritical_ftRootPoly_ne_zero

/-- info: 'ForgacsTran.eval_derivative_ftDen_ftRootPoly_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_ftDen_ftRootPoly_ne_zero

/-- info: 'ForgacsTran.eval_derivative_ftDen_fiber_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_ftDen_fiber_ne_zero

/-- info: 'ForgacsTran.ft_principal_simple_at_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_principal_simple_at_branch

/-- info: 'ForgacsTran.cone_at_branch_of_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cone_at_branch_of_two_le

/-- info: 'ForgacsTran.ft_minModulus_at_branch_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_two_le

/-- info: 'ForgacsTran.ft_geometry_unbounded_at_branch_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_unbounded_at_branch_two_le

/-- info: 'ForgacsTran.cubic_window_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_window_zeros

/-- info: 'ForgacsTran.cubic_angular_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_angular_clock

/-- info: 'ForgacsTran.cubic_local_strong_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_local_strong_clock

/-- info: 'ForgacsTran.interior_distinct_count_ofSignAlternation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_distinct_count_ofSignAlternation

/-- info: 'ForgacsTran.hasDerivAt_cubicAmpDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_cubicAmpDeriv

/-- info: 'ForgacsTran.cubicPhaseCurvature_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicPhaseCurvature_eq

/-- info: 'ForgacsTran.not_ftBranchAt_one_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_ftBranchAt_one_one

/-- info: 'ForgacsTran.map_norm_sub_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_norm_sub_prod

/-- info: 'ForgacsTran.ftArcPoint_simple_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftArcPoint_simple_uniform

/-- info: 'ForgacsTran.ftPrincipal_simple_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_simple_uniform



/-- info: 'ForgacsTran.linear_phase_variation_components_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linear_phase_variation_components_regular

/-- info: 'ForgacsTran.exp_logLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_logLift

/-- info: 'ForgacsTran.hasDerivAt_logLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_logLift

/-- info: 'ForgacsTran.viewing_angle_bound_on_arc_le_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms viewing_angle_bound_on_arc_le_pi

/-- info: 'ForgacsTran.weighted_dominance_ftCoeffPoly_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_ftCoeffPoly_at

/-- info: 'ForgacsTran.cubic_interior_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_interior_remainder

/-- info: 'ForgacsTran.cubic_interior_cos_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_interior_cos_error

/-- info: 'ForgacsTran.cubic_local_strong_clock_of_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_local_strong_clock_of_C1

/-- info: 'ForgacsTran.ftDen_cubicQ_eval_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftDen_cubicQ_eval_factor

/-- info: 'ForgacsTran.cubic_denominator_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_denominator_lower

/-- info: 'ForgacsTran.cubicTau_eq_ftTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicTau_eq_ftTau

/-- info: 'ForgacsTran.ftAngle_one_cubicTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAngle_one_cubicTau

/-- info: 'ForgacsTran.ftRootPoly_one_eq_cubicQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRootPoly_one_eq_cubicQ

/-- info: 'ForgacsTran.cubicGammaDeriv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicGammaDeriv_ne_zero

/-- info: 'ForgacsTran.cubic_branch_C2_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_branch_C2_regular

/-- info: 'ForgacsTran.interior_remainder_eq_contour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_remainder_eq_contour

/-- info: 'ForgacsTran.interior_remainder_re_eq_contour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_remainder_re_eq_contour

/-- info: 'ForgacsTran.norm_smul_ftContourRem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_smul_ftContourRem_le

/-- info: 'ForgacsTran.ftRemainder_eq_contour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRemainder_eq_contour

/-- info: 'ForgacsTran.ftCoeff_re_sub_principal_eq_contour_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftCoeff_re_sub_principal_eq_contour_re

/-- info: 'ForgacsTran.weighted_dominance_of_branch_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_of_branch_at

/-- info: 'ForgacsTran.ft_interior_data_at_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_interior_data_at_branch

/-- info: 'ForgacsTran.ft_interior_data_at_branch_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_interior_data_at_branch_nonvacuous

/-- info: 'ForgacsTran.ftAmplitudeDivisor_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmplitudeDivisor_count

/-- info: 'ForgacsTran.ftPrincipal_ne_conj_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_ne_conj_of_pos

/-- info: 'ForgacsTran.hint_of_interior_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hint_of_interior_data



/-- info: 'ForgacsTran.ftPrincipalAmp_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipalAmp_congr

/-- info: 'ForgacsTran.ftRemainder_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftRemainder_congr

/-- info: 'ForgacsTran.ft_geometry_at_branch_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_quadratic

/-- info: 'ForgacsTran.ft_geometry_unbounded_at_branch_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_unbounded_at_branch_one

/-- info: 'ForgacsTran.ft_minModulus_at_branch_of_deg_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_of_deg_le_two

/-- info: 'ForgacsTran.cone_at_branch_one_of_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cone_at_branch_one_of_three_le

/-- info: 'ForgacsTran.ft_minModulus_at_branch_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_linear

/-- info: 'ForgacsTran.sin_scaled_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_scaled_le

/-- info: 'ForgacsTran.eq_or_eq_of_natDegree_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_or_eq_of_natDegree_le_two

/-- info: 'ForgacsTran.ft_minModulus_at_branch_of_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_of_or

/-- info: 'ForgacsTran.tendsto_ftTau_nhdsLT_upper_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftTau_nhdsLT_upper_of_pos

/-- info: 'ForgacsTran.tendsto_ftBranchZ_atTop_arc_end_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftBranchZ_atTop_arc_end_of_pos

/-- info: 'ForgacsTran.ftPrincipal_ne_arcPoint_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_ne_arcPoint_of_pos

/-- info: 'ForgacsTran.ft_geometry_at_branch_of_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_geometry_at_branch_of_two_le

/-- info: 'ForgacsTran.exists_local_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_local_separation

/-- info: 'ForgacsTran.card_rootsIn_ftDen_eq_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_ftDen_eq_of_norm_lt

/-- info: 'ForgacsTran.card_rootsIn_ftDen_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_ftDen_eventuallyEq

/-- info: 'ForgacsTran.card_rootsIn_eq_two_of_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_eq_two_of_pair

/-- info: 'ForgacsTran.pair_of_card_rootsIn_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pair_of_card_rootsIn_eq_two

/-- info: 'ForgacsTran.abs_div_deriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_div_deriv_le

/-- info: 'ForgacsTran.abs_div_deriv_le_of_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_div_deriv_le_of_scaled

/-- info: 'ForgacsTran.exists_separation_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_separation_radius

/-- info: 'ForgacsTran.exists_neighborhood_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_neighborhood_separation

/-- info: 'ForgacsTran.exists_finite_separation_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_finite_separation_cover

/-- info: 'ForgacsTran.interior_data_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interior_data_of_pieces

/-- info: 'ForgacsTran.ftAngle_eq_arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAngle_eq_arg

/-- info: 'ForgacsTran.clusterAlpha_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterAlpha_im

/-- info: 'ForgacsTran.exists_endpoint_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_chart

/-- info: 'ForgacsTran.cubic_interior_cos_error_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_interior_cos_error_C1

/-- info: 'ForgacsTran.cubic_local_strong_clock_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubic_local_strong_clock_closed

/-- info: 'ForgacsTran.exists_interior_data_on_subinterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interior_data_on_subinterval

/-- info: 'ForgacsTran.exists_interior_data_on_subinterval_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interior_data_on_subinterval_pi

/-- info: 'ForgacsTran.exists_interior_data_on_subinterval_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_interior_data_on_subinterval_two_le

/-- info: 'ForgacsTran.ft_minModulus_at_branch_linear_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_minModulus_at_branch_linear_two

/-- info: 'ForgacsTran.ftAngle_eq_pi_add_arctan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAngle_eq_pi_add_arctan

/-- info: 'ForgacsTran.arg_blowup_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arg_blowup_root

/-- info: 'ForgacsTran.tendsto_expI_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_expI_slope

/-- info: 'ForgacsTran.sum_ite_cluster_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_ite_cluster_eq

/-- info: 'ForgacsTran.tendsto_ftAngleSum_blowup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftAngleSum_blowup

/-- info: 'ForgacsTran.hasDerivAt_ftAngleDerivTau_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngleDerivTau_tau

/-- info: 'ForgacsTran.hasDerivAt_ftAngleDerivAngle_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngleDerivAngle_tau

/-- info: 'ForgacsTran.hasDerivAt_ftAngleDerivTau_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngleDerivTau_angle

/-- info: 'ForgacsTran.hasDerivAt_ftAngleDerivAngle_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngleDerivAngle_angle

/-- info: 'ForgacsTran.ft_equidistribution_of_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_equidistribution_of_discrepancy

/-- info: 'ForgacsTran.ft_angular_clock_of_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_angular_clock_of_discrepancy

/-- info: 'ForgacsTran.amplitudeWindows_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amplitudeWindows_spec

/-- info: 'ForgacsTran.windowRadius_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms windowRadius_le

/-- info: 'ForgacsTran.tendsto_deletedLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_deletedLength

/-- info: 'ForgacsTran.eventually_deletedLength_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_deletedLength_le_one

/-- info: 'ForgacsTran.angular_count_lower_of_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_count_lower_of_components

/-- info: 'ForgacsTran.angular_count_lower_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_count_lower_uniform

/-- info: 'ForgacsTran.hasDerivAt_ftAngle_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngle_comp

/-- info: 'ForgacsTran.hasDerivAt_ftAngleSumDerivAngle_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngleSumDerivAngle_comp

/-- info: 'ForgacsTran.hasDerivAt_ftAngleSumDerivTau_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftAngleSumDerivTau_comp

/-- info: 'ForgacsTran.hasDerivAt_ftTauDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftTauDeriv

/-- info: 'ForgacsTran.hasDerivAt_ftTauDeriv_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftTauDeriv_principal

/-- info: 'ForgacsTran.hasDerivAt_ftBranchGamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchGamma

/-- info: 'ForgacsTran.hasDerivAt_ftGammaDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftGammaDeriv

/-- info: 'ForgacsTran.card_le_of_one_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_le_of_one_le_sum

/-- info: 'ForgacsTran.angular_window_count_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_window_count_lower

/-- info: 'ForgacsTran.angular_window_count_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms angular_window_count_upper

/-- info: 'ForgacsTran.abs_angular_discrepancy_le_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_angular_discrepancy_le_max

/-- info: 'ForgacsTran.exists_endpoint_local_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_local_inverse

/-- info: 'ForgacsTran.exists_cluster_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_cluster_branch

/-- info: 'ForgacsTran.cluster_member_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster_member_root

/-- info: 'ForgacsTran.cluster_member_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster_member_ne

/-- info: 'ForgacsTran.endpoint_package_of_two_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_package_of_two_le_rho

/-- info: 'ForgacsTran.endpoint_retained_partial_of_two_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_retained_partial_of_two_le_rho

/-- info: 'ForgacsTran.clusterDir_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterDir_pow

/-- info: 'ForgacsTran.clusterDir_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterDir_inj

/-- info: 'ForgacsTran.clusterDir_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterDir_ne_zero

/-- info: 'ForgacsTran.clusterAlpha_mul_clusterDir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterAlpha_mul_clusterDir

/-- info: 'ForgacsTran.cluster_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cluster_covers

/-- info: 'ForgacsTran.ftClusterParam_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftClusterParam_pow

/-- info: 'ForgacsTran.exists_tendsto_ftClusterParam_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_ftClusterParam_div

/-- info: 'ForgacsTran.tendsto_cluster_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_cluster_slope

/-- info: 'ForgacsTran.exists_ftBranch_phase_curvature_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranch_phase_curvature_bound

/-- info: 'ForgacsTran.ft_local_strong_clock_at_branch_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_local_strong_clock_at_branch_applies

/-- info: 'ForgacsTran.exists_ft_local_strong_clock_at_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ft_local_strong_clock_at_branch

/-- info: 'ForgacsTran.hasDerivAt_polyQuot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_polyQuot

/-- info: 'ForgacsTran.hasDerivAt_ftRatComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftRatComp

/-- info: 'ForgacsTran.hasDerivAt_ftRatCompDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftRatCompDeriv

/-- info: 'ForgacsTran.ftAmp_eq_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmp_eq_ratio

/-- info: 'ForgacsTran.continuousAt_ftTauDeriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousAt_ftTauDeriv2

/-- info: 'ForgacsTran.continuousAt_ftGammaDeriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousAt_ftGammaDeriv2

/-- info: 'ForgacsTran.eval_ftCritical_ftPrincipal_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ftCritical_ftPrincipal_ne_zero

/-- info: 'ForgacsTran.hasDerivAt_ftBranchAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchAmp

/-- info: 'ForgacsTran.hasDerivAt_ftBranchAmpDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchAmpDeriv

/-- info: 'ForgacsTran.continuousAt_ftBranchAmpDeriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousAt_ftBranchAmpDeriv2

/-- info: 'ForgacsTran.ftBranchAmp_eq_ftAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchAmp_eq_ftAmp

/-- info: 'ForgacsTran.ftBranchAmp_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchAmp_ne_zero

/-- info: 'ForgacsTran.hasDerivAt_ftBranchPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchPhase

/-- info: 'ForgacsTran.ftBranchAmp_eq_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchAmp_eq_polar

/-- info: 'ForgacsTran.ftAmp_eq_polar_at_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmp_eq_polar_at_branch

/-- info: 'ForgacsTran.continuousOn_ftBranchPhaseCurvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuousOn_ftBranchPhaseCurvature

/-- info: 'ForgacsTran.exists_ftBranch_phase_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranch_phase_deriv_bound

/-- info: 'ForgacsTran.exists_ft_branch_clock_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ft_branch_clock_data

/-- info: 'ForgacsTran.ft_branch_clock_data_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_branch_clock_data_applies

/-- info: 'ForgacsTran.exists_principal_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_principal_index

/-- info: 'ForgacsTran.pow_eq_pow_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pow_eq_pow_of_tendsto

/-- info: 'ForgacsTran.blockRight_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blockRight_mono

/-- info: 'ForgacsTran.clampTo_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clampTo_eq_self

/-- info: 'ForgacsTran.ftAngularDiscrepancy_of_supply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAngularDiscrepancy_of_supply

/-- info: 'ForgacsTran.main_bound_of_supply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_of_supply

/-- info: 'ForgacsTran.main_bound_interval_of_supply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_bound_interval_of_supply

/-- info: 'ForgacsTran.exists_clusterDir_of_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_clusterDir_of_pow

/-- info: 'ForgacsTran.abs_ftBranchAmpNormDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_ftBranchAmpNormDeriv_le

/-- info: 'ForgacsTran.exists_ftBranchAmpDeriv_norm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranchAmpDeriv_norm_bound

/-- info: 'ForgacsTran.hasDerivAt_ftBranchAmpNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftBranchAmpNorm

/-- info: 'ForgacsTran.add_le_scaled'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms add_le_scaled'

/-- info: 'ForgacsTran.exists_ftBranchZDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranchZDeriv_bound

/-- info: 'ForgacsTran.exists_ftTauDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftTauDeriv_bound

/-- info: 'ForgacsTran.exists_ftTau_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftTau_bounds

/-- info: 'ForgacsTran.exists_local_contour_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_local_contour_data

/-- info: 'ForgacsTran.ftBranchErr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchErr_spec

/-- info: 'ForgacsTran.ft_pole_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_pole_data

/-- info: 'ForgacsTran.norm_cast_pow_real_mul'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_cast_pow_real_mul'

/-- info: 'ForgacsTran.norm_pow_real_mul_smul'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_pow_real_mul_smul'

/-- info: 'ForgacsTran.pow_mul_le_of_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pow_mul_le_of_floor

/-- info: 'ForgacsTran.clusterSlope_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterSlope_inj

/-- info: 'ForgacsTran.eventually_eq_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_eq_of_cover

/-- info: 'ForgacsTran.exists_index_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_index_of_cover

/-- info: 'ForgacsTran.exists_cluster_family_of_two_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_cluster_family_of_two_le_rho

/-- info: 'ForgacsTran.exists_phase_deriv_bound_zpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phase_deriv_bound_zpow

/-- info: 'ForgacsTran.phase_deriv_bound_uniform_in_collar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_deriv_bound_uniform_in_collar

/-- info: 'ForgacsTran.exists_ft_interior_C1_on_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ft_interior_C1_on_window

/-- info: 'ForgacsTran.exists_ftBranchErr_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranchErr_C1

/-- info: 'ForgacsTran.weighted_dominance_ftCoeffPoly_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_ftCoeffPoly_of_threshold

/-- info: 'ForgacsTran.exists_upper_endpoint_of_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_endpoint_of_reflected

/-- info: 'ForgacsTran.exists_ftBranchErr_C0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranchErr_C0

/-- info: 'ForgacsTran.exists_ft_local_strong_clock_at_branch_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ft_local_strong_clock_at_branch_closed

/-- info: 'ForgacsTran.ft_local_strong_clock_at_branch_closed_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_local_strong_clock_at_branch_closed_applies

/-- info: 'ForgacsTran.exists_endpoint_dominance_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_dominance_of_threshold

/-- info: 'ForgacsTran.exists_endpoint_dominance_of_split_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_dominance_of_split_of_threshold

/-- info: 'ForgacsTran.exists_upper_endpoint_of_reflected_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_endpoint_of_reflected_of_threshold

-- guard's message wraps -- it is written from the probe, not from a neighbour.
/-- info: 'ForgacsTran.exists_upper_endpoint_dominance_of_split_of_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_endpoint_dominance_of_split_of_threshold

/-- info: 'ForgacsTran.exists_dominance_threshold_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_dominance_threshold_of_threshold

/-- info: 'ForgacsTran.weighted_dominance_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_of_threshold

/-- info: 'ForgacsTran.weighted_dominance_ftCoeffPoly_at_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_ftCoeffPoly_at_of_threshold

-- guard's message wraps -- it is written from the probe, not from a neighbour.
/-- info: 'ForgacsTran.weighted_dominance_of_branch_any_multiplicity_at_of_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms weighted_dominance_of_branch_any_multiplicity_at_of_threshold

/-- info: 'ForgacsTran.exists_absorbing_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_absorbing_constant

/-- info: 'ForgacsTran.eval_ftDen_ne_zero_on_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ftDen_ne_zero_on_sphere

/-- info: 'ForgacsTran.exists_endpoint_contour_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_contour_bound

/-- info: 'ForgacsTran.ftSepWindow_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftSepWindow_pos

/-- info: 'ForgacsTran.norm_lt_ftSepRadius_of_le_x1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_lt_ftSepRadius_of_le_x1

/-- info: 'ForgacsTran.ftAngularDiscrepancy_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAngularDiscrepancy_of_dominance

/-- info: 'ForgacsTran.exists_ftPhaseSupply_of_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftPhaseSupply_of_dominance

/-- info: 'ForgacsTran.hdom_of_threshold_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hdom_of_threshold_form

/-- info: 'ForgacsTran.notMem_amplitudeWindows_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms notMem_amplitudeWindows_of_gap

/-- info: 'ForgacsTran.exists_endpoint_contour_window_of_two_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_contour_window_of_two_le_rho

/-- info: 'ForgacsTran.eval_eq_zero_of_mem_diskRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_eq_zero_of_mem_diskRoots

/-- info: 'ForgacsTran.ftSepRatio_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftSepRatio_lt_one

/-- info: 'ForgacsTran.mem_diskRoots_of_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_diskRoots_of_eval_eq_zero

/-- info: 'ForgacsTran.norm_lt_of_mem_diskRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_lt_of_mem_diskRoots

/-- info: 'ForgacsTran.amplitudeWindows_meets_interior_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amplitudeWindows_meets_interior_clause

/-- info: 'ForgacsTran.exists_ftBranch_taylor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftBranch_taylor_bound

/-- info: 'ForgacsTran.exists_cubic_taylor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_cubic_taylor_bound

/-- info: 'ForgacsTran.simple_and_complete_of_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simple_and_complete_of_card

/-- info: 'ForgacsTran.ftSepRadius_lt_ftNextRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftSepRadius_lt_ftNextRoot

/-- info: 'ForgacsTran.exists_eq_of_eval_ftRootPoly_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_eq_of_eval_ftRootPoly_eq_zero

/-- info: 'ForgacsTran.card_rootsIn_ftRootPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_ftRootPoly

/-- info: 'ForgacsTran.card_rootsIn_ftDen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_ftDen

/-- info: 'ForgacsTran.exists_z_window_of_two_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_z_window_of_two_le_rho

/-- info: 'ForgacsTran.exists_retained_set_of_two_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_retained_set_of_two_le_rho

/-- info: 'ForgacsTran.exists_cluster_index_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_cluster_index_of_cover

/-- info: 'ForgacsTran.mem_ftClusterSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_ftClusterSet

-- guard's message wraps -- it is written from the probe, not from a neighbour.
/-- info: 'ForgacsTran.exists_principal_pair_cluster_indices_of_two_le_rho' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exists_principal_pair_cluster_indices_of_two_le_rho

/-- info: 'ForgacsTran.exists_lower_cluster_enumeration_of_two_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_lower_cluster_enumeration_of_two_le_rho

/-- info: 'ForgacsTran.deriv_phase_eq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_phase_eq_ne_zero

/-- info: 'ForgacsTran.derivative_eval_ne_zero_of_transversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivative_eval_ne_zero_of_transversal

/-- info: 'ForgacsTran.phase_deriv_bound_uniform_in_collar_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_deriv_bound_uniform_in_collar_of_bound

/-- info: 'ForgacsTran.exists_residue_asymptotics_of_slopes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_residue_asymptotics_of_slopes

/-- info: 'ForgacsTran.conj_clusterAlpha_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conj_clusterAlpha_zero

/-- info: 'ForgacsTran.phase_zero_localized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_zero_localized

/-- info: 'ForgacsTran.phase_zero_index_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_zero_index_unique

/-- info: 'ForgacsTran.adjacent_phase_zeros_consecutive_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms adjacent_phase_zeros_consecutive_index

/-- info: 'ForgacsTran.tendsto_norm_sub_one_div_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_norm_sub_one_div_of_slope

/-- info: 'ForgacsTran.clusterOmega_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_inj

/-- info: 'ForgacsTran.clusterOmega_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_one_eq

/-- info: 'ForgacsTran.clusterOmega_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterOmega_zero_eq

/-- info: 'ForgacsTran.exists_linear_gap_of_slopes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_linear_gap_of_slopes

/-- info: 'ForgacsTran.exists_quantization_point_in_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_quantization_point_in_interval

/-- info: 'ForgacsTran.card_rootsIn_ftDen_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_ftDen_upper

/-- info: 'ForgacsTran.ftDen_ne_zero_of_upper_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftDen_ne_zero_of_upper_window

/-- info: 'ForgacsTran.exists_simple_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_simple_radius

/-- info: 'ForgacsTran.card_diskRoots_eq_card_rootsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_diskRoots_eq_card_rootsIn

/-- info: 'ForgacsTran.norm_lt_of_mem_diskRoots_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_lt_of_mem_diskRoots_of_sphere

/-- info: 'ForgacsTran.exists_upper_z_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_z_window

/-- info: 'ForgacsTran.ftUpperWindow_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftUpperWindow_pos

/-- info: 'ForgacsTran.eq_one_of_pow_eq_one_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_one_of_pow_eq_one_of_nonneg

/-- info: 'ForgacsTran.exists_upper_amplitude_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_amplitude_floor

/-- info: 'ForgacsTran.ftPrincipal_ftTauArc_eq_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_ftTauArc_eq_lower

/-- info: 'ForgacsTran.eval_derivative_ftRootPoly_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_ftRootPoly_zero

/-- info: 'ForgacsTran.tendsto_upper_member_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_upper_member_slope

/-- info: 'ForgacsTran.tendsto_ftPrincipal_div_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftPrincipal_div_upper

/-- info: 'ForgacsTran.tendsto_upper_normalized_modulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_upper_normalized_modulus

/-- info: 'ForgacsTran.exists_linear_gap_of_modulus_slopes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_linear_gap_of_modulus_slopes

/-- info: 'ForgacsTran.upper_gap_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upper_gap_coeff_pos

/-- info: 'ForgacsTran.exists_upper_endpoint_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_endpoint_block

/-- info: 'ForgacsTran.exists_upper_contour_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_contour_bound

/-- info: 'ForgacsTran.ftPrincipal_ftTauArc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_ftTauArc_zero

/-- info: 'ForgacsTran.hasDerivWithinAt_ftPrincipal_ftTauArc_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivWithinAt_ftPrincipal_ftTauArc_lower

/-- info: 'ForgacsTran.exists_lower_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_lower_chart

/-- info: 'ForgacsTran.conj_ftPrincipal_ftTauArc_eq_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conj_ftPrincipal_ftTauArc_eq_lower

/-- info: 'ForgacsTran.ftBranchZLower_arc_end_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchZLower_arc_end_agree

/-- info: 'ForgacsTran.ftTauArc_le_of_ftTauLower_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftTauArc_le_of_ftTauLower_le

/-- info: 'ForgacsTran.lower_cluster_enumeration_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower_cluster_enumeration_of_chart

/-- info: 'ForgacsTran.exists_lower_endpoint_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_lower_endpoint_block

/-- info: 'ForgacsTran.ft_weighted_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance

/-- info: 'ForgacsTran.ft_weighted_dominance_hypotheses_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_hypotheses_nonvacuous

/-- info: 'ForgacsTran.ft_weighted_dominance_fixed_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_fixed_circle

/-- info: 'ForgacsTran.ft_interior_data_on_arc_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_interior_data_on_arc_two_le

/-- info: 'ForgacsTran.ft_separation_hmin_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_separation_hmin_interior

/-- info: 'ForgacsTran.ft_weighted_dominance_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_unconditional

/-- info: 'ForgacsTran.ft_interior_data_on_arc_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_interior_data_on_arc_one

/-- info: 'ForgacsTran.two_le_rootMultiplicity_ftDen_endpoint_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_le_rootMultiplicity_ftDen_endpoint_pi

/-- info: 'ForgacsTran.rootMultiplicity_ftDen_endpoint_pi_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootMultiplicity_ftDen_endpoint_pi_eq_two

/-- info: 'ForgacsTran.eight_mul_pow_le_prod_of_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eight_mul_pow_le_prod_of_sum_eq_one

/-- info: 'ForgacsTran.card_rootsIn_ftDen_eventuallyEq_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_ftDen_eventuallyEq_of_tendsto

/-- info: 'ForgacsTran.prod_roots_ftDen_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_roots_ftDen_one

/-- info: 'ForgacsTran.exists_upper_contour_bound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_contour_bound_one

/-- info: 'ForgacsTran.eight_mul_le_norm_of_mem_roots_endpoint_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eight_mul_le_norm_of_mem_roots_endpoint_pi

/-- info: 'ForgacsTran.exists_upper_endpoint_binders_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_endpoint_binders_one

/-- info: 'ForgacsTran.tendsto_ftPrincipalAmp_atTop_of_endpoint_double_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftPrincipalAmp_atTop_of_endpoint_double_root

/-- info: 'ForgacsTran.card_rootsIn_endpoint_pi_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_endpoint_pi_eq_two

/-- info: 'ForgacsTran.eval_ne_zero_on_sphere_two_mul_endpoint_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ne_zero_on_sphere_two_mul_endpoint_pi

/-- info: 'ForgacsTran.exists_upper_amplitude_floor_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_amplitude_floor_one

/-- info: 'ForgacsTran.exists_upper_endpoint_binders_one_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_upper_endpoint_binders_one_two_mul

/-- info: 'ForgacsTran.eventually_card_rootsIn_eq_two_near_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_card_rootsIn_eq_two_near_pi

/-- info: 'ForgacsTran.two_le_rootMultiplicity_ftDen_at_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_le_rootMultiplicity_ftDen_at_critical

/-- info: 'ForgacsTran.hasDerivAt_ftSigmaReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftSigmaReal

/-- info: 'ForgacsTran.sum_div_sq_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_div_sq_pos

/-- info: 'ForgacsTran.card_rootsIn_eq_two_of_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_eq_two_of_radius

/-- info: 'ForgacsTran.eval_ne_zero_on_sphere_of_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ne_zero_on_sphere_of_radius

/-- info: 'ForgacsTran.two_le_prod_add_div_of_sum_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_le_prod_add_div_of_sum_inv_eq

/-- info: 'ForgacsTran.clearance_ge_relative_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clearance_ge_relative_gap

/-- info: 'ForgacsTran.two_le_prod_add_div_of_sum_inv_eq_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_le_prod_add_div_of_sum_inv_eq_neg

/-- info: 'ForgacsTran.lt_of_ftSigmaReal_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lt_of_ftSigmaReal_eq_zero

/-- info: 'ForgacsTran.ftSigmaReal_pos_at_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftSigmaReal_pos_at_midpoint

/-- info: 'ForgacsTran.eventually_upper_retained_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_upper_retained_one

/-- info: 'ForgacsTran.exists_ftSigmaReal_eq_zero_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ftSigmaReal_eq_zero_between

/-- info: 'ForgacsTran.sum_div_add_eq_of_eval_ftCriticalReal_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_div_add_eq_of_eval_ftCriticalReal_neg

/-- info: 'ForgacsTran.eval_derivative_two_ftDen_of_double_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_derivative_two_ftDen_of_double_root

/-- info: 'ForgacsTran.ftPrincipalAmp_floor_of_endpoint_pi_of_multiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipalAmp_floor_of_endpoint_pi_of_multiplicity

/-- info: 'ForgacsTran.rootMultiplicity_ftDen_eq_two_at_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootMultiplicity_ftDen_eq_two_at_critical

/-- info: 'ForgacsTran.clearance_ge_relative_gap_of_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clearance_ge_relative_gap_of_r

/-- info: 'ForgacsTran.pow_sub_one_sub_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pow_sub_one_sub_smul

/-- info: 'ForgacsTran.succ_mul_esymm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms succ_mul_esymm_le

/-- info: 'ForgacsTran.prod_one_add_le_two_add_two_mul_prod_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_one_add_le_two_add_two_mul_prod_one_sub

/-- info: 'ForgacsTran.geomQuot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms geomQuot_zero

/-- info: 'ForgacsTran.norm_weighted_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_weighted_ge

/-- info: 'ForgacsTran.two_mul_sub_sum_le_norm_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_sub_sum_le_norm_sum

/-- info: 'ForgacsTran.prod_one_add_lt_of_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_one_add_lt_of_interior

/-- info: 'ForgacsTran.derivative_simplexPoly_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivative_simplexPoly_eval_one

/-- info: 'ForgacsTran.simplexPoly_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simplexPoly_coeff_nonneg

/-- info: 'ForgacsTran.simplexPoly_eval_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simplexPoly_eval_two

/-- info: 'ForgacsTran.simplexPoly_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simplexPoly_eval_zero

/-- info: 'ForgacsTran.simplexPoly_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simplexPoly_zero

/-- info: 'ForgacsTran.sum_coeff_eq_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_coeff_eq_eval_one

/-- info: 'ForgacsTran.sum_smul_coeff_eq_derivative_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_smul_coeff_eq_derivative_eval_one

/-- info: 'ForgacsTran.exists_endpoint_phase_deriv_bound_of_deriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_phase_deriv_bound_of_deriv2

/-- info: 'ForgacsTran.exists_endpoint_phase_deriv_bound_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_phase_deriv_bound_witness

/-- info: 'ForgacsTran.norm_deriv_sub_le_of_lipschitzOnWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_deriv_sub_le_of_lipschitzOnWith

/-- info: 'ForgacsTran.two_mul_lt_norm_of_root_endpoint_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_lt_norm_of_root_endpoint_pi

/-- info: 'ForgacsTran.ft_weighted_dominance_one_hypotheses_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_one_hypotheses_nonvacuous

/-- info: 'ForgacsTran.ft_weighted_dominance_one_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_one_unconditional

/-- info: 'ForgacsTran.eval_ftDen_branch_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_ftDen_branch_value

/-- info: 'ForgacsTran.ftBranchZLowerAt_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchZLowerAt_agree

/-- info: 'ForgacsTran.ftBranchZLower_eq_ftBranchZLowerAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftBranchZLower_eq_ftBranchZLowerAt

/-- info: 'ForgacsTran.exists_ft_endpoint_phase_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ft_endpoint_phase_deriv_bound

/-- info: 'ForgacsTran.deriv_ftFiber_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_ftFiber_eq_zero

/-- info: 'ForgacsTran.analyticAt_ftFiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms analyticAt_ftFiber

/-- info: 'ForgacsTran.eq_zero_of_hasDerivAt_ftPencilImDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_zero_of_hasDerivAt_ftPencilImDeriv

/-- info: 'ForgacsTran.ftPencilIm_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPencilIm_neg

/-- info: 'ForgacsTran.exists_endpoint_factorization_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_factorization_rho_one

/-- info: 'ForgacsTran.hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one

/-- info: 'ForgacsTran.continuous_ftPencilImDeriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuous_ftPencilImDeriv2

/-- info: 'ForgacsTran.ftPencilImDeriv2_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPencilImDeriv2_zero

/-- info: 'ForgacsTran.hasDerivAt_ftPencilImDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_ftPencilImDeriv

/-- info: 'ForgacsTran.abs_ftPencilIm_sub_linear_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_ftPencilIm_sub_linear_le

/-- info: 'ForgacsTran.abs_im_logDeriv_endpoint_factorization_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_im_logDeriv_endpoint_factorization_le

/-- info: 'ForgacsTran.eventuallyEq_endpointCofactor_of_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventuallyEq_endpointCofactor_of_quotient

/-- info: 'ForgacsTran.exists_bound_im_logDeriv_endpointCofactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_im_logDeriv_endpointCofactor

/-- info: 'ForgacsTran.hasDerivWithinAt_ftPrincipal_ftTauLower_of_simple_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms hasDerivWithinAt_ftPrincipal_ftTauLower_of_simple_endpoint

/-- info: 'ForgacsTran.exists_phase_branch_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phase_branch_of_bound

/-- info: 'ForgacsTran.hasDerivWithinAt_ftPrincipal_ftTauLower_of_not_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms hasDerivWithinAt_ftPrincipal_ftTauLower_of_not_root

/-- info: 'ForgacsTran.hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one_of_bracket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one_of_bracket

/-- info: 'ForgacsTran.rho_one_hgd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rho_one_hgd

/-- info: 'ForgacsTran.clearance_ge_relative_gap_of_r_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clearance_ge_relative_gap_of_r_general

/-- info: 'ForgacsTran.clearance_ge_sub_two_mul_relative_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clearance_ge_sub_two_mul_relative_gap

/-- info: 'ForgacsTran.exists_ft_endpoint_phase_deriv_bound_of_tau2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_ft_endpoint_phase_deriv_bound_of_tau2

/-- info: 'ForgacsTran.lt_norm_of_root_endpoint_of_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lt_norm_of_root_endpoint_of_separation

/-- info: 'ForgacsTran.ftAngleDeriv2AngleTau_eq_ftAngleDeriv2TauAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAngleDeriv2AngleTau_eq_ftAngleDeriv2TauAngle

/-- info: 'ForgacsTran.exists_endpoint_phase_deriv_bound_of_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_phase_deriv_bound_of_contDiffOn

/-- info: 'ForgacsTran.exists_endpoint_phase_deriv_bound_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_phase_deriv_bound_of_chart

/-- info: 'ForgacsTran.contDiffAt_chart_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms contDiffAt_chart_ray

/-- info: 'ForgacsTran.contDiffAt_polarAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms contDiffAt_polarAngle

/-- info: 'ForgacsTran.hasDerivAt_normalized_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_normalized_zero

/-- info: 'ForgacsTran.normalized_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normalized_at_zero

/-- info: 'ForgacsTran.exists_varPhase_of_sum_eVariationOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_varPhase_of_sum_eVariationOn

/-- info: 'ForgacsTran.ftNormPoly_coeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftNormPoly_coeff_one

/-- info: 'ForgacsTran.ftNormPoly_coeff_two_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftNormPoly_coeff_two_neg

/-- info: 'ForgacsTran.ftNormPoly_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftNormPoly_coeff_zero

/-- info: 'ForgacsTran.norm_le_one_of_mem_confinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_le_one_of_mem_confinement

/-- info: 'ForgacsTran.one_add_ne_zero_of_lt_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_add_ne_zero_of_lt_neg

/-- info: 'ForgacsTran.eq_one_of_mem_confinement_of_norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_one_of_mem_confinement_of_norm_eq_one

/-- info: 'ForgacsTran.band_subset_Ioo_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms band_subset_Ioo_pi

/-- info: 'ForgacsTran.exists_band_of_amplitude_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_band_of_amplitude_zeros

/-- info: 'ForgacsTran.Icc_subset_cover_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icc_subset_cover_three

/-- info: 'ForgacsTran.abs_le_of_cover_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_le_of_cover_three

/-- info: 'ForgacsTran.prod_ne_pow_of_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_ne_pow_of_norm_one

/-- info: 'ForgacsTran.prod_ne_zero_of_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_ne_zero_of_norm_one

/-- info: 'ForgacsTran.exists_varPhase_of_blocks_of_derivEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_varPhase_of_blocks_of_derivEq

/-- info: 'ForgacsTran.ft_weighted_dominance_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_rho_one

/-- info: 'ForgacsTran.modInterp_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modInterp_ne_one

/-- info: 'ForgacsTran.modInterp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modInterp_zero

/-- info: 'ForgacsTran.norm_modInterp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_modInterp_one

/-- info: 'ForgacsTran.one_le_norm_one_add_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_le_norm_one_add_arc

/-- info: 'ForgacsTran.modInterp_of_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms modInterp_of_norm_one

/-- info: 'ForgacsTran.norm_pos_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_pos_of_one_le

/-- info: 'ForgacsTran.one_le_re_one_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_le_re_one_sub_mul

/-- info: 'ForgacsTran.re_one_sub_mul_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_one_sub_mul_neg

/-- info: 'ForgacsTran.ftAmp_eq_fixed_mul_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftAmp_eq_fixed_mul_prod

/-- info: 'ForgacsTran.hasDerivAt_sum_polarAngle_of_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_sum_polarAngle_of_factorization

/-- info: 'ForgacsTran.ne_root_of_ftAmp_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ne_root_of_ftAmp_ne_zero

/-- info: 'ForgacsTran.sum_eVariationOn_finExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_eVariationOn_finExt

/-- info: 'ForgacsTran.continuous_eval_of_continuous_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuous_eval_of_continuous_coeff

/-- info: 'ForgacsTran.continuous_coeff_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuous_coeff_derivative

/-- info: 'ForgacsTran.card_rootsIn_eq_of_continuous_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_eq_of_continuous_family

/-- info: 'ForgacsTran.ftNormPolyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftNormPolyC

/-- info: 'ForgacsTran.ftNormPolyC_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftNormPolyC_coeff

/-- info: 'ForgacsTran.ftNormPolyC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftNormPolyC_eq

/-- info: 'ForgacsTran.ftNormPolyC_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftNormPolyC_eval

/-- info: 'ForgacsTran.natDegree_ftNormPolyC_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_ftNormPolyC_lt

/-- info: 'ForgacsTran.ftQuotC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftQuotC

/-- info: 'ForgacsTran.ftQuotC_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftQuotC_coeff

/-- info: 'ForgacsTran.natDegree_ftQuotC_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_ftQuotC_lt

/-- info: 'ForgacsTran.X_sq_mul_ftQuotC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms X_sq_mul_ftQuotC

/-- info: 'ForgacsTran.sq_mul_ftQuotC_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sq_mul_ftQuotC_eval

/-- info: 'ForgacsTran.ftQuotC_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftQuotC_eval_zero

/-- info: 'ForgacsTran.mem_sphere_neg_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_sphere_neg_one_iff

/-- info: 'ForgacsTran.ftQuotC_eval_ne_zero_of_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftQuotC_eval_ne_zero_of_norm_one

/-- info: 'ForgacsTran.exists_bound_of_finite_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_of_finite_exceptional

/-- info: 'ForgacsTran.lt_neg_of_sum_eq_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lt_neg_of_sum_eq_neg

/-- info: 'ForgacsTran.one_lt_norm_one_add_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_lt_norm_one_add_witness

/-- info: 'ForgacsTran.sum_eVariationOn_branch_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_eVariationOn_branch_le

/-- info: 'ForgacsTran.ft_weighted_dominance_rho_one_hypotheses_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_rho_one_hypotheses_nonvacuous

/-- info: 'ForgacsTran.ft_weighted_dominance_rho_one_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_rho_one_of_le

/-- info: 'ForgacsTran.exists_bound_im_centeredCofactor_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_im_centeredCofactor_logDeriv

/-- info: 'ForgacsTran.ft_weighted_dominance_rho_one_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_rho_one_unconditional

/-- info: 'ForgacsTran.ft_weighted_dominance_rho_one_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_rho_one_two_le

/-- info: 'ForgacsTran.ft_weighted_dominance_rho_one_two_le_hypotheses_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_rho_one_two_le_hypotheses_nonvacuous

/-- info: 'ForgacsTran.ft_weighted_dominance_rho_one_two_le_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ft_weighted_dominance_rho_one_two_le_unconditional

/-- info: 'ForgacsTran.windowRadius_le_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms windowRadius_le_common

/-- info: 'ForgacsTran.abs_im_logDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_im_logDeriv_le

/-- info: 'ForgacsTran.exists_bound_im_endpointCofactor_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_im_endpointCofactor_logDeriv

/-- info: 'ForgacsTran.exists_bound_of_continuousOn_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_bound_of_continuousOn_of_tendsto

/-- info: 'ForgacsTran.exists_contDiffAt_local_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_contDiffAt_local_inverse

/-- info: 'ForgacsTran.exists_endpoint_phase_deriv_bound_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_phase_deriv_bound_of_comp

/-- info: 'ForgacsTran.exists_endpoint_phase_deriv_bound_of_deriv2_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_phase_deriv_bound_of_deriv2_limit

/-- info: 'ForgacsTran.exists_endpoint_phase_deriv_bound_zpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_endpoint_phase_deriv_bound_zpow

/-- info: 'ForgacsTran.exists_ft_endpoint_phase_deriv_bound_of_tau_limits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exists_ft_endpoint_phase_deriv_bound_of_tau_limits

/-- info: 'ForgacsTran.exists_phase_family_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_phase_family_of_bound

/-- info: 'ForgacsTran.exists_tau_limits_of_tendsto_ftTauDeriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tau_limits_of_tendsto_ftTauDeriv2

/-- info: 'ForgacsTran.exists_tendsto_of_tendsto_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendsto_of_tendsto_deriv

/-- info: 'ForgacsTran.exists_threshold_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_threshold_of_bound

/-- info: 'ForgacsTran.ftPrincipal_miss_and_meet_both_occur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_miss_and_meet_both_occur

/-- info: 'ForgacsTran.ftPrincipal_miss_or_meet_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftPrincipal_miss_or_meet_once

/-- info: 'ForgacsTran.ft_dominance_cell_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ft_dominance_cell_of_admissible

/-- info: 'ForgacsTran.hasDerivAt_endpointCofactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_endpointCofactor

/-- info: 'ForgacsTran.im_logDeriv_endpoint_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms im_logDeriv_endpoint_factorization

/-- info: 'ForgacsTran.miss_or_meet_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms miss_or_meet_once

/-- info: 'ForgacsTran.norm_deriv_sub_le_of_norm_deriv2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_deriv_sub_le_of_norm_deriv2_le

/-- info: 'ForgacsTran.norm_endpointCofactorDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_endpointCofactorDeriv_le

/-- info: 'ForgacsTran.norm_endpointCofactor_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_endpointCofactor_sub_le

/-- info: 'ForgacsTran.norm_sub_smul_deriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_sub_smul_deriv_le

/-- info: 'ForgacsTran.polarModulus_eq_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polarModulus_eq_norm

/-- info: 'ForgacsTran.simple_of_card_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simple_of_card_eq_one

/-- info: 'ForgacsTran.tendsto_ftGammaDeriv2_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_ftGammaDeriv2_of_tendsto

/-- info: 'ForgacsTran.finite_zeros_of_hasDerivAt_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_zeros_of_hasDerivAt_ne_zero

/-- info: 'ForgacsTran.finite_zeros_witness_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_zeros_witness_nonempty
