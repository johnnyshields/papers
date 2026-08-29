/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CompositionLinks
import ForgacsTran.CompositionLinksRhoOne
import ForgacsTran.EndpointArcObstruction
import ForgacsTran.MainAdmissible
import ForgacsTran.PencilIndex
import ForgacsTran.ZeroCount
import ForgacsTran.Reduction
import ForgacsTran.EventualDegree
import ForgacsTran.LaurentReduction
import ForgacsTran.SignAlternation
import ForgacsTran.ClusterContour
import ForgacsTran.LinearCase
import ForgacsTran.Necessity
import ForgacsTran.NecessityBivariate
import ForgacsTran.Dominance
import ForgacsTran.DominanceCellPartition
import ForgacsTran.PhaseStateDichotomy
import ForgacsTran.Bridge
import ForgacsTran.AttractorCoeff
import ForgacsTran.AttractorRouche
import ForgacsTran.AttractorVieta
import ForgacsTran.AttractorBranch
import ForgacsTran.AttractorExpansion
import ForgacsTran.Attractor
import ForgacsTran.AttractorRate
import ForgacsTran.AttractorIndexShift
import ForgacsTran.EquidistributionCounts
import ForgacsTran.CubicEquidistribution
import ForgacsTran.Geometry
import ForgacsTran.Amplitude
import ForgacsTran.ViewingAngle
import ForgacsTran.PhaseVariation
import ForgacsTran.Cluster
import ForgacsTran.AttractorPole
import ForgacsTran.ContourRemainder
import ForgacsTran.WeightedDominance
import ForgacsTran.PhaseCount
import ForgacsTran.ClauseThree
import ForgacsTran.Consequences
import ForgacsTran.Main
import ForgacsTran.AngularBookkeeping
import ForgacsTran.ConsequencesComposition
import ForgacsTran.DenominatorSequence
import ForgacsTran.DominanceAssembly
import ForgacsTran.DominanceFT
import ForgacsTran.EndpointDominance
import ForgacsTran.EndpointRegularity
import ForgacsTran.MainClauses
import ForgacsTran.MainComposition
import ForgacsTran.PoleExpansion
import ForgacsTran.QuadraticCase
import ForgacsTran.CubicWitness
import ForgacsTran.CubicWitnessCluster
import ForgacsTran.CubicWitnessInterior
import ForgacsTran.CubicWitnessComposition
import ForgacsTran.CubicPhaseSign
import ForgacsTran.CubicPhaseDerivative
import ForgacsTran.CubicMain
import ForgacsTran.SimpleEndpoint
import ForgacsTran.SimpleWitness
import ForgacsTran.FavardRootStates
import ForgacsTran.CubicRootStates
import ForgacsTran.LowerEndpointCorner
import ForgacsTran.EndpointCriticalFactor
import ForgacsTran.LowerEndpointSimpleZero
import ForgacsTran.LowerEndpointTangent
import ForgacsTran.PolarAngleBase
import ForgacsTran.TangentVariationBound
import ForgacsTran.AmplitudeAlong
import ForgacsTran.UpperClusterWitness
import ForgacsTran.JointWitness
import ForgacsTran.QuadraticWitness
import ForgacsTran.MainCompositionWitness
import ForgacsTran.QuasiOrthogonalZeros
import ForgacsTran.QuadraticDefect
import ForgacsTran.Sharpness
import ForgacsTran.FTMinModulus
import ForgacsTran.FTGeometryExtraction
import ForgacsTran.FTGeometryAssembly
import ForgacsTran.FTGeometryBranch
import ForgacsTran.PhaseVariationSupply
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.FTMinModulus.PrincipalGap
import ForgacsTran.FTMinModulus.ArgumentCone
import ForgacsTran.FTGeometryClosure
import ForgacsTran.FTBranchAngle
import ForgacsTran.FTBranchAngleBound
import ForgacsTran.FTBranchCritical
import ForgacsTran.FTBranchDeriv
import ForgacsTran.FTBranchExistence
import ForgacsTran.FTBranchMonotone
import ForgacsTran.FTBranchPencil
import ForgacsTran.FTBranchSine
import ForgacsTran.FTBranchValue
import ForgacsTran.ClauseThreeComposition
import ForgacsTran.ClauseThreeMonomial
import ForgacsTran.ClauseThreeWitness
import ForgacsTran.ClauseThreeReduction
import ForgacsTran.ClauseThreeRayRemainder
import ForgacsTran.ClauseThreeQuadraticRay
import ForgacsTran.ClauseThreeDefect
import ForgacsTran.ClauseThreeSupply
import ForgacsTran.ClauseThreeChainObstruction
import ForgacsTran.ClauseThreeAdmissible
import ForgacsTran.FTBranchEndpoint
import ForgacsTran.FTBranchFunction
import ForgacsTran.FTBranchRegularity
import ForgacsTran.FTBranchTauDeriv
import ForgacsTran.FTBranchProp1
import ForgacsTran.FTBranchZMono
import ForgacsTran.FTBranchLimitPoint
import ForgacsTran.FTBranchGap
import ForgacsTran.FTBranchZRate
import ForgacsTran.FTBranchUpper
import ForgacsTran.FTBranchUpperRefutation
import ForgacsTran.FTBranchLemma5
import ForgacsTran.FTClusterSupply
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
import ForgacsTran.EndpointUpperOne
import ForgacsTran.EndpointUpperOneBinders
import ForgacsTran.InteriorBranchSeparation
import ForgacsTran.WeightedDominanceBranch
import ForgacsTran.DominanceBandAntitone
import ForgacsTran.WeightedDominanceBranchOne
import ForgacsTran.EndpointUpperPackage
import ForgacsTran.EndpointUpperMultiplicity
import ForgacsTran.EndpointCofactorBound
import ForgacsTran.ArcPhaseBound
import ForgacsTran.EndpointLowerRhoOne
import ForgacsTran.PencilArcSymmetry
import ForgacsTran.RhoOneEndpointFactorization
import ForgacsTran.LowerSeparationNormalized
import ForgacsTran.LowerSeparationQuotient
import ForgacsTran.AmplitudeBand
import ForgacsTran.PhaseBranchSplit
import ForgacsTran.PhaseVariationBlocks
import ForgacsTran.BranchSupply
import ForgacsTran.PhaseTangency
import ForgacsTran.RhoOneDominanceComposition
import ForgacsTran.QuotientDerivBound
import ForgacsTran.InteriorSeparation
import ForgacsTran.InteriorSupply
import ForgacsTran.CubicBranchBridge
import ForgacsTran.CubicInteriorRemainder
import ForgacsTran.CubicClockSpacing
import ForgacsTran.PrincipalSimple
import ForgacsTran.PrincipalSimpleBranch
import ForgacsTran.BranchCurvature
import ForgacsTran.BranchRadiusMonotone
import ForgacsTran.BranchCircle
import ForgacsTran.BranchTangentSum
import ForgacsTran.BranchAngleDerivSum
import ForgacsTran.BranchAmplitude
import ForgacsTran.PhaseDerivativeBound
import ForgacsTran.BranchInteriorC1
import ForgacsTran.BranchStrongClock
import ForgacsTran.BranchClockSpacing
import ForgacsTran.BranchArcGeometry
import ForgacsTran.BranchDivisorWitness
import ForgacsTran.BranchRetainedNonempty
import ForgacsTran.DominanceSupplyClosure
import ForgacsTran.BranchSupplyWitness
import ForgacsTran.CubicCollisionWitness
import ForgacsTran.BranchSupplyCubicWitness
import ForgacsTran.BranchSupplyGeometry
import ForgacsTran.CubicPhaseSupplyComposition
import ForgacsTran.TauArcAt
import ForgacsTran.CubicPhaseSupplyClosed
import ForgacsTran.RootStatesGeneral
import ForgacsTran.PhaseSupplyCofactor
import ForgacsTran.PhaseSupplyKappaZero
import ForgacsTran.CollisionCollarLeft
import ForgacsTran.UpperEndpointReduced
import ForgacsTran.UpperEndpointRadius
import ForgacsTran.UpperEndpointSlope
import ForgacsTran.LowerEndpointReduced
import ForgacsTran.LowerEndpointRates
import ForgacsTran.LowerCollarSimple
import ForgacsTran.PhaseSupplyRhoOne
import ForgacsTran.UpperCollarOne
import ForgacsTran.PhaseSupplyOne
import ForgacsTran.PhaseSupplyLastCorner
import ForgacsTran.PhaseSupplyLowerCollar
import ForgacsTran.PhaseSupplyUpperRegion
import ForgacsTran.PhaseSupplyRegionBounds
import ForgacsTran.PhaseSupplyGeneral
import ForgacsTran.PhaseSupplyRhoOneClosure
import ForgacsTran.PhaseSupplyUniform
import ForgacsTran.AmplitudeUpperEndpoint
import ForgacsTran.QuadraticCell
import ForgacsTran.AngularDiscrepancy
import ForgacsTran.MainFT
import ForgacsTran.AngularDiscrepancyFT
import ForgacsTran.AngularDiscrepancyAdmissible
import ForgacsTran.AngularSupplyAdmissible
import ForgacsTran.AngularBlocks
import ForgacsTran.FTGeometryCone
import ForgacsTran.AxiomCheck
import ForgacsTran.AngleChartForm
import ForgacsTran.EndpointTauDeriv2
import ForgacsTran.EndpointTauDeriv2Simple

/-!
# Fixed numerators over a Forgács--Tran denominator

The formalization of `../shields-2026-forgacs-tran-numerators.tex`.  Importing this
module imports the whole development.

The tree divides into six groups, in the order the paper needs them.

* **Reduction.**  `Reduction`, `LaurentReduction`, `EventualDegree`,
  `DenominatorSequence` — a fixed numerator is initial data, and the reduced
  coefficient polynomials it produces eventually have the degree the paper claims.
* **Counting.**  `ZeroCount`, `SignAlternation`, `PhaseCount`, `AngularBookkeeping`,
  `ViewingAngle`, `QuasiOrthogonalZeros` — the elementary engine that turns a supply
  of interior zeros into a bound on the zeros outside a prescribed set.
* **Geometry.**  `Geometry`, `Amplitude`, `FTBranch*`, `FTMinModulus`,
  `FTGeometry*`, `EndpointRegularity` — the denominator pencil, its branch of zeros,
  and the residue amplitude that branch carries.
* **Dominance.**  `Dominance`, `WeightedDominance`, `DominanceFT`, `PoleExpansion`,
  `Cluster`, `ContourRemainder`, `EndpointDominance` — the principal conjugate pair
  dominates the coefficient asymptotics, with the remaining poles and the contour
  remainder controlled.
* **Assembly.**  `Bridge`, `Main`, `MainClauses`, `MainComposition`, `ClauseThree*`,
  `Consequences*` — the analytic supply is bundled as `FTInputs` and the three clauses
  of `thm:main` are proved against it, unconditionally in `H`.
* **Witnesses.**  `LinearCase`, `QuadraticCase`, `Quadratic*`, `CubicWitness*`,
  `UpperClusterWitness`, `JointWitness`, `Sharpness`, `Necessity`, `Attractor*` —
  concrete pencils discharging the hypothesis bundles, so that no conditional result
  is vacuous, together with the sharpness and necessity statements.

## Implementation notes

The headline results carry their analytic inputs as an explicit `FTInputs` hypothesis
rather than as global axioms, so `#print axioms` on any of them reports only Lean's
standard three.  `AxiomCheck` pins that footprint for every result the README tabulates.

Sorry-free.

## References

* `../shields-2026-forgacs-tran-numerators.tex` — the whole paper.
* `Forgacs2017RationalDenominator`, whose Problem 14 the paper answers.

## Tags

real-rooted polynomial, rational generating function, exceptional zero, denominator pencil,
residue amplitude, zero distribution
-/
