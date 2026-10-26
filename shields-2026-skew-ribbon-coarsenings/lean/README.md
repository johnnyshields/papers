# Lean 4 formalization — Short coarsenings determine ribbon Schur equivalence

Formalizes `shields-2026-skew-ribbon-coarsenings.tex` against Mathlib
(`leanprover/lean4:v4.34.1`, namespace `SkewRibbonCoarsenings`).  **The development is
unconditional: no `sorry`, no project axiom anywhere in the tree.**  Every headline result below
reports `[propext, Classical.choice, Quot.sound]` under `#print axioms`, pinned by a `#guard_msgs`
in `SkewRibbonCoarsenings/AxiomCheck.lean`.

A composition of weight `n` is carried by its cut set, a subset of `{1, …, n-1}`, and the coarsening
polynomial `G_β` and the multiplicities `m_β(λ)` are defined from it directly.  The paper proves that
unequal coarsening inventories of two compositions of weight `n` have a distinguishing coefficient of
magnitude one or two at a partition with at most `B(n) ≤ Ω(n) + 2` parts, where `B(n)` is an explicit
arithmetic cutoff of order `2 log₆ n`; that equality of inventories is equivalent to a factor-reversal
description of the two compositions, with inventory equivalence a two-sided congruence for the
composition product; and that the cumulative distinguishing depth is given exactly by two recursive
families.  The Lean tree proves all of this, including the classification of Billera, Thomas and van
Willigenburg as an output of the descent, and the inclusion `eq:old-inclusion`.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

## Result coverage

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.  A row
marked **⚠️ Partial** below reflects the state of the Lean formalization, not of the paper.

| Where | Result | Paper | Lean | Status |
|---|---|---|---|---|
| §1 Thm 1.1 | Small discrepancies; modular recognition | `thm:main-recognition`, `eq:main-modular` | `Assembly.thm_main_recognition`, `eq_main_modular`; `MainTheorems.main_recognition_logb` | ✅ Full |
| §1 Thm 1.2 | Structure and composition; near-power stability | `thm:main-structure`, `eq:REV` | `Assembly.thm_main_structure`, `eq_REV`, `eq_congruence` | ✅ Full |
| §1 Thm 1.3 | Exact cumulative depth, and its modular sharpness | `thm:main-depth`, `eq:frontier` | `Assembly.thm_main_depth`, `thm_main_depth_modular`; `DepthFamilies.uBound_le_cumDepth'`, `even_modular_sharp`, `odd_modular_sharp` | ✅ Full |
| §2 Prop 2.4 | Seam, substitution and composition laws, grid projection | `prop:unsigned`, `eq:seam`, `eq:substitution`, `eq:Psi-laws`, `eq:projection`, `eq:split` | `Unsigned.prop_unsigned`, `Seam.G_concat_cuts`, `Unsigned.Psi_G`, `Psi_compCuts`, `Psi_revCuts`, `proj_Psi` | ✅ Full |
| §2 Cor 2.5 | Reversing factors preserves `G` | `cor:reversal-suffices` | `Unsigned.reversal_suffices` | ✅ Full |
| §3 Thm 3.5 | Support separation | `thm:support` | `Support.supportSeparation` | ✅ Full |
| §3 Prop 3.7 | Normalization | `prop:normalization`, `eq:gcd-normalization`, `eq:w`, `eq:basic-periods`, `eq:mask`, `eq:mask-odd` | `Assembly.prop_normalization`, `Normalization.normalization` | ✅ Full |
| §4 Thm 4.4 | Nested marked identity | `thm:nested`, `eq:nested-product` | `NestedIdentity.nested_identity` | ✅ Full |
| §5 Prop 5.3 | Propagation of period masks | `prop:propagation` | `Propagation.propagation` | ✅ Full |
| §5 Prop 5.4 | Termination at a literal common inner factor | `prop:termination`, `eq:common-factor` | `Termination.termination_common_factor` | ✅ Full |
| §5 Prop 5.5 | Local alternative | `prop:local-alternative`, `eq:coarse-local-budget` | `LocalAlternativeProof.localAlternativeB`, `localAlternativeOmega` | ✅ Full |
| §6 Thm 6.1 | Coarse recognition | `thm:coarse`, `eq:coarse-certificate`, `eq:coefficient-grid` | `Assembly.thm_coarse`, `Recognition.coarse_recognition`, `mult_scale` | ✅ Full |
| §6 Prop 6.3 | Recognition under a divisibility-monotone budget | `prop:budget` | `Assembly.prop_budget`, `Recognition.budget_recognition` | ✅ Full |
| §6 Cor 6.4 | Near-power class identity | `cor:class`, `eq:old-inclusion` | `ClassInclusion.cor_class_unconditional`, `oldInclusion` | ✅ Full |
| §6 Cor 6.5 | Modular budget | `cor:modular-budget` | `Assembly.cor_modular_budget`, `Recognition.modular_budget` | ✅ Full |
| §7 Prop 7.4 | Arithmetic budget `B` covers every detector | `prop:refined-budget` | `ArithmeticBound.arithBound_mono`, `arithBound_le_Omega_add_two`, `arithBound_two_pow`, `arithBound_three_pow`, `arithBound_prime_pow`; `DetectorBudget.chain_blocks_le_arithBound`, `chain_blocks_le_omega` | ✅ Full |
| §7 Prop 7.5 | Logarithmic cutoff | `prop:logarithmic-cutoff`, `eq:even-threshold`, `eq:odd-threshold` | `LogarithmicCutoff.arithBound_le_uBound`, `six_pow_arithBound_le`, `arithBound_le_logb`, `arithBound_two_eq_logb`, `logb_const_optimal` | ✅ Full |
| §7 Thm 7.6 | All-odd lift | `thm:lift`, `eq:OA-lift`, `eq:lift-extraction`, `eq:lift-difference` | `LiftIdentity.thm_lift`, `OddInvariant.OA_lift`, `LiftIdentity.lift_extraction`, `lift_difference` | ✅ Full |
| §8 Prop 8.1 | Composition coordinates | `prop:coordinates`, `eq:coordinates` | `Coordinates.prop_coordinates_automorphism`, `eq_coordinates`, `prop_coordinates_retraction` | ✅ Full |
| §8 Prop 8.2 | Leading substitution and content | `prop:depth-cancel`, `eq:leading-substitution` | `DepthCancel.depth_cancel`, `depth_cancel_int`, `content_Psi` | ✅ Full |
| §8 Thm 8.3 | Recovery at prescribed factor weights | `thm:recovery`, `eq:outer-recovery`, `eq:inner-derivative`, `eq:inner-recovery`, `eq:two-factor-cancel` | `Recovery.outer_recovery`, `inner_derivative`, `inner_recovery`, `two_factor_cancel_forward`; `Assembly.eq_two_factor_cancel` | ✅ Full |
| §8 Prop 8.4 | Characteristic-two example | `prop:parity` | `ParityExample.parity_weight_seventeen` | ✅ Full |
| §8 Cor 8.5 | Odd characteristic | `cor:odd-characteristic` | `Assembly.cor_odd_characteristic` | ✅ Full |

The ribbon Schur function is defined independently of `G`, as a Jacobi–Trudi determinant over the
ribbon shape from the shared skew Schur library (`RibbonSchur.ribbonParts_bridge` identifies it with
the tableau sum), so `eq:ribbon-expansion` is a theorem and not a convention
(`RibbonExpansion.ribbon_expansion`, `ribbon_eq_iff`).

## Structural coverage

| Where | Result | Paper | Lean | Status |
|---|---|---|---|---|
| §1 | Inventory `G_β`, multiplicity `m_β(λ)`, substitution `Ψ_ε` | `eq:introG`, `eq:introPsi` | `Defs.G`, `Defs.mult`, `Defs.Psi` | ✅ Full |
| §1 | Depth, `D_=(n)`, `C(N)` | `eq:depth-defs` | `DepthDefs.dep`, `depthEq`, `cumDepth` | ✅ Full |
| §1 | The cited inclusion as a statement | `eq:old-inclusion` | `MainTheorems.OldInclusion`; proved by `ClassInclusion.oldInclusion` | ✅ Full |
| §2 | Labeled count `K` | `eq:K` | `Defs.K` | ✅ Full |
| §2 Lem 2.1 | Labeled counts and multiplicities | `lem:labels`, `eq:label-factor` | `Labels.labeled_count_eq`, `labeled_diff_eq`, `labeled_diff_small` | ✅ Full |
| §2 Rmk 2.2 | Magnitudes one or two survive reduction modulo `q` | `rem:modular-order` | `Labels.labeled_diff_small_not_dvd`, `labeled_example_ones` | ✅ Full |
| §2 | Ribbon expansion | `eq:ribbon-expansion` | `RibbonExpansion.ribbon_expansion` | ✅ Full |
| §2 | Cut set of a composition product | `eq:composition-cuts` | `CompositionProduct.composition_cuts`, `partsCuts_compose`, `compose_assoc`, `compose_reverse` | ✅ Full |
| §2 Lem 2.3 | Literal inner factors | `lem:literal-factor` | `LiteralFactor.literal_factor_iff`, `literal_factor_unique`, `literal_factor_same_inner` | ✅ Full |
| §2 Rmk 2.6 | Near-squaring is not linear | `rem:nonlinear` | `Nonlinear.nonlinear_G_combination`, `nonlinear_nearSquare_coeff`, `no_linear_nearSquare` | ✅ Full |
| §3 | Triangle identity | `eq:uv`, `eq:three-difference` | `TriangleIdentity.three_difference`, `uFun_odd`, `vFun_odd`, `uFun_mul_vFun` | ✅ Full |
| §3 Lem 3.1 | Low-order balance | `lem:low-order`, `eq:FE` | `LowOrder.low_order`, `eqThroughThree_iff_fe` | ✅ Full |
| §3 Lem 3.2, … §3 Lem 3.4 | Clans, constant cuts, color graphs | `lem:small-core`, `lem:deletion`, `lem:color`, `eq:matrix-triangle` | `SkewTernary.small_core`, `graph_fact`, `contract_inseparable_iff`, `exists_inseparable_erase`; `ColorGraphs.color_disconnected` | ✅ Full |
| §3 Rmk 3.6 | Positive null vector | `rem:positive-equilibrium` | `Support.positive_equilibrium` | ✅ Full |
| §4 Lem 4.1 | Fibers of a period | `lem:fiber`, `eq:fiber-period` | `Fiber.fiber_period`, `fiber_eq_zero` | ✅ Full |
| §4 Lem 4.2 | Four-block identity | `lem:four-start`, `eq:four-identity` | `FourStart.four_identity`, `four_bound`, `mask_periodic_of_four_vanish` | ✅ Full |
| §4 Lem 4.3 | Antichain cancellation | `lem:antichain` | `Antichain.antichain_cancellation`; `ChainSums.K_eq_chainSum` | ✅ Full |
| §4 | Detector data of the nested identity | `eq:chain`, `eq:detector-list`, `eq:layers`, `eq:deltaH`, `eq:J` | `NestedStep.NestedData`, `NestedLabels.Nested.detList`, `NestedJ.Jcal_eq_JJ` | ✅ Full |
| §4 Lem 4.5 | Bottom probes | `lem:bottom`, `eq:bottom-probes`, `eq:shifted-reflection` | `BottomProbes.bottom_probes`, `probeF_reflect` | ✅ Full |
| §4 Lem 4.6 | Probe selection | `lem:selection`, `eq:probe-bounds`, `eq:sum-congruence` | `Selection.selection` | ✅ Full |
| §5 Lem 5.1 | Reflected packing | `lem:packing`, `eq:packing-ledger`, `eq:packing-budget`, `eq:original-weight` | `Packing.packing`, `packingBudget_of_two_mul`, `packBox_le` | ✅ Full |
| §5 Ex 5.2 | Reflection example, weight 30 | `ex:reflection` | `ReflectionExample.reflection_ordinary_difference`, `reflection_labeled_difference` | ✅ Full |
| §6 Rmk 6.2 | Shallow induction | `rem:shallow-induction` | `Assembly.rem_shallow_induction`, `Recognition.shallow_transfer` | ✅ Full |
| §6 | Congruence for `∘` | `eq:congruence` | `Assembly.eq_congruence` | ✅ Full |
| §7 Lem 7.1 | Restrictions on period growth | `lem:ratios` | `PeriodRatios.ratios_three`, `ratios_four`, `ratios_doubling_chain` | ✅ Full |
| §7 Lem 7.2 | Ratio-list optimization | `lem:arithmetic-optimization`, `eq:T` | `ArithmeticOptimization.arithmetic_optimization`, `arithT` | ✅ Full |
| §7 Def 7.3 | The cutoff `B(n)` | `def:arithmetic-bound`, `eq:arithmetic-bound` | `ArithmeticBound.arithBound` | ✅ Full |
| §7 | The frontier `U(n)` | `eq:frontier` | `ArithmeticBound.uBound`, `candidate_threshold` | ✅ Full |
| §7 | All-odd invariant and lifted pair | `eq:OA`, `eq:sharpness-lift` | `AlternatingNear.OA`, `liftR`, `liftS` | ✅ Full |
| §7 Rmk 7.7 | Signed versus unsigned depth | `rem:exact-scope` | `OddCharacteristic.exact_scope_unsigned`, `exact_scope_signed` | ✅ Full |
| §8 | Certificate recurrence | `eq:subset-dp` | `SubsetDP.subset_dp`, `partition_subset_dp` | ✅ Full |
| §A | Multilevel detector example | `app:multilevel` | `MultilevelExample.multilevel_ordinary_difference`, `multilevel_labeled_difference` | ✅ Full |

## Differences from paper

| § | Item | Lean declaration | Module | Description |
|---|---|---|---|---|
| §2 | `eq:substitution` | `Unsigned.Psi_G` | `Unsigned` | induction on the number of outer cuts through `eq:seam` in place of grouping coarsenings by the retained outer seams |
| §3 | `lem:small-core` | `SkewTernary.graph_fact_step`, `exists_constCut_of_small_sep` | `SkewTernary` | a cardinality-minimal closed set and a series split in place of the paper's component choice and ordering of complement components; Mathlib has no cograph API |
| §3 | `lem:color` | `ColorGraphs.color_disconnected_aux` | `ColorGraphs` | the four-vertex case is a kernel-evaluated finite check in place of the path-and-star analysis |
| §6 | `thm:coarse` | `Recognition.coarse_recognition_of_budget` | `Recognition` | one induction for a general divisibility-monotone budget, specialized afterwards, so `prop:budget` needs no second proof |
| §7 | `thm:lift` | `OddInvariant.G_wordBd`, `OA_lift` | `OddInvariant` | one involution on retained boundary sets in place of the three cases (only odd, only even, both parities) reflected separately |
| §8 | `eq:inner-derivative` | `Recovery.inner_derivative` | `Recovery` | both sides expanded through a prefix-times-suffix inventory formula and matched term by term in place of the marked-block bijection |

## Dependencies

This development depends on modules in the repository-wide `_lean_shared/` tree, outside the paper's
`lean/` directory.

| Component | Used by | Description |
|---|---|---|
| `Shields.Combinatorics.Young.LGVTableau` | `RibbonSchur`, for `Shields.jacobiTrudiDet`, `Shields.skewSchur`, `Shields.completeHom` and `Shields.jacobiTrudiDet_eq_skewSchur` | Skew Schur functions as sums over semistandard skew tableaux, and the skew Jacobi–Trudi determinant identity, through the Lindström–Gessel–Viennot involution.  Extracted from `edrei-spectral-classification` and shared across the papers.  Reached transitively through it: `Shields.Combinatorics.Young.JacobiTrudi`, `SkewCells`, `LGVInvolution`, `LGVPaths`, `LGVSelection` and `SkewSchurPolynomial` |

## License

Code is made available under the MIT license (see `LICENSE.txt`).

## References

1. L. J. Billera, H. Thomas and S. van Willigenburg, *Decomposable compositions, symmetric
   quasisymmetric functions and equality of ribbon Schur functions*, Advances in Mathematics
   **204** (2006), 204–240. [doi:10.1016/j.aim.2005.05.014](https://doi.org/10.1016/j.aim.2005.05.014)

Refer to the paper for references.
