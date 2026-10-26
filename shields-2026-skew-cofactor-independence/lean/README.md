# Lean 4 formalization — Cofactor independence and dilation for skew Schur functions

A Lean 4 (`v4.34.1`) development in namespace `SkewCofactorIndependence` for `shields-2026-skew-cofactor-independence.tex`.  The compiled modules contain no `sorry`, project axioms, or `native_decide`; they prove both cofactor clauses, nonnegative rigidity, the symmetric unit kernel, and the dilation and nullity theorems.

The paper determines all rational cofactor relations on the dense class and reconstructs diagrams with nonnegative Jacobi–Trudi indices.  It then classifies the change in the first-variation kernel under integral dilation and proves restoration rigidity when the base unit kernel vanishes.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```sh
lake exe cache get
lake build
```

Mathlib and the toolchain are pinned by the package files.  The shared `_lean_shared/` directory is required beside the paper directories.

## Result coverage

All proofs in the paper are unconditional and noncomputational.  The statuses below describe the Lean formalization: every listed result is proved under the paper's standing hypotheses, with no additional proof-gap assumptions.

The axiom guards pin the actual proof footprints.  The finite-word and profile results do not require classical choice.

| Where | Result | Paper | Lean |
|---|---|---|---|
| §1 Thm 1.1 | cofactor relations | `thm:cofactor-relations` | ✅ Full — `BetaDiagram.nonsymmetric_cofactor_relations` and `symmetric_cofactor_relations` give independence, the complete relation kernel, and exact ranks. |
| §2 Thm 2.3 | nonnegative-index rigidity | `thm:nonnegative-rigidity` | ✅ Full — `BetaDiagram.nonnegative_rigidity` recovers an arbitrary connected equal mate up to translation or rotation; only the source diagram must have nonnegative indices. |
| §4 Prop 4.1 | path expansion | `prop:path-expansion` | ✅ Full — `BetaDiagram.restoration_path_expansion`, `restoration_path_entry`, and `restoration_path_terminates` give the actual sorted determinant, deletion sign, strict chains, and termination. |
| §4 Prop 4.4 | symmetric unit kernel | `prop:symmetric-unit-kernel` | ✅ Full — `BetaDiagram.symmetric_unitKernel_eq` and `symmetricUnitCoordinates` prove antisymmetry, the relation basis, and exact dimension. |
| §5 Thm 5.2 | dilation | `thm:dilation` | ✅ Full — `BetaDiagram.dilation_kernel_general` identifies the actual kernel as the internal direct sum of inherited relations and odd off-grid residue functions. `dense_nonsymmetric_dilation_kernel` supplies cofactor independence automatically on the dense nonsymmetric class. |
| §5 Cor 5.3 | nullity increment | `cor:nullity-increment` | ✅ Full — `BetaDiagram.dilation_nullity_increment_general` and `dilation_nullity_modulus_one_general` give the exact off-grid orbit count and modulus-one floor formula. |
| §6 Cor 6.1 | independent restorations | `cor:independent-restorations` | ✅ Full — `BetaDiagram.independent_restorations` accepts every connected equal mate of arbitrary order, recovers its residual core, aligns it by nonnegative rigidity, and recovers the restored set from the trivial base kernel. |

## Structural coverage

Declaration names below are in namespace `SkewCofactorIndependence`.

| Where | Result | Paper | Lean |
|---|---|---|---|
| §1 eq. (1.1) | rotation condition | `eq:rotation-condition` | ✅ Full — `BetaDiagram.normalized_symmetric_betas` identifies the reflection center with the normalized span. |
| §1 eq. (1.2) | first variation | `eq:unit-intro` | ✅ Full — `BetaDiagram.unitVariation`, with actual signed complementary determinants and strict return factors. |
| §2 eq. (2.1) | ordered profile | `eq:profile` | ✅ Full — `BetaDiagram.translationEquivalent_iff_profile`, `rotate_rowLength`, and `rotate_overlap` reconstruct the actual lists and transport their profile under half-turn. |
| §2 Lem 2.1 | polynomial readings | `lem:polynomial-readings` | ✅ Full — `BetaDiagram.schur_totalDegree`, `square_initialForm`, and `square_initial_coefficient` give row count and the coefficient-one row-length monomial; `CornerMinors` proves the largest-generator and padded-corner readings. |
| §2 eq. (2.2) | corner coefficient | `eq:corner-coefficient` | ✅ Full — `CornerMinors` extracts the actual corner coefficient and proves its nonvanishing. |
| §2 Lem 2.2 | exterior gaps | `lem:exterior-gaps` | ✅ Full — `ExteriorGaps` proves the private and tied-margin coefficient formulas and recovers the unordered exterior margins. |
| §2 eq. (2.3) | border lists | `eq:border` | ✅ Full — `ExteriorGaps` constructs the actual corner diagram and its endpoint extensions with their beta coordinates. |
| §3 eq. (3.1) | cofactor degree | `eq:cofactor-degree` | ✅ Full — `BetaDiagram.cofactor_index_homogeneous` gives the exact positive generator-index degree even without density; `cofactor_ne_zero` proves nonvanishing on the dense class. |
| §3 eq. (3.2) | interlaced indices | `eq:interlaced-indices` | ✅ Full — `BetaDiagram.symmetric_interlacing` and `BetaDiagram.diagonalLabel_pos`; order and density supply all strict inequalities. |
| §3 eq. (3.3) | symmetric leader | `eq:symmetric-leader` | ✅ Full — `BetaDiagram.symmetricMinor_initialForm`, `BetaDiagram.symmetric_leader_label`, and `BetaDiagram.symmetricMinorExponent_injective`. Maximum-square leaders of actual complementary determinants are distinct on the representative half. |
| §3 Lem 3.1 | boundary pair | `lem:boundary-pair` | ✅ Full — `BoundaryCofactors` proves nonproportionality of the actual boundary cofactors. |
| §3 eq. (3.4) | cofactor relation | `eq:cofactor-relation` | — A rational linear-relation hypothesis, consumed by the cofactor theorem. |
| §3 eq. (3.5) | private derivative | `eq:private-derivative` | ✅ Full — `CofactorDerivatives` identifies the exact signed complementary determinant derivative. |
| §4 eq. (4.1) | block determinant | `eq:schur-complement` | ✅ Full — `BetaDiagram.regroup_marked_det` and `restoration_path_expansion` identify the actual sorted diagram with the division-free finite block determinant and its deletion sign. |
| §4 eq. (4.2) | path entry | `eq:path-entry` | ✅ Full — `StrictTriangularPaths.reduced_entry_strict_paths` and `StrictTriangularPaths.orderedPathSum_eq_zero_of_card_le` give actual strict chains and termination. |
| §4 eq. (4.3) | first components | `eq:first-components` | ✅ Full — `BetaDiagram.restoration_first_coefficients`, `restoration_coeff_below`, and `restoration_lowest_nonzero` give the exact lowest and next components. `unitVariation_ordinary_component` and `unitVariation_index_homogeneous` prove their actual ordinary and generator-index degrees. |
| §4 Lem 4.3 | endpoint cancellation | `lem:endpoint-cancellation` | ✅ Full — `BetaDiagram.unitVariation_endpoint`; zero-freeness identifies the strict return vectors with genuine matrix rows and columns. |
| §5 eq. (5.1) | endpoint modulus | `eq:endpoint-modulus` | ✅ Full — `BetaDiagram.endpointModulus`, its positivity theorem, and `DilationGeometry` identify the actual endpoint gcd. |
| §5 Lem 5.1 | endpoint normalization | `lem:endpoint-normalization` | ✅ Full — `EndpointNormalization` proves the finite-word period and odd residue-function characterization under the stated core hypotheses. |
| §5 eq. (5.2) | all-edge cancellation | `eq:all-edges` | — A standing edge-quadratic hypothesis of endpoint normalization. |
| §5 eq. (5.3) | off-grid space | `eq:offgrid-space` | ✅ Full — `ResidueSpaces` and `KernelDilation` construct the odd residue space and its injective restriction to actual positions. |
| §5 eq. (5.4) | dilation kernel | `eq:dilation-kernel` | ✅ Full — `BetaDiagram.dilation_kernel_general` is equality of the actual relation subspaces. |
| §5 eq. (5.5) | off-grid relation | `eq:offgrid-relation` | ✅ Full — `QuadraticReturns`, `DisjointAlphabet`, and `KernelDilation` prove regrouping and coefficientwise cancellation. |
| §5 eq. (5.6) | nullity increment | `eq:nullity-increment` | ✅ Full — `KernelNullity` proves the arithmetic dimension equality. |
| §5 Ex 5.4 | dilation ray | `ex:dilation-ray` | ✅ Full — `dilationRayCore_unitKernel`, `dilationRayCore_dilation_nullity`, and `dilationRayKernelBasis_apply` prove the trivial base kernel, every positive dilation's exact nullity, and the full residue-indicator basis. |
| §6 Ex 6.2 | unequal restorations | `ex:unequal-restorations` | ✅ Full — `restoration_components_eq` and `restoration_full_schur_ne` prove exact two-component agreement and inequality of the full polynomials for the two literal connected parents. |
| §6 eq. (6.1) | restoration separator | `eq:restoration-separator` | ✅ Full — `restorationZ_separator_coefficient` and `restorationW_separator_coefficient` compute the actual full determinant coefficients as −1 and 0. |

The symmetric dilation limitation in the concluding remarks is proved by `symmetricDouble_relation_kernel` and `symmetricDouble_relation_not_inherited_sup_arithmetic`.  `KernelRigidity` gives the symmetric zero-kernel criterion and restoration rigidity for doubled nonsymmetric modulus-one cores.

## Differences from the paper

The rational complete-generator representation is identified with the integral determinant by faithful coefficient extension.  Integral irreducibility is recovered from rational irreducibility and the actual coefficient-one diagonal monomial.  The cofactor and rigidity inductions follow the paper's geometric deletions.  Finite residue-space dimensions are obtained through explicit coordinate equivalences.

The nonsymmetric two-row case uses private-corner differentiation and the one-row child's empty cofactor rather than a separate distinct-label argument.  Exterior and symmetric-unit coefficient extractions are implemented by derivatives, with the factorial and deletion signs retained explicitly.

## Dependencies

| Component | Used by | Description |
|---|---|---|
| `Shields.Combinatorics.Young.LGVTableau` | `Base.RowMultisets`, `Base.TableauBridge` | Shared bounded-tableau and Jacobi–Trudi representation bridges. |
| `Shields.LinearAlgebra.Matrix.DesnanotJacobi` | `ConnectedIrreducibility` | Division-free condensation for the actual corner minors. |
| `Vendor.AlgebraicCombinatorics.DeterminantsBasic` | `Base.MongeMinors` | Row-to-column determinant expansion from the external algebraic-combinatorics project. |
| `Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions` | `Base.SymmetricSpecialization` | Complete-symmetric polynomial algebraic independence from the same external project. |

## License

The files in this directory are released under the MIT license; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the `LICENSE.txt` at the root of the repository.

## References

1. J. Shields, *Cofactor independence and dilation for skew Schur functions*.
2. J. Shields, *Boundary reconstruction and cofactor rigidity for skew Schur functions*.  The copied polynomial and diagram substrate comes from that formalization.

Refer to the paper for references.
