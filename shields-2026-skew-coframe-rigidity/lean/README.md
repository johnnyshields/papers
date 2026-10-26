# Lean 4 formalization — Coframe rigidity and finite stationary separation for skew Schur functions

Lean 4 formalization (Lean `v4.34.1`, Mathlib `v4.34.1`, namespace `SkewCoframeRigidity`) of `shields-2026-skew-coframe-rigidity.tex`.  Everything here is `sorry`-free, and every headline result is pinned by `AxiomCheck` to exactly `[propext, Classical.choice, Quot.sound]`.

The paper proves that a connected skew diagram is determined by its skew Schur function together with the function of the same fixed connected cap spliced onto it, and derives zero-free linearized, finite stationary and unshifted opposite-end consequences from complete rational Jacobi–Trudi coframes.  The formalization covers every numbered result: the coframe atlas and coprimality, weak-cap recognition, fixed-cap rigidity, complete unit restoration with the linearized theorem and the first cell-splice grade, highest-component matching, one-power stationary separation with whole-field descent, and the unshifted exclusion.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```
lake exe cache get
lake build
```

## Result coverage

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.  A row marked **⚠️ Partial** below reflects the state of the Lean formalization, not of the paper.

| Where | Result | Status | Lean declaration | Note |
|---|---|---|---|---|
| Thm. `sc:fixed-cap` | Fixed-cap rigidity | ✅ Full | `FixedCap.fixed_cap_rigidity_unconditional`, `capDescent`, `capVanishing` | proved by strong induction on child span over all connected caps |
| Thm. `sc:linearized-cap` | Zero-free linearized fixed-cap rigidity | ✅ Full | `UnitRestoration.linearized_cap` | |
| Thm. `sc:positive-power` | One-power stationary separation | ✅ Full | `Coframe.positive_power` | |
| Cor. `cor:stationary-field-descent` | Whole moving potential | ✅ Full | `Coframe.stationary_field_descent` | base field `ℚ`; ambient field an arbitrary extension |
| Lem. `ph:unshifted-exclusion` | Unshifted opposite-end exclusion | ✅ Full | `Unshifted.unshifted_exclusion` | |

## Structural coverage

| Where | Item | Status | Lean declaration | Note |
|---|---|---|---|---|
| `sc:row-degree` | Row degree, largest generator and signed proper corner, irreducibility; coherent homogenization irreducible and relatively prime to its corner | ✅ Full | `BetaDiagram.rowDegree`, `largestGenerator`, `connected_irreducible`, `cohSchur_posRowDegree`, `not_theta_dvd_cohSchur`, `cohSchur_irreducible`, `cohSchur_isRelPrime_cohCorner`, `cohSchur_eq_of_schur_eq'`, `cohSchur_primitive`, `cohSchurFrac_irreducible`, `cohSchurFrac_isRelPrime_cohCornerFrac` | both forms proved: in `ℚ[ϑ, H₁, H₂, …]`, and over `ℚ(ϑ)` as a polynomial in the positive letters (primitive over `ℚ[ϑ]`, irreducible, relatively prime to the corner), via a Gauss lemma for `MvPolynomial` |
| `sc:splice-flags` | The `00`-splice is an actual connected normalized diagram | ✅ Full | `splice`, `splice_connected`, `splice_norm`, `splice_span` | |
| `sc:exact-shift-cap` | Exact shift identity of the clipped operator | ✅ Full | `clippedOp_X_mul` | |
| `ex:same-cell-cap` | The cell cap separates the equal hooks | ✅ Full | `hooks_schur_eq`, `hooks_ne`, `cellSplice_schur_ne` | |
| `sc:atlas` | Support, algebraic independence and inverse of the coframe coordinates | ✅ Full | `Coframe.atlasCoords_algebraicIndependent`, `numerator_coeff_eq_zero_iff`, `schur_eq_corner_mul_topQuotient` | |
| `sc:coprime` | Irreducibility and coprimality of coframes | ✅ Full | `Coframe.coframe_irreducible`, `coframe_isCoprime`, `eq_of_coframe_eq` | |
| `sc:coequal-data` | Defect orders for coequal pairs | ✅ Full | `Coframe.coequal_data`, `coequal_distinct` | |
| `lem:cap-recognition` | Weak-cap recognition and absolute flags | ✅ Full | `CapRecognition.WeakCap.numerator_irreducible`, `ratio_injective`, `ratio_empty` | Differs from the paper's route.  The paper's staged elimination for `gcd(D,R)=1` is replaced by an induction on cap length through Desnanot–Jacobi. |
| `sc:splice-identity` | `s_{K◁B} = κ_K κ_B [z^{c+a}] H C_K G_B` | ✅ Full | `FixedCap.schurOf_splice` | |
| `sc:unit-expansion` | Scaled determinant expansion, core diagram, regularity, coequal core data | ✅ Full | `UnitRestoration.coequal_core`, `scaled_schur_expansion`, `coframe_regular_at_zero`, `det_scaledMatrix_series` | |
| `sc:finite-injectivity` | Finite injectivity, with and without units | ✅ Full | `Coframe.finite_injectivity`, `finite_injectivity_unitFree` | |
| `sc:splice-nonzero` | First cell-splice grade | ✅ Full | `UnitRestoration.splice_nonzero`, `UnitRestoration.adjugate_difference_order`, `UnitRestoration.contraction_order_ge` | `UnitRestoration.adjDifference_unit_exact`, `adjDifference_core_exact`, `adjDifference_self_exact`, `contraction_unit_exact`, `contraction_core_exact`: the whole-array and contraction orders are lower bounds, and the bounds are attained at single adjugate entries and single-entry contractions |
| `sc:component-remainder`, `sc:top-support` | Highest-component remainder and support | ✅ Full | `Coframe.component_remainder`, `top_support` | |
| `sc:top-matching` | Highest-component matching | ✅ Full | `Coframe.top_matching` | |
| `ex:terminal-coframes` | Terminal coframes of the equal hooks | ✅ Full | `Coframe.hooks_defect` | |

## Differences from the paper

- The Lean proof of the first defect coefficient does not pass through the display `[z^{M+1}]D = -J₂|_{e=0}/κ`; it argues from the cell-splice difference directly.

## Dependencies

The tree wires `_lean_shared/Shields` and `_lean_shared/Vendor` through the lakefile.  The `SkewCofactorIndependence` modules are copied from the sibling formalization of the cofactor-independence paper, each marked `TODO-COPIED`.

| Module | Provenance |
|---|---|
| `SkewCofactorIndependence.Base.*`, `BetaDiagrams`, `CompleteAlgebra`, `ConnectedIrreducibility`, `CornerAlgebra`, `CornerMinors`, `OrdinaryReadings`, `PolynomialReadings`, `WeightedReadings` | copied from `skew-cofactor-independence/lean` |
| `Shields.LinearAlgebra.Matrix.DesnanotJacobi` | `_lean_shared/Shields` |
| `Vendor.AlgebraicCombinatorics.DeterminantsBasic` | `_lean_shared/Vendor` |

## License

The files in this directory are released under the MIT license; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the `LICENSE.txt` at the root of the repository.

## References

1. V. Reiner, K. M. Shaw, and S. van Willigenburg, *Coincidences among skew Schur functions*, Adv. Math. 216 (2007).
2. F. Barekat, V. Reiner, and S. van Willigenburg, *Corrigendum to “Coincidences among skew Schur functions”*, Adv. Math. 220 (2009).
3. J. Shields, *Boundary reconstruction and cofactor rigidity for skew Schur functions*.

Refer to the paper for references.
