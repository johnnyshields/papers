# Lean 4 formalization — Factor Schur functions of marked compositions from differential operators

A Lean 4 (`v4.34.1`) development in namespace `SkewMarkedFactor` for `shields-2026-skew-marked-factor.tex`.  Coverage below distinguishes proved assemblies from missing mathematics; no project axiom or proof-gap hypothesis is used to stand for a missing result.

The paper recovers the inner and outer Schur functions from a parent function and a supplied period, for ordinary legal charts with arbitrary connected outers and for mixed legal charts with ribbon outers.  It also compares ordinary Schur-equal charts at a common period under inner rigidity and exhibits both recovery mechanisms.  It does not select a period or construct a chart for an arbitrary mate.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```sh
lake exe cache get
lake build
```

The pinned Mathlib packages and the repository-wide `_lean_shared/` tree are required.

## Result coverage

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.  A row marked **⚠️ Partial** below reflects the state of the Lean formalization, not of the paper.

| Where | Result | Paper | Lean |
|---|---|---|---|
| §4 Thm 4.2 | factor recovery at a supplied period | `thm:extraction` | ✅ Full — `factor_recovery` gives the exact terminal order, canonical primitive inner readout, complete normalized-character outer readout, and actual fraction-field ratios in both ordinary conventions. `factor_recovery_empty_vertical` explicitly covers the vertical empty edge. |
| §4 Cor 4.3 | prescribed-period rejection test | `cor:period-test` | ✅ Full — `period_test` rejects every proper ordinary chart with the supplied parent function and period from a zero first derivative or a nonrational actual quotient. |
| §5 Prop 5.1 | mixed ribbon factor recovery | `rt:mixed-readout` | ✅ Full — `mixed_factor_recovery` proves that the parent function and the period determine the inner and the ribbon outer functions of any legal mixed chart, with no phase or normalization exponent supplied; `mixed_inner_readout_general` gives the inner readout by primitive gcd reduction, and `mixed_terminal_data`, `outer_proportional` and `readout_injective` the triangular outer readout. |
| §5 Cor 5.2 | ordinary and mixed terminal ratios | `lem:terminal-readout` | ✅ Full — `ordinary_ratio_display` supplies the ordinary clause and `mixed_terminal_readout` the mixed clause, with both denominators nonzero and the quotient taken in the fraction field. |
| §6 Thm 6.2 | common-period comparison | `thm:transport` | ✅ Full — `common_period_transport` proves membership of both actual parents in one marked fiber, using the genuine standing inner-rigidity hypothesis and supplied common-period charts. |
| §6 Cor 6.3 | two-row inner specialization | `cor:two-row` | ✅ Full — `two_row_common_period_transport` supplies inner rigidity from row/overlap invariants; the connected outer and the connected mate's initial attachment type are unrestricted. |

## Structural coverage

| Where | Result | Paper | Lean |
|---|---|---|---|
| §2 eq. (2.1) | Jacobi–Trudi and the tableau interpretation | `eq:jt` | ✅ Full — `Gluing.aeval_cellSchur_skewDiagram_all` identifies the actual cell function with the tableau skew Schur polynomial, including disconnected shapes. |
| §2 eq. (2.2) | Hall derivations in both coordinates | `eq:delta` | ✅ Full — `pDeriv_powerSumEquiv` and `pDeriv_h_coordinate_sum` bridge power-sum and complete-homogeneous coordinates. |
| §2 eq. (2.3) | Murnaghan–Nakayama | `eq:mn` | ✅ Full — `Gluing.Plan.pDeriv_cellSchur_left` and `Gluing.Plan.pDeriv_cellSchur_right` give both actual ribbon-removal sums. |
| §2 eq. (2.4) | width and period | `eq:period` | — Definitions in `Gluing.MarkedInner`; admissibility is a standing geometric hypothesis. |
| §2 eq. (2.5) | hatted cell sets | `eq:hats` | — Definitions `Gluing.hatMarkFin` and `Gluing.hatMiddleFin`; their geometric and Schur-function properties are proved in the action substrate. |
| §2 eq. (2.6) | ordinary copy origins | `eq:ordinary-offsets` | — The ordinary clauses of `Gluing.MarkedInner.origin` define the actual union of translated cell copies. |
| §2 eq. (2.7) | span of a legal composition | `eq:span` | ✅ Full — `readout_span_compose` covers every admitted mark, including the vertical empty edge. |
| §2 eq. (2.8) | normalization functions | `eq:normalizers` | — `normalizerRow`, `normalizerColumn`, and `normalizerDiagonal` are the Schur functions of the actual three cell sets. |
| §2 Lem 2.1 | key-ribbon deletion | `lem:ribbon-deletion` | ✅ Full — `ribbon_deletion` proves the southeast correspondence for arbitrary skew outers, exact integer heights, absence in the normalizer pieces, and actual remainder products. |
| §2 eq. (2.9) | ribbon remainder | `eq:ribbon-remainder` | ✅ Full — `southeast_ribbon_remainder` includes exhaustion of the outer, using algebraic empty value one. |
| §2 eq. (2.10) | modified-map normalization | `eq:modified` | ✅ Full — `modified_normalization` and `modified_empty` separate the algebraic empty symbol from geometric empty composition. |
| §2 Lem 2.2 | ordinary power-sum action | `lem:action` | ✅ Full — `ordinary_action`, `ordinary_word_action`, and `xi_factor_normalizers` supply the action, nonzero multiplier, degree, and both empty-edge readings. |
| §2 eq. (2.11) | signed period action | `eq:action` | ✅ Full — `ordinary_action` and `normalization_killed` include the additional vertical outer sign. |
| §3 Lem 3.1 | mixed-chart annihilation | `lem:mixed-vanishing` | ✅ Full — `mixed_period_derivative_zero` covers all positive period multiples; `mixed_excludes_ordinary_multiple` excludes nonempty ordinary skew outers without properness or factor-size bounds. |
| §3 eq. (3.1) | periodic mixed boundary and end caps | `eq:mixed-boundary` | ✅ Full — `mixed_boundary` and `mixed_boundary_caps` prove the normalized interior range, both end steps, exact span, and positive width in case (d); case (c) is its transported rotation. |
| §3 eq. (3.2) | generator-defined composition homomorphism | `eq:algebra-map` | ✅ Full — `compositionMap` is the algebra map with \(\Psi_\eta(h_j)=A^{j-1}b_j\) (`compositionMap_hPos`) for every attachment case, and `intertwine_of_generators` reduces covariance with a derivation to the generators; `compositionMap_cellSchur` is the bridge to the all-type normalization. |
| §3 eq. (3.3) | complete all-type signed modifier | `eq:full-normalization` | ✅ Full — `compositionMap_cellSchur` proves \(\Psi_\eta(s_D)=\mathcal N_\eta(D)s_{D\circ_\eta E}\) for every legal mark and connected outer, with the sign \((-1)^{n(D)}\) of `fullNormalizer` (`signExponent_ordinary` for the ordinary cases) and the complete normalizer; the cases (a)–(d) are `compositionMap_cellSchur_ordinary`, `compositionMap_cellSchur_c` and `compositionMap_cellSchur_d`. |
| §3 eq. (3.4) | weighted derivation | `eq:weighted-operator` | ✅ Full — `wDeriv` is the derivation \(V_k\) of the actual ring \(\Lambda\), with `wDeriv_hPos`, `wDeriv_elem`, and `wDeriv_pPoly` computing it on complete, elementary, and Newton generators. |
| §3 eq. (3.5) | original-order weighted beta replacements | `eq:weighted-beta-moves` | ✅ Full — `wDeriv_jtDet` and `wDeriv_hh` prove the identity for all integer entries, including zero and negative indices. |
| §3 Lem 3.2 | mixed weighted covariance | `rt:mixed-covariance` | ✅ Full — `mixed_covariance` is \(V_{kp}\Phi=\chi^k\Phi(pV_k+\rho\delta_k)\) on all of \(\Lambda\) for every legal mixed mark in the positive-phase convention, and `wDeriv_period_inner_mixed` is \(V_ps_E=\rho\chi\); case (c) is the whole rotation of case (d) (`compositionMap_rotate`, `mixedChi_rotate`). |
| §3 eq. (3.6) | mixed generator and algebra intertwining | `rt:mixed-intertwining` | ✅ Full — `wDeriv_rowComposite` computes \(V_{kp}b_m\) with the positive phase factor and the sign \((-1)^{-kv_1}\), `mixed_generator_intertwining` is the generator identity with the full normalizer, and `mixed_covariance_d` lifts it to the algebra. |
| §3 eq. (3.7) | literal mixed strip remainder | `eq:mixed-strip-remainder` | ✅ Full — `rowPower_strip_eq` is the separated cell identity, `rowPower_strip_cellSchur` its Schur function, and `compose_rowCells_zero` the exhaustion convention \(F_0=W\) used only in the remainder. |
| §3 Lem 3.3 | unified composition covariance | `lem:covariance` | ✅ Full — `ordinary_covariance` and `mixed_covariance_full` give the Hall, weighted and offset clauses with \(\xi=\delta_ps_E\) (`xi_factor_normalizers`), and `readoutMap_outer` the identity \(\Phi(Q)=\mathcal N_\eta(D)s_{D\circ_\eta E}\) in the read-outer convention. |
| §3 eq. (3.8) | ordinary Hall and weighted identities | `eq:ordinary-covariance` | ✅ Full — `readout_hall_covariance` and `readout_weighted_covariance` prove \(\delta_{kp}\Phi=\xi^k\Phi\delta_k\) and \(V_{kp}\Phi=\xi^k\Phi(pV_k+\theta\delta_k)\) in the read-outer convention; `wDeriv_period_inner_ordinary` gives \(V_ps_E=\theta\xi\) with integer \(\theta\), \(\lvert\theta\rvert<p\), and `ordTheta_eq_phases` identifies \(\theta=s-t\) in case (a), with \(\theta=0\) at the empty edge. |
| §3 eq. (3.9) | mixed Hall zero and weighted identity | `eq:mixed-covariance` | ✅ Full — `mixed_hall_zero` proves \(\delta_{kp}\Phi=0\) on all of \(\Lambda\) and `mixed_covariance_full` assembles it with the weighted identity. |
| §3 eq. (3.10) | physical involution signs | `eq:physical-operator-transport` | ✅ Full — `wDeriv_schurInvolution` proves \(V_j\omega=(-1)^j\omega V_j\) and `Plan.pDeriv_schurInvolution` the Hall sign; `compositionMap_anti` transports the composition map across antitransposition, and `readout_weighted_covariance` carries it to \(\theta_b=-\theta_a\). |
| §3 generator formulas | \(\mathcal B_k\) on \(h_j\) and \(e_j\) | after `lem:covariance` | ✅ Full — `mixedOp_hPos` and `mixedOp_elem` give both formulas for \(pV_k+\rho\delta_k\), including the vanishing for \(j<k\) and the scalar output at \(j=k\). |
| §3 generator span | \(V_{kp}\) annihilates \(A,B,C\) | after `eq:full-normalization` | ✅ Full — `wDeriv_cellSchur_of_span_le` and `wDeriv_normalizers_eq_zero` show that every \(V_r\) with \(r\) at least the span kills the Schur function of a skew diagram, hence \(A,B,C\) for every legal mark and every \(k\ge1\). |
| §4 Lem 4.1 | primitive canonical normalization | `lem:primitive` | ✅ Full — `coefficient_one_minimum_cell_schur` and `primitive_cellSchur_scalar` prove the row-length coefficient-one strict minimum and integral normalization for every skew diagram. |
| §4 eq. (4.1) | complete character expansion and tableau count | `eq:character` | ✅ Full — `cellSchur_character_expansion`, `characterCoefficient_cellSchur_eq_ribbonCharacter`, `standardTableauCount_derivative`, and `standardTableauCount_pos` use all partitions and the genuine finite tableau set. |
| §4 eq. (4.2) | canonical terminal data | `eq:terminal` | ✅ Full — `factor_recovery_order` identifies `terminalOrder`; `terminalDerivative` and `penultimateDerivative` depend only on the parent and period. |
| §4 eq. (4.3) | gcd-reduced inner readout | `eq:inner-recovery` | ✅ Full — `factor_recovery_inner` supplies irreducibility, coprimeness, gcd reduction, and primitive normalization internally. |
| §4 eq. (4.4) | normalized outer readout | `eq:outer-recovery` | ✅ Full — `factor_recovery_outer` and `factor_recovery_outer_primitive` recover the correct attachment-dependent involution. |
| §4 eq. (4.5) | penultimate derivative display | `eq:penultimate` | ✅ Full — `ordinary_penultimate_display` uses the actual tableau count and normalizer exponents. |
| §4 eq. (4.6) | last derivative and next vanishing | `eq:last` | ✅ Full — `ordinary_last_display`, `ordinary_terminal_ne_zero`, and `ordinary_next_eq_zero` identify both ends of the derivative tail. |
| §4 eq. (4.7) | genuine fraction-field ratio | `eq:ratio` | ✅ Full — `ordinary_ratio_display` and `actualRatio_eq_scalar` prove the quotient in `FractionRing`, rather than imposing rationality as a premise. |
| §5 eq. (5.1) | fractional-alphabet terminal evaluation | `eq:mixed-terminal-evaluation` | ✅ Full — `mixedOp_iterate_terminal` proves \(\mathcal B_1^mQ=m!\,p^mQ(1^{\rho/p})\) for every homogeneous \(Q\) of weight \(m\); `ribbon_powerSumSpecialize_ne_zero` proves \(s_D(1^x)\ne0\) for every ribbon \(D\) and rational \(0<x<1\), and `mixed_terminal_evaluation` combines them. |
| §5 eq. (5.2) | mixed terminal order and ratio | `eq:mixed-terminal-ratio` | ✅ Full — `mixed_terminal_data` proves that the terminal order of \(V_p\) on the parent is the number of outer cells, that the weighted tail vanishes beyond it, and that \(V_p^{M-1}P\cdot V_ps_E=V_p^MP\cdot s_E\) with \(V_ps_E=\rho\chi\ne0\); `mixed_inner_readout_general` is the reduced numerator. |
| §5 eq. (5.3) | fixed-order character inversion | `rt:outer-triangle` | ✅ Full — `word_pProd` proves the triangular structure of the ordered words \(\mathcal B_\nu\) on power-sum monomials with nonzero diagonal, `readout_injective` that a function of weight \(m\) is determined by its readout, `mixed_terminal_data` the equality of the \(V_{p\nu}\) quotient with the \(\mathcal B_\nu\) quotient, and `outer_proportional` the recovery of the outer function. |
| §5 eq. (5.4) | ordinary terminal specialization | `eq:ordinary-readout` | ✅ Full — `ordinary_ratio_display` supplies the actual nonzero-denominator ratio. |
| §5 eq. (5.5) | mixed terminal specialization | `eq:mixed-readout` | ✅ Full — `mixed_terminal_readout` proves the weighted ratio \(V_p^{M-1}s_F/V_p^Ms_F=s_E/(\rho\chi)\) with nonzero denominators. |
| §6 eq. (6.1) | antitranspose gauge | `eq:gauge` | ✅ Full — `ordinary_mark_gauge` is equality of actual cell sets and includes both empty-edge readings. |
| §6 Lem 6.1 | ordinary mark atlas | `lem:mark-atlas` | ✅ Full — `ordinary_mark_unique`, `ordinary_mark_displacement`, and `ordinary_mark_gauge` use only the fixed inner and period. |
| §7 eq. (7.1) | general two-row legal family | `eq:two-row-mark` | ✅ Full — `twoRowMark_legal` and `twoRow_normalizers` produce legality and all normalizers from the stated parameter bounds. |
| §7 eq. (7.2) | general two-row terminal formula | `eq:two-row-last` | ✅ Full — `twoRow_formulas` includes arbitrary connected outers, singletons, and all zero-parameter boundaries. |
| §7 eq. (7.3) | general two-row penultimate formula | `eq:two-row-previous` | ✅ Full — `twoRow_formulas` retains the cases of zero overlap, empty marks, and equal overlap and width. |
| §7 eq. (7.4) | nonribbon example tails | `eq:example-tail` | ✅ Full — `example_derivative_tails`, `example_parents_schur_eq`, and `example_parents_not_rotated_translates` prove the literal example and its exact tails. |
| §7 eq. (7.5) | complete six-term outer and empty-edge example | `eq:example-outer` | ✅ Full — `example_outer_readout`, `example_rotated_readouts`, `gaugeExample_vertical_readout`, and `gaugeExample_readout_ne_column` establish both examples, including the indispensable involution. |
| §7 eq. (7.6) | legal mixed hook and weighted tail | `eq:mixed-example` | ✅ Full — `mixedExampleMark_legal`, `mixedExampleParent_eq`, `mixedExampleParent_schur`, `mixedExampleMark_normalizers`, `mixedExample_weighted_tail`, `mixedExample_wDeriv_inner`, `mixedExample_terminal_quotient`, `mixedExample_ratio`, `mixedExample_outer_operators`, and `mixedExample_readout_h2` prove the literal mark, the composite \((3,2,1)/(1)\), the displayed tails, the quotient, the ratios, and the readout of \(h_2\); `mixedExample_Phi_h2` and `mixedExample_Phi_e2` give \(\Phi(h_2)=h_1P\) and \(\Phi(e_2)=-s_{(3,2,1)}\) on the actual composites. |

## Differences from the paper

The sign \(\varepsilon_\eta(D)\) of `eq:full-normalization` is formalized as \((-1)^{n(D)}\) with \(n(D)\) the number of cells of \(D\) that have a cell directly north of them on the same boundary ribbon (`signExponent`, the northbound count of the gluing substrate); it is zero in the ordinary cases.  The paper's phrasing as a sum of ribbon heights of the boundary decomposition is not separately formalized.  The all-type theorem is proved from the kernel of the Schur map on the shape space and the row values of \(\Psi_\eta\), not by quoting the external theorem.

Mixed weighted covariance is proved for a mark in case (d), the case-(c) statement being the whole rotation, which leaves \(\Psi_\eta\) and \(\chi\) unchanged (`compositionMap_rotate`, `mixedChi_rotate`); the antitransposition relations for the mixed maps are not used.

Mixed annihilation uses the proved absence of removable period-multiple ribbons and Murnaghan–Nakayama, rather than expressing the same boundary obstruction as a closed beta set.  The penultimate tableau identity is evaluated after the translation-invariant modified map; literal singleton basis vectors remain distinct in the free shape space.

## Dependencies

The package requires Lean and Mathlib at the versions pinned by `lean-toolchain` and `lake-manifest.json`, together with the repository-wide `_lean_shared/` tree.

| Imported shared component | Role |
|---|---|
| `Shields.Combinatorics.Young.LGVTableau` | Tableau Jacobi–Trudi identity |
| `Shields.Combinatorics.Young.LGVOddTableau` | Dual tableau determinant |
| `Shields.Combinatorics.Young.ElementarySymmetric` | Elementary symmetric-function identities |
| `Shields.Combinatorics.Young.SkewSchurPolynomial` | Actual skew tableau polynomials |
| `Shields.LinearAlgebra.Matrix.DesnanotJacobi` | Determinant condensation used in connected-skew irreducibility |
| `Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions` | Finite-alphabet symmetric-function identities from AlgebraicCombinatorics |

## License

The files in this directory are released under the MIT license; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the `LICENSE.txt` at the root of the repository.

## References

1. J. Shields, *Factor Schur functions of marked compositions from differential operators*.
2. J. Shields, *Local common-factor gluing and reduction of composition necessity for skew Schur functions*.

Refer to the paper for references.
