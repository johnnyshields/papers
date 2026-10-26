# Lean 4 formalization — Class recovery and inflation for repeated-block skew diagrams

Lean 4.34.1 formalization in the `SkewClassInflation` namespace of
`shields-2026-skew-class-inflation.tex`.  The shipping declarations are sorry-free,
use no project axioms or native decision procedures, and have exact axiom guards.
Their footprints are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

The paper determines complete connected skew Schur classes for separated repeated
constant-gap blocks and for asymmetric two-row blocks under profile inflation.
The formalization establishes the full two-row class, both threshold class counts,
full separated-block saturation, erosion, and exact class transport on zero-free
diagrams.  General chart inflation is formalized only in part.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```sh
lake exe cache get
lake build
```

## Result coverage

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.
A row marked **⚠️ Partial** or **❌ Missing** below reflects the state of the Lean formalization, not of the paper.

| Where | Result | Paper | Lean |
|---|---|---|---|
| §1 Thm 1.1 | Complete unrestricted class formula, literal arbitrary-mate inverse, injective parameterization, both exact symmetry-dependent cardinalities, and actual case-(a) legal marked presentations I–V. | `thm:repeated-block-saturation` | ✅ Full — `SkewClassInflation.SaturationInner.repeated_block_saturation`, `SkewClassInflation.SaturationInner.every_mate_legal_presentation` |
| §1 Thm 1.2 | Full class formula, both cardinalities, literal legal charts I–V, and exhaustive generation by ribbon factor reversals and global rotation below the threshold. | `thm:sharp-inflation` | ✅ Full — `SkewClassInflation.ThinParameters.sharp_inflation`, `SkewClassInflation.ThinParameters.inflation_full_class`, `SkewClassInflation.ThinParameters.inflation_full_class_card`, `SkewClassInflation.ThinParameters.subthreshold_literal_chart`, `SkewClassInflation.ThinParameters.inflation_class_generated`, `SkewClassInflation.ribbonClass_eq_factorReversal`, `SkewClassInflation.factorReversal_of_ribbon_eq` |
| §3 Cor 3.3 | Arbitrary connected mate deflation and permanence of lost equality. | `cor:inflation-no-escape` | ✅ Full — `SkewClassInflation.ConnectedProfile.inflation_no_escape`, `SkewClassInflation.ConnectedProfile.equality_at_earlier` |
| §5 Prop 5.3 | The actual two end-row placements satisfy I–V, and affine cell composition agrees literally with every full general source in its specified translation. | `prop:saturation-chart` | ✅ Full — `SkewClassInflation.SaturationInner.literal_legal_chart`, `SkewClassInflation.SaturationInner.markedInner_legal`, `SkewClassInflation.SaturationInner.markedInner_hypothesisV`, `SkewClassInflation.SaturationInner.diagram_compose_eq_source` |
| §6 Thm 6.2 | Complete class, literal parameter injectivity, disjoint orientations, and exact cardinality. | `thm:two-row-thin-class` | ✅ Full — `SkewClassInflation.ThinParameters.thin_full_class`, `SkewClassInflation.ThinParameters.thin_orientations_disjoint`, `SkewClassInflation.ThinParameters.thin_full_class_card`, `SkewClassInflation.ribbonRows_schur` |
| §8 Cor 8.1 | The iterated weight-three ribbon family has exactly 2^e members, so the source class and its first-inflation image have exactly 2^(e+1) members and the image splits into exactly 2^e rotation classes; every image member has exactly its two rotations as all its mates and stays inside the image. | `cor:unbounded-class-splitting` | ✅ Full — `SkewClassInflation.unbounded_class_splitting`, `SkewClassInflation.binaryRibbon_census`, `SkewClassInflation.binaryRibbon_class_card`, `SkewClassInflation.splittingSource_class_card`, `SkewClassInflation.splittingSource_image_card`, `SkewClassInflation.splittingSource_image_class_count`, `SkewClassInflation.splittingSource_image_classes`, `SkewClassInflation.splittingSource_image_closed` |

## Structural coverage

| Where | Result | Paper | Lean |
|---|---|---|---|
| §1 Eq 1.1 | Standing domain for the repeated-block saturation results. | `eq:saturation-domain` | — |
| §1 Eq 1.2 | Actual arbitrary-inner powers and larger-seam source chains. | `eq:repeated-blocks` | ✅ Full — `SkewClassInflation.SaturationInner.power_thick`, `SkewClassInflation.SaturationInner.diagram_thick` |
| §1 Eq 1.3 | The entire unrestricted connected class is exactly both actual outer-ribbon parameter images. | `eq:saturation-class` | ✅ Full — `SkewClassInflation.SaturationInner.full_class` |
| §1 Eq 1.4 | Exact full connected-class cardinality, with original-inner symmetry characterized by a proved literal profile/row-word bridge. Equal endpoints alone do not collapse the orientations. | `eq:saturation-cardinality` | ✅ Full — `SkewClassInflation.SaturationInner.full_class_card`, `SkewClassInflation.SaturationInner.inner_symmetric_iff`, `SkewClassInflation.SaturationInner.orientations_disjoint`, `SkewClassInflation.SaturationInner.full_class_of_palindrome` |
| §1 Eq 1.5 | Literal two-row powers and zero-joined composition diagrams. | `eq:thin-domain` | ✅ Full — `SkewClassInflation.ThinParameters.diagram_thick` |
| §1 Eq 1.6 | Actual profile inflation and exact inverse on its image. | `eq:inflation` | ✅ Full — `SkewClassInflation.Profile.inflate_r`, `SkewClassInflation.Profile.inflate_g`, `SkewClassInflation.Profile.inflate_deflate` |
| §1 Eq 1.7 | Full unrestricted set formula and exact cardinalities. | `eq:inflation-class` | ✅ Full — `SkewClassInflation.ThinParameters.inflation_full_class`, `SkewClassInflation.ThinParameters.inflation_full_class_card` |
| §2 Eq 2.1 | Actual normalized full beta lists and their profile correspondence. | `eq:beta-profile` | ✅ Full — `SkewJacobiNegative.BetaDiagram.toProfile_xi`, `SkewJacobiNegative.BetaDiagram.toProfile_zeta` |
| §2 Eq 2.2 | Standing positivity and adjacent-gap conditions in Profile. | `eq:profile-validity` | — |
| §2 Eq 2.3 | Full actual content span and the general row-minus-gap sum identity. | `eq:content-span` | ✅ Full — `SkewClassInflation.profileCells_span`, `SkewClassInflation.profile_span_sum` |
| §2 Eq 2.4 | Actual private-corner coefficient and cofactor. | `eq:maximal-cofactor` | ✅ Full — `SkewJacobiNegative.BetaDiagram.schur_corner_split` |
| §2 Lem 2.1 | Full-board monomial-cofactor recognition and arbitrary-mate membership. | `lem:hessenberg-membership` | ✅ Full — `SkewClassInflation.cofactor_monomial_iff_hessenberg`, `SkewClassInflation.hessenberg_of_equal_schur` |
| §2 Eq 2.5 | Full-board recognition of monomial maximal cofactors. | `eq:hessenberg-membership` | ✅ Full — `SkewClassInflation.cofactor_monomial_iff_hessenberg` |
| §2 Eq 2.6 | Both actual boundary observations are composed with the copied reconstruction theorem. | `eq:boundary-reconstruction-input` | ✅ Full — `SkewClassInflation.boundary_reconstruction` |
| §2 Eq 2.7 | Actual Hessenberg seam-mask expansion in the complete-generator ring. | `eq:interval-expansion` | ✅ Full — `SkewJacobiNegative.GeneralHessenberg.schur_interval_mask_expansion` |
| §2 Lem 2.2 | Positive distinguished seams and retained zero seams, with actual cut and contracted profiles. | `lem:seam-coefficients` | ✅ Full — `SkewClassInflation.zero_seam_constant_coefficient`, `SkewClassInflation.zero_seam_highest_coefficient` |
| §2 Eq 2.8 | Distinguished positive-seam constant and highest coefficients. | `eq:seam-extremes` | ✅ Full |
| §2 Eq 2.9 | Retained-unit determinant is the actual homogenized specialization. | `eq:unit-homogenization` | ✅ Full — `SkewClassInflation.unitEval_schurHom` |
| §2 Eq 2.10 | Actual zero-seam cut and contraction coefficients. | `eq:unit-extremes` | ✅ Full — `SkewClassInflation.zero_seam_constant_coefficient`, `SkewClassInflation.zero_seam_highest_coefficient` |
| §2 Eq 2.11 | Full literal product-minus-contraction identity at every admissible Hessenberg joining seam. | `eq:cut-merge` | ✅ Full — `SkewClassInflation.Profile.join_schur`, `SkewClassInflation.Profile.zeroJoin_schur` |
| §2 Eq 2.12 | Signed expansion over actual positive coarsenings; exact weights and multiplicities; ribbon equality iff unordered inventories agree; actual coarsenings iff their proper cuts are retained original cuts. | `eq:ribbon-coarsening` | ✅ Full — `SkewClassInflation.ribbon_coarsening_formula`, `SkewClassInflation.coarsenRows_injective`, `SkewClassInflation.coarseningWords_composition`, `SkewClassInflation.ribbon_eq_iff_coarseningPartitions`, `SkewClassInflation.coarsening_partition_count`, `SkewClassInflation.coarsening_partition_weight`, `SkewClassInflation.coarsenRows_exists_iff_cuts_subset`, `SkewClassInflation.ribbon_eq_iff_coarseningInventory`, `SkewClassInflation.coarseningInventory_count_pair` |
| §2 Eq 2.13 | Canonical composition product is exactly the concatenation of the specified actual ordinary near powers. | `eq:ribbon-composition` | ✅ Full — `SkewClassInflation.compositionProduct_blocks`, `SkewClassInflation.compositionProduct_eq_literal` |
| §2 Lem 2.3 | Injective over any integral domain, in every characteristic, without requiring unit leading coefficients. | `lem:triangular-substitution` | ✅ Full — `SkewClassInflation.triangular_substitution_injective` |
| §2 Eq 2.14 | The exact full fraction-field ribbon identity is proved for every actual constant-gap Hessenberg profile, including zero gaps and the one-row boundary. | `eq:constant-gap-substitution` | ✅ Full — `SkewClassInflation.constant_gap_substitution`, `SkewClassInflation.constantGap_denominator_ne_zero`, `SkewClassInflation.constant_gap_equality_iff` |
| §3 Lem 3.1 | Actual erosion with empty rows allowed: the ordinary-degree-n part of the full determinant, with h_j to h_{j-1}, is the determinant of the eroded board; the cell count drops by exactly the number of rows, and whole Schur equality is preserved. | `lem:erosion` | ✅ Full — `SkewClassInflation.erosion_lowering`, `SkewClassInflation.mem_erodeCells_profileCells`, `SkewClassInflation.card_erodeCells_profileCells`, `SkewClassInflation.erodedSchur_eq_of_profileSchur_eq`, `SkewClassInflation.erodedSchur_eq_deflate` |
| §3 Lem 3.2 | Lowering on arbitrary integer full boards, including newly opened entries. | `lem:inflation-lowering` | ✅ Full — `SkewClassInflation.lowering_shifted_det`, `SkewClassInflation.lowering_inflated_profile` |
| §3 Eq 3.1 | Actual homogeneous ordinary-degree lowering operator. | `eq:lowering-map` | ✅ Full — `SkewClassInflation.lowering_shifted_prod` |
| §3 Eq 3.2 | Actual full-board lowering, even at an opening. | `eq:lowering-identity` | ✅ Full — `SkewClassInflation.lowering_shifted_det` |
| §3 Eq 3.3 | Every connected inflated mate has a genuine original mate deflation. | `eq:no-escape` | ✅ Full — `SkewClassInflation.ConnectedProfile.inflation_no_escape` |
| §3 Lem 3.4 | Inverse bijections between the entire connected Schur classes of a zero-free nonline diagram and of its erosion, over every row count, with the no-index-minus-one raising identity, zero-freeness of every mate, and rotation compatibility. | `lem:zero-free-bijection` | ✅ Full — `SkewClassInflation.zeroFree_class_transport`, `SkewClassInflation.Profile.profileSchur_inflate_one_of_negOneCount`, `SkewClassInflation.Profile.negOneCount_eq_of_profileSchur_eq`, `SkewClassInflation.Profile.deflate_rotate`, `SkewClassInflation.Profile.zeroFree_of_profileSchur_eq` |
| §3 Lem 3.5 | A proper legal chart whose outer is not a row and whose inflated board is zero-free has a legal period-\(q\) chart of the inflation in each of the three width alternatives: for \(0<w<q-1\) the inflated inner and mark with the same displacement and attachment, at \(w=0\) the inflated inner with its singleton end mark, and at \(w=q-1\) the atom decomposition \(\mathcal I(T)=\mathcal I(C)\circ_\varnothing\mathcal I(W)\) with \(\mathcal I(C)\) zero-free. | `lem:inflate-chart` | ✅ Full — `SkewClassInflation.InflateChart.inflate_chart` |
| §4 Lem 4.1 | No multipart ordinary right factor, and the complete actual overlap ribbon class is its two orientations. The signed-period obstruction avoids the full factor-classification input. | `lem:overlap-power-rigidity` | ✅ Full — `SkewClassInflation.OverlapWord.no_right_factor`, `SkewClassInflation.OverlapWord.reconstructible`, `SkewClassInflation.compositionProduct_blocks` |
| §4 Eq 4.1 | The displayed literal endpoint-merging word has exactly the bounded period translates of the actual original proper cuts. | `eq:overlap-cut-set` | ✅ Full — `SkewClassInflation.OverlapWord.properCuts_composition`, `SkewClassInflation.OverlapWord.cuts_bounds`, `SkewClassInflation.OverlapWord.composition_eq_periodic` |
| §4 Eq 4.2 | Initial zero interval is consumed by the exact finite cut obstruction. | `eq:initial-zero-interval` | ✅ Full — `SkewClassInflation.overlap_cut_obstruction` |
| §4 Eq 4.3 | Actual Bezout combination and gcd divisibility obstruction. | `eq:period-gcd` | ✅ Full — `SkewClassInflation.periodic_nat_gcd`, `SkewClassInflation.overlap_cut_obstruction` |
| §4 Eq 4.4 | Punctured invariance is completed and the internal word is forced empty. | `eq:cut-period-comparison` | ✅ Full — `SkewClassInflation.overlap_period_obstruction` |
| §4 Lem 4.2 | Every arbitrary connected mate of every power with at least two copies is the source or its rotation, with actual geometry and all reconstruction inputs supplied. | `lem:merged-block-rigidity` | ✅ Full — `SkewClassInflation.SaturationInner.power_mate_eq_or_rotate`, `SkewClassInflation.SaturationInner.power_full_class` |
| §5 Eq 5.1 | Full source row count, row weight, exact positive span increment, gap multiplicities, and signed maximal-generator coefficient, including zero internal gaps. | `eq:saturation-readings` | ✅ Full — `SkewClassInflation.SaturationInner.diagram_row_count`, `SkewClassInflation.SaturationInner.diagram_row_weight`, `SkewClassInflation.SaturationInner.diagram_span`, `SkewClassInflation.SaturationInner.spanIncrement_pos`, `SkewClassInflation.SaturationInner.diagram_small_gap_count`, `SkewClassInflation.SaturationInner.diagram_large_gap_count`, `SkewClassInflation.SaturationInner.diagram_maximal_derivative` |
| §5 Lem 5.1 | Actual coarsening multiplicities determine unordered endpoints; every arbitrary power mate inherits them, including a nonrigid one-copy inner. | `lem:ribbon-endpoints` | ✅ Full — `SkewClassInflation.ribbon_endpoints_of_eq`, `SkewClassInflation.SaturationInner.power_mate_endpoints` |
| §5 Lem 5.2 | Actual extreme coefficients and unrestricted power rigidity supply the full core; recursive positional splitting reconstructs the actual source in one global orientation with an outer-ribbon mate and the same part multiset. | `lem:total-contraction-inverse` | ✅ Full — `SkewClassInflation.SaturationInner.total_contraction_inverse`, `SkewClassInflation.SaturationInner.oriented_profile_reconstruction`, `SkewClassInflation.SaturationInner.merged_power_inverse_of_function`, `SkewClassInflation.distinguished_prefix_contraction` |
| §5 Eq 5.2 | Actual larger-seam constant coefficient and full connected factor matching, preserving multiplicities and row counts for arbitrary mates. | `eq:cut-components` | ✅ Full — `SkewClassInflation.distinguishedCutInventory_product`, `SkewClassInflation.SaturationInner.diagram_constant_coefficient`, `SkewClassInflation.SaturationInner.arbitrary_mate_component_matching` |
| §5 Eq 5.3 | Exact signed highest coefficient and actual total-contracted board function for every arbitrary source mate. | `eq:total-contraction` | ✅ Full — `SkewClassInflation.SaturationInner.diagram_highest_coefficient`, `SkewClassInflation.SaturationInner.arbitrary_mate_total_contraction` |
| §5 Eq 5.4 | Every actual proper outer prefix has one-based core length one plus its copy sum times the inner order; that exact position in the actual full source core is its literal merger row. | `eq:split-positions` | ✅ Full — `SkewClassInflation.SaturationInner.prefix_split_position`, `SkewClassInflation.SaturationInner.prefix_core_row_count`, `SkewClassInflation.SaturationInner.diagram_total_contraction` |
| §5 Eq 5.5 | Exact affine private index, signed constant-gap cofactor, and strict lower-index residual support. | `eq:private-saturation-corner` | ✅ Full — `SkewClassInflation.SaturationInner.power_corner_expansion`, `SkewClassInflation.SaturationInner.power_largest_label` |
| §5 Eq 5.6 | Actual ratio identity, injective localized substitution, and exact ribbon comparison within the full general source family. | `eq:saturation-substitution` | ✅ Full — `SkewClassInflation.SaturationInner.diagram_substitution`, `SkewClassInflation.SaturationInner.localizedSubstitution_injective`, `SkewClassInflation.SaturationInner.diagram_schur_eq_iff_ribbon` |
| §5 Eq 5.7 | Literal lower and upper marked cell intervals in the actual southwest-normalized original inner. | `eq:saturation-marks` | ✅ Full — `SkewClassInflation.SaturationInner.mem_lowerMark`, `SkewClassInflation.SaturationInner.mem_upperMark` |
| §5 Eq 5.8 | The actual east and north affine copy origins have exactly the displayed coordinates. | `eq:saturation-translations` | ✅ Full — `SkewClassInflation.SaturationInner.markedInner_origin_east`, `SkewClassInflation.SaturationInner.markedInner_origin_north` |
| §5 Rem 5.4 | Actual nonrotation one-copy and equal-gap equalities, strict-parent inequality, and both unrestricted strict-parent rotation classes are proved. | `rem:saturation-boundaries` | ✅ Full — `SkewClassInflation.ambiguous_inner_schur_eq`, `SkewClassInflation.ambiguous_inner_nonrotation`, `SkewClassInflation.ambiguous_equal_gap_schur_eq`, `SkewClassInflation.ambiguous_equal_gap_nonrotation`, `SkewClassInflation.ambiguous_parent_schur_ne`, `SkewClassInflation.ambiguous_parent_nonrotation`, `SkewClassInflation.ambiguous_zero_parent_full_class`, `SkewClassInflation.ambiguous_one_parent_full_class` |
| §5 Eq 5.9 | Both displayed actual constant-gap inners inhabit the separated domain and give a genuine nonrotation one-copy equality. | `eq:ambiguous-inners` | ✅ Full — `SkewClassInflation.ambiguous_inner_schur_eq`, `SkewClassInflation.ambiguous_inner_nonrotation` |
| §6 Eq 6.1 | Actual row count, total cell weight, full span, and signed maximal-generator coefficient. | `eq:thin-readings` | ✅ Full — `SkewClassInflation.ThinParameters.diagram_row_count`, `SkewClassInflation.ThinParameters.diagram_row_weight`, `SkewClassInflation.ThinParameters.diagram_largest_label`, `SkewClassInflation.ThinParameters.diagram_maximal_derivative` |
| §6 Lem 6.1 | Complete connected class, without fixing a mate row count in advance. | `lem:two-row-power-rigidity` | ✅ Full — `SkewClassInflation.ThinParameters.innerPower_full_class` |
| §6 Eq 6.2 | Private shortest-row coefficient and connected tail. | `eq:short-row-coefficient` | ✅ Full — `SkewClassInflation.ThinParameters.innerPower_shortest_coefficient` |
| §6 Eq 6.3 | Full arbitrary connected mate class. | `eq:thin-class` | ✅ Full — `SkewClassInflation.ThinParameters.thin_full_class` |
| §6 Eq 6.4 | The actual total-contracted thin mate loses exactly the common interior merger multiplicity, leaving both endpoints and the stated junction multiset, including one-copy and all-single-part boundaries. | `eq:orientation-multiset` | ✅ Full — `SkewClassInflation.ThinParameters.arbitrary_mate_orientation_residual`, `SkewClassInflation.ThinParameters.innerPower_orientation_residual` |
| §6 Eq 6.5 | Actual ribbon evaluation with an explicit algebraic section. | `eq:thin-substitution` | ✅ Full — `SkewClassInflation.ThinParameters.diagram_substitution`, `SkewClassInflation.ThinParameters.power_substitution_injective`, `SkewClassInflation.ribbonRows_schur` |
| §7 Lem 7.1 | Full class transport and the literal outer ribbon composition, with all actual geometric hypotheses I–V supplied. | `lem:subthreshold-transport` | ✅ Full — `SkewClassInflation.ThinParameters.diagram_negative_depth`, `SkewClassInflation.ThinParameters.subthreshold_full_class`, `SkewClassInflation.ThinParameters.subthreshold_literal_chart`, `SkewClassInflation.ThinParameters.diagram_compose_eq_inflation`, `SkewClassInflation.ribbonChain_eq_ribbonRows` |
| §7 Eq 7.1 | Exact retained-unit homogeneous polynomial substitution. | `eq:subthreshold-shift` | ✅ Full — `SkewClassInflation.profileSchur_inflate_eq_shiftHom` |
| §7 Eq 7.2 | Actual translated cell realization of the inflated inner. | `eq:inflation-inner-cells` | ✅ Full — `SkewClassInflation.ThinParameters.mem_innerCells`, `SkewClassInflation.ThinParameters.innerCells_connected` |
| §7 Eq 7.3 | Both actual marked placements and their full geometric legality. | `eq:inflation-marks` | ✅ Full — `SkewClassInflation.ThinParameters.mem_lowerMark`, `SkewClassInflation.ThinParameters.mem_upperMark`, `SkewClassInflation.ThinParameters.inflationMark_legal`, `SkewClassInflation.ThinParameters.inflationMark_hypothesisV` |
| §7 Eq 7.4 | Actual proper suffix set, size, bounds, and injectivity. | `eq:suffix-set` | ✅ Full — `SkewClassInflation.suffixSet_injective`, `SkewClassInflation.suffixSet_card` |
| §7 Lem 7.2 | Exact positive deletion sign, lowest surviving component and degree, and the actual connected zero-free Hessenberg core. | `lem:boundary-core` | ✅ Full — `SkewClassInflation.ThinParameters.boundary_core_lowest`, `SkewClassInflation.BoundaryParameters.restoredParent_deletionSign_one` |
| §7 Eq 7.5 | Actual retained upper and lower sets, with proved sorted coordinates. | `eq:boundary-core-lists` | ✅ Full — `SkewClassInflation.BoundaryParameters.core_rowSet`, `SkewClassInflation.BoundaryParameters.core_colSet`, `SkewClassInflation.ThinParameters.boundary_core_rows`, `SkewClassInflation.ThinParameters.boundary_core_cols` |
| §7 Eq 7.6 | Full uncanceled source beta sets. | `eq:thin-beta-lists` | ✅ Full — `SkewClassInflation.ThinParameters.diagram_rowSet`, `SkewClassInflation.ThinParameters.diagram_colSet` |
| §7 Eq 7.7 | Actual inflated full beta sets. | `eq:boundary-beta-lists` | ✅ Full — `SkewClassInflation.ThinParameters.boundary_rowSet`, `SkewClassInflation.ThinParameters.boundary_colSet` |
| §7 Eq 7.8 | Actual residue separation and suffix-grid exclusions. | `eq:boundary-residue-separation` | ✅ Full — `SkewClassInflation.BoundaryParameters.residue_separation`, `SkewClassInflation.BoundaryParameters.suffix_grid_not_upper` |
| §7 Eq 7.9 | Both literal full retained beta lists have the displayed order. | `eq:boundary-core-ordered` | ✅ Full — `SkewClassInflation.ThinParameters.boundary_core_rows`, `SkewClassInflation.ThinParameters.boundary_core_cols` |
| §7 Eq 7.10 | Exact core component and least occupied ordinary degree, with positive actual deletion sign. | `eq:boundary-lowest-degree` | ✅ Full — `SkewClassInflation.ThinParameters.boundary_lowest_component`, `SkewClassInflation.ThinParameters.boundary_least_ordinary_degree`, `SkewClassInflation.BoundaryParameters.restoredParent_deletionSign_one` |
| §7 Lem 7.3 | Private last-column support and full ordered upper-list recovery. | `lem:private-residue-column` | ✅ Full — `SkewClassInflation.BetaDiagram.private_residue_support`, `SkewClassInflation.BetaDiagram.row_list_eq_of_private_residues` |
| §7 Eq 7.11 | Standing residue-separation condition of the private-column theorem. | `eq:private-residue-condition` | — |
| §7 Eq 7.12 | Each proper suffix `k` is retained exactly when the generator indexed by `qk+p` occurs in the single boundary core; equal cores therefore recover every suffix set. | `eq:suffix-support-recovery` | ✅ Full — `SkewClassInflation.BoundaryParameters.core_support_iff_mem_suffix`, `SkewClassInflation.BoundaryParameters.core_suffix_set_injective` |
| §7 Rem 7.4 | A concrete skew-convexity witness excludes the specified marks at and above the exact threshold, independently of full-class rigidity. | `rem:chart-boundary` | ✅ Full — `SkewClassInflation.ThinParameters.upper_mark_removal_not_skew`, `SkewClassInflation.ThinParameters.inflationMark_legal_iff`, `SkewClassInflation.ThinParameters.superthreshold_full_class` |
| §8 Eq 8.1 | Both displayed ordered row and gap words are the actual constructed inflated profiles. | `eq:first-boundary-example` | ✅ Full — `SkewClassInflation.threshold_one_first_rows`, `SkewClassInflation.threshold_one_first_gaps`, `SkewClassInflation.threshold_one_second_rows`, `SkewClassInflation.threshold_one_second_gaps` |
| §9 Question 9.1 | Open problem; not asserted by the manuscript. | `prob:nonconstant-inners` | — |
| §9 Question 9.2 | Open problem; not asserted by the manuscript. | `prob:inflation-survivors` | — |

## Differences from the paper

| § | Item | Lean declaration | Module | Description |
|---|---|---|---|---|
| §1 | Thm 1.1 `thm:repeated-block-saturation` | `SkewClassInflation.SaturationInner.diagram_injective` | `SaturationColumnResidues` | Recovers proper suffix cuts from period-zero column betas rather than parsing the larger-gap word. |
| §1 | Eq 1.4 `eq:saturation-cardinality` | `SkewClassInflation.SaturationInner.full_class_of_palindrome` | `SaturationClassCounts` | The singleton total-power class and the unrestricted positional inverse eliminate the second parameter image, without first proving the literal reversal identity for every source. |
| §1 | Thm 1.2 `thm:sharp-inflation` | `SkewClassInflation.ribbonClass_eq_factorReversal` | `FactorGeneration` | The paper cites the classification of ribbon Schur equality by factor reversals; this tree reuses the copied proof of the companion and states the exact set equality for every positive weight. |
| §2 | Eq 2.14 `eq:constant-gap-substitution` | `SkewClassInflation.constant_gap_equality_iff` | `ConstantGapRibbons` | Lowering and no-opening reinflation prove faithfulness without passing to the localization at the gap generator. |
| §3 | Lem 3.4 `lem:zero-free-bijection` | `SkewClassInflation.zeroFree_class_transport` | `ZeroFreeTransport` | Surjectivity onto the class of the diagram is the one-sided no-escape theorem, and zero-freeness of the mates comes from the index zero count being a Schur invariant, in the same way as the index minus one count, rather than from ordinary-degree homogeneity. |
| §4 | Lem 4.1 `lem:overlap-power-rigidity` | `SkewClassInflation.OverlapWord.reconstructible` | `OverlapSignedPeriods` | The signed-period consequence of actual nonreconstructibility already contradicts the overlap's initial zeros and full period. The full factor-reversal classification is unnecessary for this input. |
| §4 | Lem 4.2 `lem:merged-block-rigidity` | `SkewClassInflation.SaturationInner.power_full_class_of_palindromic_inner` | `SaturationSymmetricPowers` | Reconstructs the symmetric source from exact two-part coarsening multiplicities, without a factor-classification input. |
| §5 | Lem 5.1 `lem:ribbon-endpoints` | `SkewClassInflation.ribbon_endpoints_of_eq` | `RibbonEndpoints` | Recovers endpoint incidences from the maximal and next-length coarsening partitions, without using factor-reversal classification. |
| §5 | Lem 5.2 `lem:total-contraction-inverse` | `SkewClassInflation.SaturationInner.oriented_profile_reconstruction` | `SaturationPositionalInverse` | Reconstructs the first actual component and the remaining literal core recursively; the paper splits all recovered positions at once. |
| §5 | Eq 5.6 `eq:saturation-substitution` | `SkewClassInflation.SaturationInner.localizedSubstitution_injective` | `SaturationLocalizedInjectivity` | Normalizes both seam generators to one and uses localization at the larger generator to compare with an injective triangular family, rather than working directly over the rational-function coefficient field. |
| §5 | Rem 5.4 `rem:saturation-boundaries` | `SkewClassInflation.ambiguous_parent_schur_ne` | `SaturationBoundaryExamples` | Uses the actual total-contraction functions and a specific coarsening multiplicity discrepancy, rather than full class rigidity. |
| §6 | Thm 6.2 `thm:two-row-thin-class` | `SkewClassInflation.ThinParameters.oriented_profile_reconstruction` | `ThinPositionalInverse` | Positional peeling uses the complete rigidity of the total power at each step instead of testing mixed block orientations. |
| §6 | Eq 6.5 `eq:thin-substitution` | `SkewClassInflation.ThinParameters.projection_innerPower` | `ThinPowerSection` | A residue specialization gives a left inverse on the power generators instead of the general triangular-substitution lemma. |
| §8 | Cor 8.1 `cor:unbounded-class-splitting` | `SkewClassInflation.unbounded_class_splitting` | `UnboundedSplitting` | The exact census of the binary family comes from unconditional factor transport and small-weight reconstruction of the weight-three factors (`binaryRibbon_census`), not from the full factor-reversal classification. |

## Dependencies

The build imports the shared `_lean_shared/` tree directly.  The copied local
`SkewJacobiNegative`, `SkewSchurReconstruction`, and `SkewGluing` modules supply
determinant, irreducibility, reconstruction, and marked-cell geometry inputs
from [2], [3], and [5].  The copied local `SkewRibbonCoarsenings` modules are the
Lean tree of [7], reproducing the factor-reversal classification of [6]; they are
used only by `SkewClassInflation.FactorGeneration` and retire into `_lean_shared`.

| Component | Used by | Description |
|---|---|---|
| `Shields.LinearAlgebra.Matrix.CauchyBinet` | `SkewJacobiNegative.Overlaps.ShiftedDeterminant` | The Cauchy--Binet formula and the discrete Andréief identity. Shared core mathematics reused by the skew-diagram formalizations [2,3,5]. |
| `Shields.LinearAlgebra.Matrix.DesnanotJacobi` | `SkewJacobiNegative.CornerMinors` | Desnanot--Jacobi condensation. Shared core mathematics reused by the skew-diagram formalizations [2,3,5]. |
| `Vendor.AlgebraicCombinatorics.DeterminantsBasic` | `SkewJacobiNegative.Base.MongeMinors`, `SkewJacobiNegative.WeightedReadings`, `SkewSchurReconstruction.MongeMinors` | Determinants: Basic Properties. Fabian Gloeckle and the Meta AlgebraicCombinatorics contributors’ formalization of Grinberg [4], upstream `b6022318e986a0c20764569208ba8ebbe1c04dbf`. |

## License

MIT; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. J. Shields, *Class recovery and inflation for repeated-block skew diagrams* (2026).
2. J. Shields, *Skew Schur equivalence by Jacobi–Trudi negative count* (2026).
3. J. Shields, *Boundary reconstruction and cofactor rigidity for skew Schur functions* (2026).
4. D. Grinberg, *An Introduction to Algebraic Combinatorics*, arXiv:2506.00738.
5. J. Shields, *Local common-factor gluing and reduction of composition necessity for skew Schur functions* (2026).
6. L. J. Billera, H. Thomas and S. van Willigenburg, *Decomposable compositions, symmetric quasisymmetric functions and equality of ribbon Schur functions*, Adv. Math. 204 (2006).
7. J. Shields, *Short coarsenings determine ribbon Schur equivalence* (2026). [doi:10.5281/zenodo.23644543](https://doi.org/10.5281/zenodo.23644543)

Refer to the paper for references.
