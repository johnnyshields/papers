# Lean 4 formalization — Skew Schur classes through thirty-three cells and composition necessity

Formalizes `shields-2026-skew-base-computational.tex` against Mathlib (`leanprover/lean4:v4.34.1`,
Mathlib `v4.34.1`, namespace `SkewBase`; a few modules are declared in namespace `SkewGluing`).
**There is no `sorry` and no project axiom anywhere in the tree**, and every result below reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.

The paper proves, with computer assistance, the necessity direction of the composition-and-reversal
conjecture of McNamara and van Willigenburg [1] for every connected skew diagram of at most 35 cells.
The computation rests on algorithms whose correctness the paper proves: a census that groups
diagrams by invariants and evaluations and returns exactly the Schur classes, two complete searches
for marked compositions (charts), and an induction on area that turns common keys into
factorizations.  The marked composition is that of [1] in the cell form of [3], and the row and
overlap invariants of Schur-equal diagrams are those of [2].  This tree formalizes those algorithm-level theorems.  It does not verify the
programs that run the census and the searches, and it does not reproduce their output.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

## Result coverage

**Work in progress.**  The main theorem of the paper rests on a computation, which this tree does
not reproduce.  A row marked **⚠️ Partial** or **❌ Missing** below reflects the state of the Lean
formalization, not of the paper's mathematics.

Every Lean name in this section and the next is pinned to the standard axiom footprint by a
`#guard_msgs` in `SkewBase/AxiomCheck.lean`, or reaches one that is.

| Where | Result | Paper | Status | Lean |
|---|---|---|---|---|
| §2 | A diagram Schur-equal to a connected `F` has the same row overlap partitions `ρ^{(k)}` for every `k ≥ 1` (Reiner–Shaw–van Willigenburg, Cor. 8.11), the same row lengths and gaps, the same area, and is connected; rotation does not change `s_F` | `lem:invariants` | ✅ Full | For a diagram `H` given as a cell set with `s_H = s_F` (`HasSchur`), `isConnectedSkew_of_hasSchur_eq` gives `IsConnectedSkew H`, `H.card = ∑ F.r`, `rowLengths H = F.rowMultiset`, `gapMultiset H = F.gapMultiset`, and `overlapPartition H k = F.toBetaRows.rowOverlaps k` for every `k ≥ 1`.  Every skew cell set has a presentation (`exists_hasSchur_of_isSkew`).  Behind it: `BetaRows.rowOverlaps_eq_of_schur_eq`, `Profile.rowOverlapPartition_eq_of_schur_eq`, `BetaRows.connected_of_schur_eq`, `BetaRows.area_eq_of_schur_eq_profile`, `BetaRows.overlapPartition_cells`, `BetaRows.isSkew_cells`, `BetaRows.isEdgeConnected_cells`; `Profile.schur_rotate`, `AnyProfile.shard_invariant_eq`, with `reinerRowInvariants` for rows and gaps.  Connectedness is shown through the row overlap partitions `ρ^{(1)}`, `ρ^{(2)}` and a translation to cell sets, not through the factorization over components and the irreducibility of connected `s_F` |
| §2 | A connected diagram is determined up to translation by its profile `(r; g)`, every profile occurs, and the two maps are inverse; `r_i` is the length of row `i` and `g_i + 1` the number of columns shared by rows `i` and `i + 1`; row `i` occupies the contents `y_i, …, x_i - 1` and `N_F = x_1 = ∑ r_i - ∑ g_i`; rotation reverses both sequences; the Jacobi–Trudi determinant of a profile, and its evaluation at a point of any commutative ring | `lem:profiles`, `eq:jt` | ✅ Full | The diagram of a profile `P` is the cell set `P.toBetaRows.cells`, and `HasProfile D P` says that `D` is a translate of it.  `profileEquiv` is a bijection from the connected skew cell sets up to translation (`ConnectedDiagramClass`) to profiles `Σ n, Profile n`; behind it `isConnectedSkew_cells_profile` (every profile gives a connected diagram), `exists_hasProfile` (every connected cell set has a profile), `hasProfile_unique` and `eq_translate_of_hasProfile` (the profile determines the diagram, and conversely), with `profileOf`.  The profile is read off the cells: `HasProfile.sharedColumns_one` and `HasProfile.sharedColumns_two` give `r_k` and `g_k + 1` as the length of row `k` and the number of columns shared by rows `k`, `k + 1`; `mem_cells_profile_iff_content`, `contents_cells_profile` and `HasProfile.span_eq` give the contents of row `i`, the contents `0, …, x_1 - 1` and `N_F = x_1 = ∑ r_i - ∑ g_i`; `HasProfile.rotated` gives the profile `Profile.rotate` of a rotated diagram.  The determinant is `Profile.schur`, with `schurZ`, `evalAt`, `evalAt_schurZ`, `map_schurZ`, `schurZ_eq_iff` over `ℤ`, and `Profile.schur_rotate`.  Rows come from the presentation of a skew cell set by beta lists; the crossing of a chain of cells from row `i` to row `i + 1` by a vertical step (`exists_shared_column_of_reach`) gives consecutive rows and shared columns |
| §2 | The skew Schur function of a connected cell set does not depend on the beta lists presenting it: a connected `H` has the skew Schur function `f` exactly when `f` is the Jacobi–Trudi determinant of its profile | `lem:profiles`, `eq:jt` | ✅ Full | `hasSchur_iff_of_hasProfile`, `hasSchur_eq_of_hasProfile`, `hasSchur_unique`, `hasSchur_iff_eq_schurOf` with `schurOf`.  A presentation may carry empty rows above and below the nonempty ones (`BetaRows.beta_of_cells_eq` gives their position and the beta lists on the nonempty rows up to one shift); an empty first or last row is removed from the determinant by `betaDet_first_empty`, `betaDet_last_empty`, `betaDet_pad`.  Stated for connected `H`; for a disconnected skew cell set `exists_hasSchur_of_isSkew` gives a presentation and no uniqueness is claimed |
| §3 | The census returns exactly the Schur classes: abstractly, given that equal polynomials have equal shard and invariant; unconditionally for connected diagrams given by profiles, with the invariant `I` the sequence of all row overlap partitions | `thm:census` | ✅ Full | `census_eq`, `census_eq_schurClasses`.  The enumeration of profiles and the finite-field arithmetic are not modeled; the identification of connected diagrams with profiles is the row `lem:profiles` |
| §5 | Span of a composite, `N_F = N_D q + w`, `w = N_F mod q`, `N_E = q + w` | `lem:copies` (iii) | ✅ Full | `span_compose_eq`, `width_eq_span_mod`, `span_inner_eq` |
| §5 | Contents occupied by a copy and by a supplemental copy; the origins of the copies on one content of the outer form an interval of `h_D(t)` consecutive integers, `[0, h_D(t) - 1]` in case (c) and `[1 - h_D(t), 0]` in case (d) | `lem:copies` (i), (ii) | ✅ Full | `contents_copy`, `content_mem_copy`, `content_mem_supplemental`, `origin_mem_iff`, `origin_mem_iff_c`, `origin_mem_iff_d`.  Stated with the least content of the inner equal to `0` |
| §5 | Bottom and top bands are the copies of the cells `d₀`, `d₁`; on a private content the cells of `F` are a run of `h_D(t) + h_E(w') - 1` cells with least row `a_E(w') + κ_t` | `lem:bands` | ✅ Full | `mem_compose_lower_iff`, `mem_compose_upper_iff`, `mem_compose_private_iff`, `diagLo_private`, `diagHi_private`, `height_private`.  Stated for an outer with `sw D = (0, 0)` and an inner with least content `0` |
| §5 | Heights `h_D(t) = h_F(tq + w') - h_F(w') + 1` and offsets `κ_t - κ_0` read off `F`, independent of `w'`; the outer in cases (a) and (b) is determined by `F` and the marked inner | `cor:outer`, `eq:private` | ✅ Full | `private_height_eq`, `private_row_eq`, `privateHeightsAgree_compose`, `privateRowsAgree_compose`, `eq_corOuterA`, `eq_corOuterB` |
| §5 | Every connected skew diagram with prescribed heights arises from the recursion on contents | `lem:heights` | ✅ Full | `heightRecursion_of_isConnectedSkew`, `eq_diagramOfRows` |
| §5 | `\|F\| ≥ q\|D\| + w`, `q ≥ 2`, `\|D\| ≤ \|F\|/2`, `\|D\| ≤ 17` for `\|F\| ≤ 35` | `lem:size` | ✅ Full | `card_compose_ge`, `size_of_proper`, `two_le_period`, `two_mul_card_outer_le`, `card_outer_le_seventeen` |
| §5 | `3\|E\| ≤ 2\|F\| - 1`, `\|E\| ≤ 23` for `\|F\| ≤ 35` | `lem:inner-size` | ✅ Full | `inner_size_of_two_le_span`, `inner_size`, `card_inner_le_23` |
| §5 | The forward generation returns exactly the proper charts of the connected diagrams of at most `n` cells | `thm:searches`, last sentence | ✅ Full | `mem_forwardGeneration_iff`, `mem_forwardGeneration_of_isChartOf` |
| §5 | Searches S and B return exactly the proper charts of `F`: every returned chart is a proper chart of `F` with composite `F`, and every proper chart of `F` is returned, in normalized position (`sw D = sw E = (0, 0)`), and up to translation otherwise | `thm:searches` | ✅ Full | `searchS_eq`, `searchB_eq` (`SearchS F` and `SearchB F` equal `NormalizedProperCharts F`), `searchS_sound`, `searchB_sound`, `searchS_complete`, `searchB_complete`, `exists_searchS_of_isChartOf`, `exists_searchB_of_isChartOf`.  The searches are the sets of charts defined by the conditions of `def:searches`; the enumeration programs are not modeled |
| §6 | If the key sets `K(X)` and `K(Y)` of minimal charts meet for every connected `X` of at most `n` cells and every Schur-equal `Y` that is not a rotation mate, then necessity holds for those diagrams, by induction on area | `prop:induction` | ✅ Full | `necessityUpTo_of_commonKeysUpTo`; the induction itself, from common final factors, is `necessityUpTo_of_commonFinalFactorsUpTo`, and `hasCommonFinalFactor_of_common_key` derives a common final factor from a common key.  The ordinary-gauge identification is not used: the proposition does not need it |

## Structural coverage

| Where | Item | Paper | Lean |
|---|---|---|---|
| §2 | Profile and beta lists `x_i`, `y_i` | `lem:profiles` | `Profile`, `Profile.xi`, `Profile.zeta`, `Profile.rotate` |
| §2 | A cell set with a given profile; the profile of a connected cell set; the translation classes of connected cell sets | `lem:profiles` | `HasProfile`, `profileOf`, `translationSetoid`, `ConnectedDiagramClass`, `profileEquiv` |
| §2 | Skew diagrams with possibly empty rows by their beta lists; the diagram `D̂` with the top cell of every column removed; the numbers of columns shared by `k` consecutive rows and the row overlap partition `ρ^{(k)}` | `lem:invariants` | `BetaRows`, `BetaRows.hat`, `BetaRows.overlap`, `BetaRows.overlaps`, `BetaRows.rowOverlaps`, `BetaRows.overlap_eq_ncard`, `Profile.toBetaRows`, `Profile.rowOverlapPartition` |
| §2 | A skew diagram as a cell set, by its beta lists: `s_H` of a cell set through a presentation; the row lengths, gaps and `ρ^{(k)}` counted on cells | `lem:invariants` | `BetaRows.cells`, `HasSchur`, `presentation`, `columnsOfRow`, `sharedColumns`, `overlapPartition`, `rowLengths`, `gapMultiset` |
| §2 | The shifted Jacobi–Trudi determinant `∑_m X^m h_{a-m}`: its degree and its leading coefficient `s_{D̂}` | `lem:invariants` | `shiftHom`, `shiftEntry`, `shifted_coeff`, `BetaRows.shiftHom_schur_natDegree`, `BetaRows.schur_hat_eq_of_schur_eq` |
| §3 | The census, one shard at a time | `def:census` | `census`, `censusOf`, `classesBy`, `refineBy` |
| §4 | Legal marks: Hypotheses I–IV | `sec:composition` | `MarkedInner`, `MarkedInner.IsLegal` |
| §4 | Copy origins `L(d)` and the composition `D ∘_ω E` | `eq:offsets` | `MarkedInner.origin`, `MarkedInner.compose` |
| §4 | Charts, proper charts, a chart of `F` | `sec:composition` | `Chart`, `Chart.IsProperLegal`, `Chart.IsChartOf` |
| §4 | Iterated composition, factors reversed with their marks | `eq:tower`, `conj:mvw` | `Presentation`, `Presentation.Corresponds` |
| §5 | Forward generation with bound `n` | `def:searches` | `ForwardGeneration` |
| §5 | Search S and search B | `def:searches` | `SearchS`, `SearchB`, `SearchBAt` |
| §5 | Heights and offsets of `eq:private`, their independence of `w'`; the outer of `cor:outer`; the copies pruning of cases (c), (d) | `eq:private`, `cor:outer` | `privateHeight`, `privateRow`, `PrivateHeightsAgree`, `PrivateRowsAgree`, `corOuterA`, `corOuterB`, `CopiesInF` |
| §5 | The inner of search B from the bottom and top bands of `F` | `def:searches` | `bottomBand`, `topBand`, `bandInner`, `BandsAgree` |
| §5 | The recursion of `lem:heights` and the diagram of prescribed diagonals; the outers generated by search S | `lem:heights`, `def:searches` | `HeightRecursion`, `diagramOfRows`, `heightCandidates` |
| §5 | The proper charts of `F` in normalized position | `thm:searches` | `NormalizedProperCharts`, `exists_normalized_chart` |
| §5 | Cost `(N_W, N_E)` of a chart, equal to `(N_F mod q, q + N_F mod q)`; minimal charts | `sec:keys` | `Chart.cost`, `Chart.cost_eq`, `Chart.IsMinimalOf` |
| §6 | Key of a chart (marked inner up to translation and rotation, with `s D`) and the key set `K(F)` | `def:key` | `MarkedInner.orbit`, `MarkedInner.orbit_eq_iff`, `Chart.key`, `keySet` |
| §6 | Necessity up to `n` cells | `prop:induction` | `NecessityUpTo`, `CommonKeysUpTo`, `CommonFinalFactorsUpTo` |
| §5 | A chart meeting the hypotheses of the size bounds | `lem:size`, `lem:inner-size` | `figureChart_isProperLegal` |

## Differences from the paper

Searches S and B are formalized as sets of charts, `SearchS F` and `SearchB F`, defined by the
conditions of `def:searches`: the subdiagram `S ⊆ F` and the legal mark in S, the integer `q`, the
bands and the legal mark in B, and the outer generated by `lem:heights` or taken from `cor:outer`.
The data of a chart are an outer `D` and a marked inner `ω`, and `F` is a connected skew diagram
with `sw F = (0, 0)`, the position in which the paper reads the contents of `F` from `0`.  The
returned charts are in normalized position, `sw D = sw E = (0, 0)`; for a proper chart of any
translate of `F`, `exists_searchS_of_isChartOf` and `exists_searchB_of_isChartOf` give the returned
chart obtained by translating the outer and the inner.  The finite enumeration, its cost, and the
program that implements it are not modeled; the theorem is the equality of the set `SearchS F`
(respectively `SearchB F`) with the proper charts of `F`.

The outer function in `prop:induction` and in the keys is an arbitrary `s : Diagram → R`; the paper takes `s_D`.  Minimal charts are ordered by cost lexicographically, as in the paper.  The key set is defined for any `s`, and the induction uses only that a common key is a pair of proper legal charts with equal outer value; minimality is not used in the proof.
A skew diagram with possibly empty rows is the pair of its strictly decreasing beta lists
`ξ_i = λ_i - i`, `ζ_i = μ_i - i` with `ζ_i ≤ ξ_i` (`BetaRows`); row `i` is the column interval
`[ζ_i + i, ξ_i + i)`.  The row overlap partition `ρ^{(k)}` of the invariant `I` lists the numbers
of columns shared by `k` consecutive rows; zero parts are kept in `Profile.rowOverlapPartition`
and dropped in `BetaRows.rowOverlaps`, and the two carry the same information for Schur-equal
diagrams, which have the same number of rows.  The proof that `s_D` determines every `ρ^{(k)}`
follows Reiner–Shaw–van Willigenburg, Cor. 8.11, by induction on the number of rows, but extracts
`s_{D̂}` from the leading coefficient of the image of `s_D` under the ring homomorphism
`h_a ↦ ∑_{m ≤ a} X^m h_{a-m}`, computed by Cauchy–Binet, in place of the coefficient of
`h_{ℓ+c}` in the Littlewood–Richardson expansion and the bijection of pictures.

Connectedness in `lem:invariants` is proved for cell-set diagrams (`IsConnectedSkew`) by a bridge
from the beta-list form, not by the route of the paper.  A cell-set diagram `H` has the skew Schur
function `f` (`HasSchur H f`) when `H` is a translate of the cells of a diagram `B` given by beta
lists with `s_B = f`; `isConnectedSkew_of_hasSchur_eq` holds for every such presentation, and
`exists_hasSchur_of_isSkew` shows that every skew cell set has one.  The independence of `s_H`
from the presentation is not used for this lemma; for connected `H` it is proved separately, as
`hasSchur_unique`.  The row overlap partitions of `B` determine that the nonempty
rows are consecutive and that adjacent rows share a column, which is connectedness of the cell
set, and the same partitions counted on cells are `rowLengths`, `gapMultiset` and
`overlapPartition`.  The paper obtains connectedness from the factorization of `s_H` over its
components and the irreducibility of the skew Schur function of a connected diagram; neither is
used, and `BarekatIrreducibility` is not needed for this lemma.

The census is stated over any finite rotation-closed set of diagrams and any choice `canon x ∈ {x, x*}`
of orbit representative, not only the lexicographically smaller.  The polynomial ring is
`ℤ[h₁, h₂, …]` for the census and evaluations, and `ℚ[h₁, h₂, …]` in the invariants; `schurZ_eq_iff`
identifies equality in the two.

## Dependencies

Mathlib at `v4.34.1`, and one module of the shared library `_lean_shared/Shields`, which sits
at `../../_lean_shared`:

| Module | Used for |
|---|---|
| `Shields.LinearAlgebra.Matrix.CauchyBinet` | The Cauchy–Binet expansion of the shifted Jacobi–Trudi determinant |

## License

Code is made available under the MIT license (see `LICENSE.txt`).  This directory is also subject
to the patent and trademark terms in the `LICENSE.txt` at the root of the repository.

## References

1. P. R. W. McNamara and S. van Willigenburg, *Towards a combinatorial classification of skew Schur
   functions*, Trans. Amer. Math. Soc. 361 (2009), 4437–4470.
2. V. Reiner, K. M. Shaw and S. van Willigenburg, *Coincidences among skew Schur functions*, Adv. Math.
   216 (2007), 118–152.
3. J. Shields, *Local common-factor gluing and reduction of composition necessity for skew Schur
   functions*, preprint, 2026.

Refer to the paper for references.
