# Computational supplement — Recognition of ribbon-outer skew Schur compositions

Cross-check scripts for `shields-2026-skew-ribbon-recognition.tex` build skew diagrams, their legal marks and compositions, their beta lists and their Jacobi–Trudi matrices from cell lists, and compare the finite statements of the paper against exact determinants, cofactors and adjugates over integer or generic letters.  Each sweep enumerates every connected diagram, legal mark or coequal pair up to a stated size and fails with an `AssertionError` on the first counterexample.

The paper proves that two minimal ribbon-outer factorizations with the same skew Schur function are equivalent.  These checks exercise the chart and mark combinatorics, the finite determinant identities, flag lists and support facts its comparison and endpoint arguments consume, on bounded instances; they do not check the recognition theorem itself.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.10 or later.  Install the pinned dependencies and run the harness:

```sh
python3 -m pip install -r requirements.txt
bash run_all.sh
```

## Scripts by section

| Where | Script | Paper section | Content |
|---|---|---|---|
| §1 eq. (1.1), … §5 Prop 5.2 | `verify_charts.py` | `sec:charts`, `eq:intro-span`, `lem:diagonal-reconstruction`, `prop:local-data`, `prop:gluing-inputs`, `ex:gauge`, `lem:strict-area`, `ge:remark:same-mark` | Diagonal characterization of connected skew diagrams against diagrams generated from pairs of partitions; the span law of every legal mark and composition; the middle content interval, thin diagonals and end diagonals of a positive-width mark; at most two marks per inner and width, a double being the two ordinary gauges; the worked gauge example; equal outer functions through one mark |
| §3 Prop 3.2 | `check_landing_data_satisfiable.py` | `rt:lower-landing` | The landing data is satisfiable: a coequal non-translate pair of span 3 and a source-minimal empty-mark inner; the smallest witness is identified |

| §4 Lem 4.1 | `verify_upper_mate.py` | `sec:comparison`, `ph:activation` | The open mate implications on every legal positive upper mark of every connected diagram and of every composition source, all four attachment types |
| §4 Lem 4.2 | `check_source_chart_support.py` | `ph:source-chart`, `ph:ordinary-source-chart`, `ph:mixed-source-chart` | The outside exponents of the returned charts are distinct, lie between the finer span and the source span, and miss the returned exponents |
| §4 Lem 4.2 | `check_mixed_baseline_det.py` | `ph:mixed-flags`, `ph:mixed-baseline-det` | On every legal mixed mark of a small finer, the native row list of the source, the square baseline and its determinant `±Â^{M+1} C_priv^M` |
| §4 Lem 4.2, §4 Prop 4.3 | `check_row_mark_mixed_words.py` | `ph:mixed-flags`, `ph:source-chart`, `ph:finite-block`, `ph:rectangular-splice` | Horizontal row marks are those with single-row end windows; the periodicity of the closed words of a mixed finer and their one-count balance; the keyed crossing regrouping on random arrays |
| §4 Lem 4.2 | `check_mixed_one_period_coframe.py` | `ph:mixed-flags`, `ph:mixed-native` | The one-period coframe reading on sampled flag configurations of the mixed shape |
| §4 Lem 4.2 | `check_mixed_coframe_legal_marks.py` | `ph:mixed-flags`, `ph:mixed-native` | The same reading on the flags of every legal case (d) mark of a small finer |
| §4 Lem 4.2 | `check_low_row_response.py` | `ph:mixed-flags` | The one-period response at a low mark row of a mixed finer, and where the top letter enters it |
| §4 Prop 4.3 | `check_neutral_returns.py` | `ph:finite-block` | The raised fixed rows of the grade-zero ordinary chart: the raise hypothesis on every landing, and the returned monomial meeting a raised row |
| §4 Prop 4.3 | `check_coarse_adjugate_weight.py` | `ph:finite-block`, `ph:one`, `ph:two` | Every keyed adjugate entry of a small coarse diagram is weighted homogeneous of weight `|V| - (j - k)`, so the prefix sums separate by coarse weight |
| §4 Prop 4.3 | `check_live_crossing.py` | `ph:finite-block`, `ph:ordinary-source-chart`, `ph:effective-current` | The live crossing on the actual ordinary composition chart |
| §2 Lem 2.7, §A Lem A.1 | `verify_transports.py` | `rt:transports`, `lem:strict-area` | Antitransposition of marks and sources, and of the empty-mark composites; both factors of a proper composition have strictly smaller area |
| §5 Lem 5.1 | `verify_aligned_finish.py` | `sec:children`, `ge:aligned-finish` | The aligned lift `V ∘_μ J = (γ(V) ∘_λ A_J) ∘_κ K` with one `(λ, γ)` for all outers, `γ = id` unless `λ` is empty |
| §6 Thm 6.3 | `verify_two_window.py` | `sec:boundary`, `ge:two-window` | Instances of the hypotheses assembled backwards from the cut identities with a common ordinary inner of S and T; on those meeting the coverage bounds, `d = f` divides `L` and `D` |
| §6 Lem 6.1, §6 Lem 6.2 | `verify_reflection.py` | `sec:boundary`, `ge:zero-port`, `ge:ordinary-reflection` | The reflected native words force `s + t = v` and a self-rotational full mark; crossed windows exist only on self-rotational ordinary marks and never on mixed marks |
| §6 Lem 6.4 | `verify_literal_mixed.py` | `sec:boundary`, `ge:literal-mixed` | The closed-word hypotheses on a composition through a type (d) mark give a proper factor of period `gcd(r, L)`, `2 ≤ d < r`, `d ∤ v` |
| §6 Lem 6.6 | `verify_signed_cap.py` | `sec:boundary`, `ge:signed-cap` | Every pair of capped, periodic-away-from-phase binary words with a unit comparison error: the stated error positions, equal filled native words, zero or one ports, and the congruent-phase case |
| §6 Lem 6.7, §6 Prop 6.8 | `verify_signed_windows.py` | `sec:boundary`, `ge:crossed-cover`, `ge:carried-signed` | Instances of the signed comparisons assembled from compositions (carried and crossed marks): the crossed full mark is carried or the children are half-turns of each other, and for distinct carried children the inner period divides `L` or `D` |
| §6 Thm 6.9 | `verify_terminal_signed.py` | `sec:boundary`, `ge:terminal-signed` | Terminal signed cuts built from an ordinary finer with the whole-child equality: the finer is self-rotational; instances without the equality as a control |
| §6 Prop 6.5, §A Cor A.6 | `verify_zero_matrix.py` | `sec:boundary`, `app:boundary`, `ge:zero-second-response`, `ge:zero-matrix-finish` | On the native signatures of `ph:zero-matrix`, search actual legal compositions for a proper chart of period `g = gcd(r, δ)` and width `v mod g`; exceptional column classes retain their actual occupancies |
| §7 Lem 7.1, §A Lem A.5 | `verify_empty_cycles.py` | `sec:completion`, `app:boundary`, `rt:empty-cycles`, `ge:primitive-cycle` | The empty-overlap residue condition gives a self-reflecting inner at gcd one and a period-g empty chart otherwise; the ordinary no-eligible implications at gcd one give a self-rotational full mark |
| §A Lem A.7 | `verify_rectangle_words.py` | `ge:rectangle` | Every connected diagram meeting the closed-word hypotheses for some period is a rectangle composition through an ordinary or empty inner of that period and width |
| §A Lem A.3, Lem A.4 | `verify_wide_upper.py` | `app:boundary`, `rt:wide`, `rt:boundary` | A wide or equal-width upper mark on a composition gives a smaller-score chart of period `gcd(r, Q)` or a line finer, and the equal-width case excludes mixed finers |

| §A Prop A.8 | `verify_endpoint_consumer.py` | `sec:boundary`, `ge:endpoint-splice` | With the equality of the two splices, the ordinary endpoint finer is self-rotational or has a proper chart of smaller score |

| §B Lem B.1 | `check_two_copy_flags.py` | `app:physical`, `ph:rectangular-splice` | The flag lists of the two-copy diagram `Row_2 ∘ E` of every legal row mark of a small diagram |
| §B Lem B.1 | `verify_rectangular_splice.py` | `app:physical`, `ph:rectangular-splice` | The splice sum for the Schur function of the two-copy row composition, the substitution `h_i → h_i + z h_{i-r}` on the cofactors, and the coefficient formula, at exact integer letters |
| §B Lem B.2, §B Lem B.3 | `verify_mark_determinants.py` | `app:physical`, `ph:ordinary-activation`, `ph:mixed-compound` | Ordinary activation with the signed contact cofactor, its full-hat interpretation, and the mixed compound identity with its unsigned minor; both contact signs and a top-letter-dependent minor are exercised, with a symbolic activation example and an independent determinant-variation current |
| §B Lem B.4 | `check_first_grade.py` | `ph:first-grade` | Every ordered coequal pair of spans 3 to 6: at the first nonzero grade of the absolute adjugate difference, a distance `d` with the extreme boundaries, their vanishing beyond `d`, and the prefix sums `C_{1,d} = C_{M-d,d} ≠ 0` |
| §B Lem B.4 | `check_core_facts.py` | `ph:first-grade` | Every connected diagram of span 3 to 9: its zero-free core is connected of the same span, and the proper corner and both replaced boards are feasible; the feasibility criterion against the determinant |
| §C Lem C.1 | `check_all_j.py` | `app:first-responses`, `ph:all-J` | The same coequal pairs: some `J_a`, `2 ≤ a < M`, is not divisible by the whole polynomial, and a nonzero `J_a` is never divisible by it |
| §D Lem D.1 | `check_mark_child_equality.py` | `app:cofaces`, `ph:coface-data`, `ph:CF0` | Equal connected children through mark factors: the cleared mixed comparison forces equal children and constant one |
| §D Lem D.1 | `check_mixed_normalization.py` | `ph:coface-data` | The mixed normalization on every legal case (d) flag set of a small finer: the coframe coefficients, the constant η read two ways, and the block lists |
| §D Lem D.3, §E Lem E.4 | `check_ordinary_high_square.py` | `app:cofaces`, `ph:ordinary-two-copy`, `app:endpoints`, `ph:active-dichotomy` | The flag lists of the two-copy diagram of an ordinary mark and the block triangularity of its fixed matrix; the threshold `r` splits the proper corner of an ordinary finer into a square high piece |
| §D Lem D.6 | `verify_zero_matrix.py` | `app:cofaces`, `ph:zero-matrix` | Under full row closure and foreign-class column closure by `δ` modulo `r`, the complete row classes, distinct ports with occupancies summing to `m`, and `|T| = |R| - 1`; the normalized proposed short-width root directly factors the source with its literal overlap, type, contacts, and legal period and width |
| §D Lem D.5 | `check_mixed_low_row_cofactor.py` | `ph:mixed-native` | The first-order response at a low native row is a two-period cofactor, nonzero on every native row checked |
| §E Lem E.1 | `verify_pinches.py` | `app:endpoints`, `ph:pinches` | The contact and height pinches `s > w`, `t < δ`, `h_W(w) = h_W(δ-1) = 1` on every positive upper mark of an ordinary or mixed finer source |
| §E Lem E.2 | `verify_endpoint_splice.py` | `app:endpoints`, `ph:endpoint-splice` | The restrictions `B`, `D` and the splices `S`, `T` are connected with the stated flags and shared words, the endpoint area law, and the strict area drop below the source |
| §E Lem E.3 | `verify_mixed_upper_sign.py` | `app:endpoints`, `ph:mixed-upper-sign` | Closed upper recurrences and the exact cofactor-parity formulas on abstract flag words, retaining shared-label units; conditional contact inequalities under the signed cofactor subgate, with gate counts distinguished from non-vacuous parity checks |
| §E Lem E.5 | `verify_structured_dual.py` | `app:endpoints`, `ph:structured-dual` | The global contraction of the antitransposed source against the involution image of the source, positive width and empty upper, at exact rational letters |
| §E Lem E.7 | `verify_principal_star.py` | `app:endpoints`, `rt:principal-star` | Among coequal coarse pairs on one ordinary mark with equal source function, equal global contractions occur exactly for the half-turn pair (no non-rotation coequal pair occurs in the range) |
| §E Lem E.6 | `verify_endpoint_product.py` | `app:endpoints`, `rt:endpoint-product` | Irreducibility of the end polynomials, and `(N, L_D R_D)` determining the pair `{D, D*}` |
| §3 Lem 3.1 | `check_domino_probe.py` | `sec:reduction`, `rt:domino-probe` | The `p_2`-coefficient `γ = p χ_Q(m) + (θ/2) χ_Q(m-2,2)` of the degree-two element read from ribbon characters, its sign values and nonvanishing on `|θ| < p`, with the zero at `|θ| ≥ p` as control; the row-two domino area `2|E| - |W|` |
| §3 Prop 3.3 | `check_preprocessing_scores.py` | `sec:reduction`, `rt:preprocessing`, `rt:finer-parameters` | The aligned-case score comparison `(v, r+v) < (w, Q+w)` on a parameter box and on actual marks, and the `N_E = Mr + v` identity; the control `w < v` where the score is not lower |
| §6 Prop 6.10 | `check_ordinary_amplified.py` | `sec:boundary`, `ge:ordinary-amplified` | The full area law of an ordinary composition with the hatted sets, the positive area drop of the row-two parent for nonline outers, the EMPTY area bounds, and the two-copy lists of `Z` |
| §A Prop A.9 | `check_high_head.py` | `app:boundary`, `ge:high-head` | The inequality chain derived from the head hypotheses on every case (d) parameter set: `A ≥ δ ≥ g`, `r ≥ 2g`, `H > 2g`, and the coverage inequalities for `H > r` |
| §A Lem A.2 | `check_line_finer.py` | `app:boundary`, `rt:line-finer`, `rt:line-companion`, `rt:tail-product` | Flags of a composition through a line finer, the companion identity `s_E^2 = h_w s_{F_R} + s_{F_C}`, the grouped cofactor decks `C_q`, `D_q` against derivatives and Euler identities, `c = [f_M]e`, `gcd(e, c) = 1`, and the Dodgson tail product |
| §4 Prop 4.4, §4 Prop 4.5, §C Lem C.2, §C Lem C.3, §C Lem C.4 | `check_coframes.py` | `app:first-responses`, `ph:first-response`, `ph:stationary-packet`, `ph:gradient`, `ph:matrix-powers`, `ph:intercept-exclusion` | Coframes of every connected board of span 2 to 5: the neutral adjugate `κ G_k C_{M-j}`, the support of `D = T_{G,C}(H)`, the finite multiplication and shift-cap formulas, the cutoff family `J_a` with `J_1 = J_M = 0` and `Ĵ_a = J_{a+1}`, and the crossed assignment on coequal pairs |
| §4 Cor 4.6, §D Lem D.4 | `check_two_copy_equation.py` | `app:cofaces`, `ph:two-copy-equation`, `ph:vanishing`, `ph:CF0` | The flags of `Row_2 ∘ J` for a case (d) mark, the cut words of the private-pair children with their closed row and column defects, and the weight inequalities of the vanishing corollary |
| §D Lem D.2 | `check_transpose.py` | `app:cofaces`, `ph:transpose` | The antitransposed flags and the relations `G† = I(P)`, `P† = I(G)`, `C† = I(Q)`, `Q† = I(C)` coefficientwise at exact rational letters |
| §D Lem D.7 | `check_ordinary_zero.py` | `app:cofaces`, `ph:ordinary-zero` | The native closure conditions as predicates on real marks and empty finers: satisfying and violating cases, with each step orbit staying in `I` until reaching zero or repeating; a closed nonzero cycle is checked explicitly |
| §E Lem E.8 | `check_self_inner.py` | `app:endpoints`, `rt:self-inner` | Every narrow upper over a self-reflecting inner is ordinary, with the non-reflecting inners as control; the symmetric native matrix at an empty finer |
| §F Lem F.1 | `check_mixed_empty.py` | `app:mixed-empty`, `rt:mixed-empty`, `rt:empty-junction` | On compositions through a type (d) mark: the two-junction identity, the flags of the empty row parent, the splice sum, and the pencil coefficient formula |
| §4 Prop 4.4, §D Lem D.7 | `check_first_matrix.py` | `sec:comparison`, `ph:ordinary-flags`, `ph:finite-block`, `ph:first-response`, `ph:ordinary-zero` | Exact directional Jacobian of the complete first response in its own normalized chart, checked symbolically at generic and zero-valued moving elimination multipliers; mark/cofactor normalization, the unfixed zero-column coefficient, and native closure retaining the returned row; mate-free diagnostics do not assert the full-comparison implication |

A failed identity raises `AssertionError`; a successful harness ends with `ALL PASS`.

## Coverage by section

**Work in progress.**  These marks describe the computational checks, not the validity of the paper's proofs.

| Result group | Coverage | Scope |
|---|---|---|
| `sec:charts` Marked charts and strict descent | ⚠️ Partial | The diagonal characterization, the span and local data of legal marks, the gauge example, strict area and equal outer functions through one mark; the fiber, source-minimality and joint-hypothesis statements have no check |
| `sec:reduction`, `sec:completion` Factor readout and the two-copy reduction | ⚠️ Partial | Satisfiability of the landing data, the degree-two domino readout, and the aligned-case score comparison |
| `sec:comparison` Finite comparisons on actual composition charts | ⚠️ Partial | Flag lists, chart supports, the mixed baseline determinant, the one-period mixed response, the coarse weights and the live crossing on small diagrams; the ordinary first-response Jacobian and normalization have bounded checks, but the full comparison is not instantiated |
| `sec:children`, `sec:boundary` Children, boundary comparisons and completion | ⚠️ Partial | The aligned lift, the literal mixed factor and the signed-cap word lemma; the remaining interfaces have no check |
| `app:boundary` Boundary constructions | ⚠️ Partial | Transports, the rectangle construction from closed words, the cycle lemmas and the wide and equal-width upper marks; the endpoint-splice and two-window constructions have no check beyond their sweeps; the line finer and the high head are checked through the finite objects their proofs build, not through the descent |
| `app:physical` Whole currents and the first complete grade | ⚠️ Partial | The two-copy flags and splice identities, the signed ordinary activation and unsigned mixed compound identities, and the first grade on bounded ranges; the activation example also has a symbolic two-route check |
| `app:first-responses` First responses and the unshifted defect | ⚠️ Partial | The all-`J` statement exhaustively on a bounded range; the coframe algebra, neutral adjugate and cutoff family; the response equations in the fine field have no check |
| `app:cofaces` Cofaces and two-copy identities | ⚠️ Partial | The equal-children step of the coface data, ordinary two-copy flags and fixed matrix, low native row cofactor, native signatures with both exceptional column classes retained, and direct marked factorizations through the proposed short-width roots; the zero-response implication itself is not instantiated |
| `app:endpoints` Endpoint scalars and ordinary reflection | ⚠️ Partial | The pinches, the geometric endpoint splice, the square high piece, the endpoint product, and the mixed sign proof's parity mechanism; bounded subgate counts do not establish universal satisfiability or emptiness |
| `app:mixed-empty` An empty upper over a mixed inner | ⚠️ Partial | The junction identity, the empty row parent flags, the splice sum and the pencil formula on compositions through a mixed mark; the window cofactors and the recovery of the coarse outer have no check |

## Dependencies

| Component | Used by | Description |
|---|---|---|
| `requirements.txt` | every script | Pinned SymPy and mpmath |
| `_gluing_common.py` | every script building a diagram or a composition | Cell sets, connectivity of skew shapes, the mark record and its legality test, composition by adjacency propagation, and the exact Schur function from a Jacobi–Trudi board, as in the supplement of [1] |

## License

MIT; refer to `LICENSE.txt`.

This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. J. Shields, *Local common-factor gluing and reduction of composition necessity for skew Schur functions*, preprint, 2026.

Refer to the paper for references.
