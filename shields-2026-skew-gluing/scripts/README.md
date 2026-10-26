# Computational supplement — Local common-factor gluing and reduction of composition necessity for skew Schur functions

Cross-check scripts for the marked compositions, component keys, and period arguments in `shields-2026-skew-gluing.tex`.  The checks use exact integer polynomials, cell-set legality tests, and independently constructed finite equality graphs.  They import no private data or research engine.  Composition by adjacency propagation is compared with diagonal-rank offsets; Schur polynomials are checked against integer determinant evaluations and, for the smaller boards, full permutation expansions and direct semistandard tableaux.

The paper proves that common-factor components are cliques and that every source-minimal chart at a rooted vertex describes its whole component.  It identifies the components by marked and polynomial data and reduces composition-and-reversal necessity to terminal rigidity and equality of keys for rooted mates.  Neither global assertion is proved.  The scripts test explicit charts, hypothesis boundaries, and finite instances of the arithmetic and graph arguments; they enumerate all roots only for diagrams of at most nine cells, and all connected Schur mates only for diagrams of at most ten.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Python 3.10 or later is required.  From this directory:

```sh
python3 -m pip install -r requirements.txt
bash run_all.sh
```

The harness stops on any failed assertion and prints `ALL PASS` only after every mathematical script finishes.

## Scripts by section

| Paper section or result | Script | Checks |
|---|---|---|
| Local common-factor gluing; equal and divisible periods | `verify_common_factor_graphs.py` | Proper I–IV certificates, marked reversal, exact outer and parent equality, complete witness graphs, a divisible-period fork with nonrotation equal outers, and the width-zero case of the reassociation lemma at both edge readings, including the antitransposition gauge |
| Diagonal geometry; window locality and mark transfer | `check_mark_locality.py` | The mark lister against the separate search in `check_gcd_fold_sweep.py`; the last window of a mixed composite translated by the same vector for every outer of a span; legality, attachment case and hatted mark constant on every class of diagrams sharing the two windows one diagonal wider than the mark; legal marks below the period equal across all outers of one span, and none at the period on a mixed composite while ordinary composites carry some; the cell-set form of the diagonal criterion on every subset of a 4x4 box; the southeast endpoint and periodic southeast word of every mixed composite in range; and the row-and-hook and width-three examples printed in the paper |
| Recovery from the generic words; ordinary cell criterion; native ordinary, EMPTY and mixed folds | `check_native_word_folds.py` | Connected parents reconstructed from both full words with unconstrained labeled port bits, at outer span one, two and three; native signatures realized as actual legal inners before an independently searched divisor mark is decoded and recomposed; equal native ranks, both exceptional mixed occupancies, endpoint contacts, small and large widths, zero/singleton/multiple remainders, both mixed phase orders, ordinary gauges, genuine EMPTY common fills, full end windows and strict areas.  Controls retain identical heights with different words, reject an illegal supplied mark, distinguish partial EMPTY cycles from a common fill, and detect omitted mixed supplements |
| Reassociation through a coarse mark; the antitransposition gauge | `check_reassociation.py` | For every connected inner of at most six cells, every legal mark on it, every connected outer of at most three cells and every legal coarse mark on the composite whose displacement has content a multiple of the period, a legal fine mark or edge reading and a choice of identity or antitransposition for which the reassociation identity holds on every connected coarse outer of at most four cells, with the identity on the coarse outer unless the fine mark is empty; the gauge identity for every case-(a)/(b) pair of ordinary marks through nine cells.  Controls: the unchanged outer fails with the horizontal reading, rotating the outer on the left side alone empties every working set, and transposition in place of antitransposition breaks the gauge |
| The chart definition; the figure | `make_figures.py` | The chart drawn in the paper's figure: the mark against the legality predicate for I–IV, the composition by the structural route and by the displayed offset formula with the two required to agree, and the two drawn copies verified to union to the parent and to overlap in exactly the mark.  `--check-only` verifies without drawing and imports no plotting library |
| Local common-factor gluing; ordinary and mixed gcd roots | `verify_common_factor_graphs.py` | Two actual nondividing-period presentations and independently recovered extreme-window gcd inners |
| Period words; appendix, Mixed cap data | `verify_period_words.py` | One-hole and ordered two-hole equality graphs, the retained mixed-height identity, and the excluded dividing-period control |
| Row inners and the line-inner alternative | `check_row_inner_action.py` | The legal row mark built from cells; cell-placed composition against the affine profile formula, with beta lists, rotation and negative Jacobi–Trudi positions; the congruence form of the row-inner condition against its gcd-and-offset form; the substitution carrying each outer's polynomial to its image's; full connected classes of every image of at most ten cells against the images of the outer's class; and, for every outer of at most ten cells, equal outer polynomials exactly when the image polynomials are equal, including the nonrotation classes in that range |
| Source-minimal fibers | `check_component_controls.py` | The complete three-cell hook class, the coarse-fiber obstruction, the ordinary-gauge involution, and the line-inner qualification, reconstructed from cells |
| Source-minimal fibers; reduction of composition necessity | `verify_component_reduction.py` | Strict modular score descent, rotation augmentation and quotienting, the terminal/rooted logical split, and an abstract disconnected-rooted graph control |
| Source-minimal fibers | `check_gcd_fold_sweep.py --controls` | The same four controls rebuilt from a separate cell implementation, with Schur equality decided by a dual Jacobi–Trudi determinant in the elementary generators |
| Two ordinary roots; pairs involving mixed charts; appendix, Quantitative data for the gcd charts | `check_gcd_fold_sweep.py --sweep` | Generated parents carrying two nondividing-period charts.  Each parent is a row composed with an inner of one fixed period, so the gcd of the two coarse periods is that period and the gcd root is the generating chart, present by construction.  What is tested is the fold: at remainders of two or more, the appendix's prescribed mark and outer, computed from the two coarse charts alone, are legal and recompose the parent.  Remainders zero to three by default, zero to four with `FULL=1` |
| Two ordinary roots; pairs involving mixed charts | `check_gcd_fold_words.py` | Parents generated from two punctured period constraints and cap bits rather than from a known gcd factor, then tested for literal I–IV charts and the prescribed fold.  Each actual pair, in both selections of its supplied inner, checks the completed native sets, reconstructs a legal divisor root, and searches for the same descended full mark and permitted gauge on the original outer and connected test outers, including a nonribbon outer.  Genuine EMPTY pairs also check the common-return rank equation before filling either return.  A control distinguishes connected word pairs from legal charts |
| Source-minimal fibers; reduction of composition necessity | `check_component_keys.py` | Every connected diagram of at most nine cells: one source-minimal key per rooted diagram, least-period divisibility without line inners, and common-factor components that are cliques identified by their keys.  On every connected class of at most nine cells the rotation-augmented graph is connected, and (TR) and (RI) hold throughout that range, so only the forward implication is exercised; the converse is checked on abstract graphs by `verify_component_reduction.py` |

## Coverage by section

Coverage below describes these finite computational checks, not the scope of the paper's proofs.

| Portion of the paper | Computational coverage |
|---|---|
| Charts, fibers, and clique conclusion | Explicit complete witness graphs, with every edge certified by proper legal charts and equal outer polynomials |
| Window locality and mark transfer | Every connected diagram up to a fixed area for locality, every subset of a 4x4 box for the cell-set form of the diagonal criterion, and every mark on an inner up to a fixed area with every outer up to a fixed span for the window translate, the case-(d) southeast word and the transfer; `FULL=1` widens each range, and the script prints the ranges it ran |
| Generic decoder and native folds | Exact finite word and native-signature ranges in `check_native_word_folds.py`, with actual cell legality and independent cell recomposition; the decoder retains both gauges and every attachment type, and the empty check requires one earned common fill rather than assuming periodic returns |
| Divisible-period refinement | An explicit mixed fork and direct third-edge certificate, and the width-zero case of the reassociation lemma for several connected outers at both coarse displacements; the full reassociation identity on every inner, mark, outer and coarse mark in the stated ranges |
| Nondividing-period gcd construction | Ordinary empty-overlap and mixed singleton-overlap fixtures, with both coarse charts checked; generated nondividing chart pairs at remainders zero to three, or zero to four with `FULL=1`, the prescribed fold recomposing the parent at remainders of two or more; punctured-word parents additionally exercise actual-inner native restriction and aligned composition without a preplanted gcd root |
| Finite period arguments | Bounded equality-graph sweeps, with the nondividing and overlap-band hypotheses retained |
| Row-inner action and class transport | Every connected outer of at most seven cells at periods two to four for the action and the substitution; every connected parent of at most eleven cells for the row-inner condition; full classes among connected diagrams for images of at most ten cells |
| Source-minimal components and keys | The four explicit geometric controls, exact parent and outer polynomials, bounded score comparisons, and an all-root census of source minima, keys and components for every connected diagram of at most nine cells |
| Reduction of composition necessity | Every rotation-covariant cluster graph on six vertices, with a control rejecting omission of covariance; abstract graphs are not asserted to be Schur classes |
| General wide-mark legality and arbitrary classes | No exhaustive computational claim; the unbounded proofs are in the paper |

Controls reject an incorrect attachment case, a false polynomial equality, omitted mixed supplemental copies, an outer that is not antitransposed at the vertical edge, omission of the outer involution from a key, an overbroad one-hole lemma, and a changed folded endpoint.  Dropping the padding by the width's generator breaks the substitution, an unreduced offset breaks the row-inner condition, and a map shifting rows but not overlaps splits every nonrotation class in range.  A disjoint union of cliques checks the distinction between local gluing and connectivity.  Windows narrowed by one diagonal, marks one wider than the period, and a literal comparison across outers for ordinary marks each break the corresponding locality or transfer assertion, and dropping the singleton-end clause breaks the cell-set criterion.  The nonminimal-fiber example prevents replacing a source-minimal chart by an arbitrary chart.

## Dependencies

Refer to `requirements.txt`.  The cell-set component controls use SymPy for independent integer determinant evaluations; the other mathematical scripts use only the Python standard library.

## License

Licensed under the MIT License.  See [LICENSE.txt](LICENSE.txt).

This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. P. R. W. McNamara and S. van Willigenburg, *Towards a combinatorial classification of skew Schur functions*, Transactions of the American Mathematical Society 361 (2009), 4437–4470.
2. N. Olson-Harris, *Some applications of combinatorial Hopf algebras to integro-differential equations and symmetric function identities*, Ph.D. thesis, University of Waterloo, 2024.

Refer to the paper for references.
