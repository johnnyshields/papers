# Computational supplement — Factor Schur functions of marked compositions from differential operators

Cross-check scripts for `shields-2026-skew-marked-factor.tex`.  All comparisons use exact integer or rational arithmetic, cell-set geometry, and Jacobi–Trudi determinants; no external composition or symmetric-function engine is imported.

The paper recovers the inner and outer Schur functions from the parent function and a supplied period: ordinary charts allow arbitrary connected outers, while mixed recovery requires a ribbon outer.  Its ordinary power-sum action is Olson-Harris's theorem [1], proved using key-ribbon deletion; the mixed inverse uses weighted derivations and ordered character inversion.  The common-period marked-fiber comparison additionally requires an inner determined up to rotation by its function.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.12 or later:

```sh
python3 -m pip install -r requirements.txt
bash run_all.sh
```

The suite finishes with `ALL PASS`.  It can take several minutes because it expands exact parent determinants and rational gcds.  The extraction sweep can be enlarged with `python3 verify_extraction.py --max-inner 6 --max-outer 4`.

## Scripts by section

| Where | Script | Paper section | Content |
|---|---|---|---|
| §2 | `verify_power_sum_action.py` | `sec:action` | Murnaghan–Nakayama by beta-number removal versus polynomial differentiation; literal lifted ribbons and their heights; the full normalized action; the empty-outer distinction |
| §2 | `check_thesis_marks.py` | `sec:action` | The thesis's vocabulary of marks against Hypotheses I–IV, key ribbons, and the properness criterion, over every connected inner of three through nine cells |
| §2, Lem. 2.2 | `check_hopf_action.py` | `sec:action`, `lem:action` | The power-sum action identities in the formal space of shapes, with no Schur functions involved; four firing controls on the signs and the power of the normalizing factor |
| §3 | `verify_weighted_action.py` | `sec:weighted-action` | Actual generator and original-order beta-move identities, literal mixed strip remainders, all four attachment readings, full signed modifiers, physical involution transport, empty-edge exhaustion, and wrong-sign controls |
| §4 | `verify_extraction.py` | `sec:extraction` | Terminal order, reduced-numerator inner recovery, every top-weight character ratio, outer recovery in both ordinary gauges, and the two terminal formulas |
| §4, Lem. 4.1 | `check_primitive_monomial.py` | `lem:primitive` | The row-length monomial is the unique minimum-square monomial with coefficient \(+1\), for every connected diagram of at most eight cells; the two-term form of two-row functions |
| §4, Thm. 4.2 | `check_readout_flint.py` | `thm:extraction` | The terminal order, the reduced numerator, and the outer readout by a second route (exact multivariate polynomials from python-flint), over every legal ordinary mark on inners of two through seven cells; firing controls for a wrong period, a mixed chart, and the missing involution |
| §4, Thm. 4.2 | `check_decoder_modes.py` | `thm:extraction`, `eq:ratio` | The decoder fed only the parent and the period, recovering the inner, the outer, and the hatted factors by the same second route, over inners of three through five cells and outers of four through six cells; area bounds, cross-type exclusion, and a period-shifted control |
| §2, §4 | `check_hatted_mark.py` | `sec:action`, `sec:extraction` | A nonempty hatted mark in both ordinary conventions, over a row and a square outer |
| §5, Prop. 5.1 | `verify_mixed_extraction.py` | `sec:mixed-extraction`, `rt:mixed-readout`, `rt:outer-triangle` | Decoder supplied only the parent and period; terminal and penultimate outputs, fractional-alphabet nonvanishing, integer phase content, every outer character value, full signed normalizer, and order/gauge/sign controls |
| §3, §6 | `verify_transport.py` | `lem:mixed-vanishing`, `sec:transport` | The mark atlas, literal antitransposition gauge, mixed core boundary and annihilation, mixed rejection, and two-row comparisons |
| §7 | `verify_examples.py` | `sec:examples` | Two-row terminal formulas, the displayed nonrotation pair, its recovered outer polynomial, the ordinary involution control, and the legal mixed hook with its exact weighted tail and supplemental column-domino sign |

Every script prints `PASS` lines and ends `ALL PASS`; a failed identity raises `AssertionError` and exits nonzero.

## Coverage by section

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.  These marks describe the exact computational checks, not the validity of the proofs.  **⚠️ Partial** means that a universally quantified theorem is checked only on the stated box.

| Section | Coverage | Domain |
|---|---|---|
| Introduction | — | No additional mathematical assertion beyond the cited results and main theorems |
| Marked composition and the power-sum action | ⚠️ Partial | All connected diagrams of at most seven cells for ribbon differentiation; all legal horizontal marks on inners of two through five cells and all connected outers of two through four cells for the action and literal ribbon lifting; the formal-shape action on inners of two through six cells and outers of up to three cells |
| Weighted composition covariance | ⚠️ Partial | Every legal mark on the six seed profiles \((3)\), \((2,2;1)\), \((2,1;0)\), \((3,2;0)\), \((4,2;1)\), \((3,3;1)\) and their rotations and antitransposes; row generators through weight three, beyond-exhaustion modes, literal mixed strips, and full modifiers on row, column, hook, and square outers |
| Recovering ordinary factors | ⚠️ Partial | Every ordinary legal mark, including both empty readings, on inners of two through five cells and all connected outers of two through four cells by the Jacobi–Trudi route; inners of two through seven cells by the second route; the minimum-square monomial on every connected diagram of at most eight cells |
| Recovering mixed ribbon factors | ⚠️ Partial | Every mixed legal mark on inners of three through five cells and every ribbon outer of one through four cells; the six-cell inner \((4,2;1)\) and its physical transforms add a nonempty hatted mark |
| Equal functions at a common period | ⚠️ Partial | All legal marks on inners of two through six cells; all connected outers of two through four cells; equality comparisons within the resulting two-row-inner sample |
| Explicit formulas and examples | ✅ Full | Every displayed example; the general two-row formulas are also swept over a finite parameter box |
| Concluding remarks | — | Scope summary only |

The hatted-mark probes include nonconstant local factors.  Firing controls reject a wrong period, reject mixed charts in the ordinary decoder, distinguish the two ordinary outer gauges, preserve the genuine mixed outer, detect a wrong mixed local sign and reversed weighted-operator order, and distinguish the algebraic empty-outer unit from the geometric overlap function.

## Dependencies

Refer to `requirements.txt`.  The files below assert nothing about the paper themselves.

| Component | Used by | Description |
|---|---|---|
| `schur_tools.py` | the `verify_*` scripts, `_weighted_readout.py`, `check_hatted_mark.py`, `check_primitive_monomial.py` | Cell operations, direct I–IV mark tests, recursive Laplace expansion, polynomial adjoints, a diagram-free ordinary decoder, and a standard-tableau count by corner removal |
| `_composition_engine.py` | `check_decoder_modes.py`, `_readout_lib.py`, `_hopf_shapes_lib.py` | Composition of marked diagrams from the four attachment cases and the hypotheses I–V as decidable predicates, used as the engine for shape enumeration and mark logic; run directly it prints a census of equal Jacobi–Trudi determinants and is not part of `run_all.sh` |
| `_readout_lib.py` | `check_readout_flint.py` | Exact multivariate polynomials in the h-alphabet, a separate Jacobi–Trudi expansion and power-sum adjoint cross-checked against Murnaghan–Nakayama deletion, built once |
| `_decoder_lib.py` | `check_decoder_modes.py` | Profiles, interiors, Jacobi–Trudi minors and exact polynomial primitives for the decoder; modular evaluation only certifies nonvanishing |
| `_hopf_shapes_lib.py` | `check_hopf_action.py`, `check_thesis_marks.py` | The formal space of shape classes with its two ribbon-deletion actions, built from the thesis's definitions |
| `_weighted_readout.py` | `verify_weighted_action.py`, `verify_mixed_extraction.py`, `verify_examples.py` | Weighted derivations, original-order beta replacements, full modified algebra maps, exact alphabet specialization, and the diagram-free mixed ribbon decoder |

## License

The code is licensed under the MIT License; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. N. Olson-Harris, *Some applications of combinatorial Hopf algebras to integro-differential equations and symmetric function identities*, Ph.D. thesis, University of Waterloo, 2024.  https://hdl.handle.net/10012/20710.

Refer to the paper for references.
