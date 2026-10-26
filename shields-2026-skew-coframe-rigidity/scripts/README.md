# Computational supplement — Coframe rigidity and finite stationary separation for skew Schur functions

Cross-check scripts for the complete Jacobi–Trudi coframes in `shields-2026-skew-coframe-rigidity.tex` [1].  The scripts rebuild matrices, signed corners, native solves, and literal splices from full beta lists using exact SymPy arithmetic.  Common row-column betas remain genuine coherent units; no numerical sampling or external data is used.

The paper proves same-literal-cap rigidity, a separate constant-weight linearized theorem for zero-free children and caps, and finite shifted stationary separation with whole-field descent.  Its unshifted theorem concerns opposite ends of one actual diagram.  The scripts corroborate bounded cases and the distinctions among those hypotheses; they do not prove the uniform statements or a classification of skew Schur equality.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.10 or later.  The pinned dependencies are SymPy 1.14.0 and mpmath 1.3.0.

```bash
python3 -m pip install -r requirements.txt
bash run_all.sh
```

The harness runs serially.  Each script raises an exception on a failed assertion and prints `ALL PASS` only after its checks finish.  The harness prints its own final `ALL PASS` only after every script succeeds.

## Scripts by section

| Where | Script | Paper section | Content |
|---|---|---|---|
| §2 | `verify_coframe_coordinates.py` | `sec:coframe-coordinates` | Native support, independent atlas inversion, positive row degree, signed corners, coequal defect bounds, weak-cap joint numerators and tail recovery, exact shift correction |
| §3 | `verify_fixed_caps.py` | `sec:fixed-caps` | Literal full-flag splices, connectedness and area, determinant/coframe identity, equal-function pairs with the same cap, figure cells, failure of replacing the literal cap by an equal-function cap |
| §4 | `verify_unit_restoration.py` | `sec:unit-restoration` | Complete bordered determinants and feedback pulses, finite native-equation injectivity, constant-weight coefficient rank, raw-rational-weight boundary, whole-array and cell-splice grades |
| §3 | `verify_fixed_cap_census.py` | `sec:fixed-caps` (`sc:fixed-cap`, `sc:splice-flags`, `sc:splice-identity`, `sc:fcp-observations`, `sc:fcp-prefix-zero`, `sc:fcp-prefix-solve`) | Fixed-cap rigidity as a census in exact integers: every connected child through span seven against every connected cap through span four, with the splice connected of span \(c+a\) and area \(|K|+|B|\) and the map to the two functions injective; every coequal pair separated by every cap; the two displayed observations equal to the whole-function differences; the top-letter extraction and the prefix compensation formula |
| §4 | `verify_linearized_and_grades.py` | `sec:unit-restoration` (`sc:restoration-polynomial`, `sc:bordered-grade`, `sc:linearized-cap`, `sc:splice-nonzero`) | The bordered restoration polynomial and its two grades on every zero-free board through span eight; the stacked restoration polynomials of child and splice independent over \(\mathbb Q\) for every zero-free child through span eight and zero-free cap through span four, with the child observation alone dependent on some child; the first nonzero grade of the cell-splice difference on every diagram through span eight |
| §4 Thm 4.3 | `verify_linearized_observations.py` | `sec:unit-restoration` (`sc:linearized-observations`) | The two differentiated fixed-cap identities: the variation of the child's whole function and of the splice's whole function in terms of the first variation of the coframe and of the signed corner, on every zero-free child and two caps |
| §4 Thm 4.3 | `verify_linearized_cap_steps.py` | `sec:unit-restoration` (`sc:linearized-prefix`, `sc:linearized-zero-range`, `sc:linearized-direct-zeros`, `sc:strict-block-variation`) | Inside the proof of the linearized fixed-cap theorem: the prefix compensation at every cut into leading strict blocks through span seven, with a weight above the prefix breaking it; the zero range as the implication the proof uses, solved with generic coefficients on every zero-free cap through span four, child span through seven and every raw ceiling, and shown sharp; the direct zeros inside that range, symbolically; and the strict-block variation as a polynomial identity in symbolic weights: once the direct zeros hold, the derivative at the head letter is \(s_E\dot s_N-s_N\dot s_E\) times a weight-free nonzero factor, at every cut through span nine, and fails to be without them |
| §4, §3 | `verify_block_cramer_quotient.py` | `sec:unit-restoration`, `sec:fixed-caps` | The inverse column selected by the head of a strict block equals the numerator over \(\det P\) times the block function, on every zero-free board through span nine with at least two strict blocks |
| §5 | `verify_stationary.py` | `sec:stationary` | Component remainders and true-unit/cell distinction, sampled rational potentials on actual coequal pairs, exact terminal coframes, whole moving inverse and higher-clock compatibility |
| §5 Thm 5.4 | `verify_positive_power_steps.py` | `sec:stationary` (`sc:top-matching`, `sc:complete-pole-bracket`, `sc:first-pole-jet`, `sc:cell-second-jet`, `sc:unit-first-cap`, `sc:whole-field-equation`) | The steps of the one-power separation proof: matching of the top components from the two endpoint observations with controls, the pole bracket and first pole jet coefficient by coefficient on every matched pair through span seven, the cell second jet with generic defect coefficients, the first-order true-unit identity with its exponent-one control, and the coefficient extraction of the whole-field equation |
| §6 | `verify_unshifted.py` | `sec:unshifted` | Opposite-end defects, first neutral coefficient, complete highest-letter expansion, exponent-two row exception, span-seven/eight flag exhaustion and a span-nine boundary |
| §6 Lem 6.1 | `verify_unshifted_all_p.py` | `sec:unshifted` (`ph:unshifted-exclusion`) | The lemma for every exponent \(p\ge2\) on every connected board of span three to five: each defect coefficient is \(\vartheta^p\) times a polynomial in \(p\) of degree at most \(2M\), asserted by interpolation reproducing further exponents; on every nonself board one such polynomial is nonzero with no integer root \(p\ge2\), and on self boards all vanish |
| §3, §4, §5 | `verify_proof_identities.py` | `sec:fixed-caps`, `sec:unit-restoration`, `sec:stationary` (`sc:linearized-coframe`, `sc:linearized-prefix`, `sc:gap-coface`, `sc:fcp-numerator-flags`, `sc:fcp-recursive-cap`, `sc:component-column`, `sc:common-top-column`, `sc:component-ratio`, `sc:two-endpoints`, `sc:native-shift-identity`) | The displayed identities inside the proofs: the first variation of the coframe under constant weights and its prefix compensation; the numerator flags, their connectivity, the Schur-complement coface and the literal cap-splice form of every proper-block cut; the endpoint coefficients of the shifted operator, the affine dependence of the coframes on the top proper letter with derivative \(-z^ag/k\), the component-ratio derivative, and the vanishing of the whole cap polynomial |

## Coverage by section

**Work in progress.**  All proofs in the paper are unconditional and noncomputational.  A row marked **⚠️ Partial** below describes bounded computational coverage, not a gap in the paper's proofs.

| Paper section | Coverage | Exact scope and limitation |
|---|---|---|
| `sec:introduction` | — | Orientation and statements of the paper's contracts; no additional computation |
| `sec:coframe-coordinates` | ⚠️ Partial | All connected full flags of spans one through four; explicit feasible weak caps, including units and disconnected blocks; disconnected and empty-row degree controls.  No uniform irreducibility or absolute-flag proof is claimed by computation. |
| `sec:fixed-caps` | ⚠️ Partial | Connected children through span seven against every connected cap through span four; the figure example on cell, two-cell-row and two-cell-column caps.  The equal hook figure is derived exactly from flags.  The strong induction is noncomputational. |
| `sec:unit-restoration` | ⚠️ Partial | Zero-free children through span four; native-equation injectivity through span three; coefficient rank for three zero-free caps.  A row-three child-only kernel and a raw-rational row-four two-observation kernel test the stated boundaries.  Both core cases of the cell-splice grade are tested through span four. |
| `sec:stationary` | ⚠️ Partial | Components and coequal pairs through span four, exponents two through four, explicit rational potentials, and the full-clock span-three example.  Neither all rational potentials nor the general field-intersection argument is decided by this finite suite. |
| `sec:unshifted` | ⚠️ Partial | Opposite ends through span five at every exponent \(p\ge2\), through span four at exponents two through four, selected complete highest-letter expansions, the two-cell-row exception, all balanced residual flags at spans seven and eight, and one nonself span-nine board.  The complete exceptional-case proof remains the manuscript's argument. |
| `sec:conclusion` | — | Scope boundaries, with no new computational assertion |

## Dependencies

Refer to `requirements.txt`.  The scripts need no manuscript, reference library, build directory, network access, or generated data to run.

| Component | Used by | Description |
|---|---|---|
| `check_paper_crossrefs.py` | `run_all.sh` | Label index and the scanner for number citations over every script and this file; run directly |
| `_coframes.py` | All section scripts | Full-flag matrix construction, exact native coframes, finite clipping, actual rotation/splicing, cells, vacancy restoration, and absolute adjugates shared by the independent assertion suites |

## License

MIT; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the LICENSE.txt at the root of the repository.

## References

1. J. Shields, *Coframe rigidity and finite stationary separation for skew Schur functions*, preprint, 2026.
2. F. Barekat, V. Reiner, and S. van Willigenburg, *Corrigendum to “Coincidences among skew Schur functions”*, Advances in Mathematics 220 (2009), 1655–1656.  https://doi.org/10.1016/j.aim.2008.10.010

Refer to the paper for references.
