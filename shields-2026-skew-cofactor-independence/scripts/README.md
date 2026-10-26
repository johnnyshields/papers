# Computational supplement — Cofactor independence and dilation for skew Schur functions

Cross-check scripts for `shields-2026-skew-cofactor-independence.tex`.  Each one rebuilds the
objects the paper defines — beta lists, the Jacobi–Trudi matrix, its signed cofactors, the
first-variation units — from those definitions, and compares what it finds against the identities
and dimension counts the manuscript states.  Everything is exact: determinants expand over the
integers or rationals, ranks are exact, and no floating-point arithmetic appears anywhere.

The populations enumerated here are finite, and finite evidence corroborates an unbounded statement
without establishing it.  Every theorem in the paper is proved for every order, so no count below is
a premise for anything the paper claims; where a script exhibits a single object rather than a
population — a counterexample, or a witness that some case is non-empty — that is said in its own
output.  The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Python 3.10 or newer.  The scripts that compute ranks over many boards use `python-flint` for exact integer matrices, `check_symmetric_unit_kernel.py` uses SymPy, and the rest use the standard library only.

```sh
pip install -r requirements.txt
sh run_all.sh
```

The run prints each script's own summary and ends with `ALL PASS`.  Any failure raises an
`AssertionError` naming the claim that broke.

## Scripts by section

| where | script | paper section | what it checks |
|---|---|---|---|
| §2 Thm 2.3 | `check_nonnegative_rigidity.py` | `sec:boundary` | `thm:nonnegative-rigidity` on a census of every connected skew shape through a cell bound: no member of a nontrivial Schur class has nonnegative Jacobi–Trudi indices, with relaxed hypotheses as firing controls; a direct mate-space comparison on small areas |
| §3 Thm 1.1 | `check_cofactor_relations_exact.py` | `sec:cofactors` | `thm:cofactor-relations` by exact rank over every normalized dense core of orders 2 to 5, with the private-derivative, boundary-pair, rotation-branch and symmetric-leader steps of its induction; four firing controls |
| §3 Thm 1.1 | `check_cofactor_relations_all_spans.py` | `sec:cofactors` | `thm:cofactor-relations` for every dense core of orders 2 and 3 whatever its span: the cofactors depend on the core only through which labels coincide, so the realizable label patterns are enumerated exactly as the faces of a hyperplane arrangement in the gaps, each is met by a witness core, the renaming is checked coefficient by coefficient on same-pattern pairs, and the rank and reflection relations are asserted on every pattern |
| §3, §4 | `check_dense_kernel_inputs.py` | `sec:cofactors`, `sec:restoration` | Both inputs of edge normalization: the cofactor ranks \(k^2\) and \(k(k+1)/2\), and the reflection kernel on symmetric cores of order at least two |
| §2–§6 | `check_cofactor_dilation.py` | `sec:boundary`, `sec:cofactors`, `sec:restoration`, `sec:dilation`, `sec:full-equality` | The cofactor relations and their exact ranks; the dilation direct sum and the nullity increment; the path expansion; the first-correction control; the arbitrary-mate reconstruction; the finite-word period bound |
| §2 Lem 2.1, Lem 2.2, Thm 2.3 | `check_exterior_gaps_nonnegative_class.py` | `sec:boundary` | `lem:exterior-gaps`, `eq:border` and `eq:corner-coefficient` on every connected diagram with no negative index through 14 cells, the boundary case of a unit on the board included: the border form of the lists, the largest remaining generator, its coefficient in each of the three margin cases, and the positivity facts the rigidity induction uses; the diagrams outside the hypothesis are counted beside them |
| §4 Prop 4.1, Lem 4.3 | `check_path_expansion_and_endpoint_units.py` | `sec:restoration` | `prop:path-expansion`, `eq:path-entry` and `eq:first-components` over every connected zero-free core of span at most 8 and order at most 4, dense or not, and every set of restored positions; `lem:endpoint-cancellation` at every beta endpoint and outside the span, with the gap-zero convention as a control that gives the nonvanishing determinant |
| §3 | `check_ref_induction.py` | `sec:cofactors` | The cofactor-degree identity; the rank formula in both cases, including boards whose entry labels repeat heavily; the interlacing chain and the symmetric leading monomials; the private-derivative identity; the symmetric-child branch of the induction; the boundary-pair separation |
| §4 | `check_dense_kernel.py` | `sec:restoration` | The base kernel on nonsymmetric dense cores as the words \(\phi(z \bmod g)\) with \(\phi(r)+\phi(N-r)=0\), by exact rank and explicit relations, also on dilated cores; symmetric cores, the modulus \(2g\) and single-site vectors as firing controls |
| §4 Prop 4.4 | `check_symmetric_kernel_exact.py` | `sec:restoration` | `prop:symmetric-unit-kernel` on every symmetric dense core of orders 2 to 5: \(U_z=U_{N-z}\), the rank, independence of the representatives, and the derivative steps of its induction; firing controls |
| §4 Prop 4.4 | `check_symmetric_unit_kernel.py` | `sec:restoration` | The same proposition by exact rational linear algebra, with the dilation symmetry and density instances |
| §4 | `check_symmetric_lower_bound.py` | `sec:restoration` | That the units of a symmetric core satisfy \(U_z=U_{N-z}\), that the available positions are closed under reflection, and that the resulting relations meet the stated dimension |
| §4 | `check_symmetric_child_derivative.py` | `sec:restoration` | The derivative identity carrying the symmetric induction: differentiating at the private generator lands on the normalized child, with the sign, and the representatives correspond |
| §2, §4 Prop 4.1, §5 Lem 5.1, Thm 5.2, Cor 5.3, Ex 5.4, §6 Cor 6.1 | `sec:boundary`, `sec:restoration`, `sec:dilation`, `sec:full-equality` (`eq:profile`, `eq:rotation-condition`, `eq:cofactor-degree`, `lem:endpoint-normalization`, `eq:all-edges`, `cor:nullity-increment`, `ex:dilation-ray`, `cor:independent-restorations`) | `check_restoration_edges_and_rigidity.py` | Profile conditions, rotation on beta lists and the rotation-fixing condition, the cofactor degree formula; connected residual cores and connected restorations of the stated area and row count; the edge-equation solution space on every connected zero-free core, dense or not, equal to the odd residue functions modulo the endpoint modulus; the dilation ray to \(t=9\) with its explicit basis, the nullity increment at modulus one, and the strict containment of the concluding remarks; and rigidity of every restoration of every dense core with vanishing unit kernel, and of the doubles of the modulus-one nonsymmetric ones, against the complete table of connected diagrams through 12 cells |
| §5 Thm 5.2, Cor 5.3 | `check_dilation_all_t.py` | `sec:dilation` | `thm:dilation` and `cor:nullity-increment` for every dilation factor on every dense core of span at most 9 and order at most 3: the off-grid relations of the dilated core split by residue pair into one system independent of the factor and, for even factors, one middle system; those two kernels are computed once per core, shown to be the transported residue functions, and checked against direct kernels of the dilated cores; the nullity increment is then symbolic in the factor on each parity class |
| §5 | `check_widen_containment.py` | `sec:dilation` | That the containment stated without the cofactor hypothesis holds, and is not vacuous, on a symmetric core where the equality itself fails |

## Coverage by section

| section | covered | note |
|---|---|---|
| §2 Boundary coefficients and dense rigidity | yes | reconstruction against arbitrary connected mates, and the global census, each to a stated cell bound |
| §3 Linear relations among cofactors | yes | both clauses, with the repeated-label case exercised deliberately |
| §4 Common beta entries and first variations | yes | the path expansion over every restoration set of every small core, the first two ordinary components, the endpoint cancellation, the nonsymmetric base kernel and the symmetric kernel in full |
| §5 Integral dilation | yes | the direct sum and the nullity increment for every dilation factor on the cores in range, the dilation ray, the one-sided containment, and the edge-equation solution space on non-dense cores |
| §6 Restoration and full equality | yes | the separating coefficient of the unequal-restoration pair, and rigidity of every restoration of the dense cores with vanishing unit kernel through 12 cells |
| §1, §7 | n/a | introduction and closing remarks state no computational claim |

Each script asserts that its own enumeration is non-empty before reporting success, so a sweep that
silently stopped matching anything fails rather than passing.

## Dependencies

| Component | Used by | Description |
|---|---|---|
| `_cofactor_lib.py` | `check_cofactor_relations_exact.py`, `check_symmetric_kernel_exact.py` | Exact Jacobi–Trudi determinants, signed cofactors, first-variation units and flint rank over \(\mathbb{Z}[h_1,h_2,\dots]\), built once for the two sweeps that share them |
| `check_paper_crossrefs.py` | `run_all.sh` | Label index and the scanner for number citations over every script and this file; run directly |
| `python-flint` | `check_dense_kernel.py`, `check_dense_kernel_inputs.py`, `_cofactor_lib.py` | Exact integer matrix rank; pinned in `requirements.txt` |

## License

MIT, in `LICENSE.txt` beside this file.  This directory is also subject to the patent and trademark
terms in the `LICENSE.txt` at the root of the repository.

## References

1. F. Barekat, V. Reiner and S. van Willigenburg, *Corrigendum to "Coincidences among skew Schur functions"*, Adv. Math. **220** (2009), 1655–1656.
2. L. J. Billera, H. Thomas and S. van Willigenburg, *Decomposable compositions, symmetric quasisymmetric functions and equality of ribbon Schur functions*, Adv. Math. **204** (2006), 204–240.
3. I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford University Press, 1995.
4. P. R. W. McNamara and S. van Willigenburg, *Towards a combinatorial classification of skew Schur functions*, Trans. Amer. Math. Soc. **361** (2009), 4437–4470.
5. V. Reiner, K. M. Shaw and S. van Willigenburg, *Coincidences among skew Schur functions*, Adv. Math. **216** (2007), 118–152.

Refer to the paper for references.
