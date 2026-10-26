# Computational supplement — Skew Schur equivalence by Jacobi–Trudi negative count

Cross-check scripts for `shields-2026-skew-jacobi-negative.tex` [1], including exact certificate replays that corroborate its five-row classifications.  All mathematical arithmetic is integral or rational.  Determinants are compared by signed permutations and column-subset dynamic programming; infeasibility certificates are checked without a solver.

The paper classifies connected skew diagrams with at most six full-row Jacobi–Trudi negatives.  When the negative pattern requires at least seven rows to realize, nine negatives force rigidity; at ten negatives, exactly two seven-row quartet families are nonrigid and every higher-row source in that domain is rigid.  The complete exceptional classes have legal marked-composition presentations.  A saturated first negative column with at most two negatives elsewhere gives a separate rigidity criterion for sources with at least six rows, with no bound on negative count.  Its finite-order classifications and higher-row deductions are proved algebraically in the text.  The supplement checks formulas, replays symbolic searches, and reproduces the bounded census in the concluding remarks; the census does not establish the classification theorems.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.10 or later and install the pinned dependencies:

```bash
python3 -m pip install -r requirements.txt
bash run_all.sh
```

`bash run_all.sh` runs every check except two slow ones and takes a few minutes on a single core.  `FULL=1 bash run_all.sh` adds the full rational staircase search (`check_staircase_certificate.py`, up to an hour) and the seven-row ten-negative sample (`check_ten_negative_rigidity_sample.py`, about four minutes).  All are corroborating computations, not premises of the manuscript's algebraic proofs.  An interrupted run is not a pass.  The last line of a successful run is `ALL PASS`.

The optional second staircase execution requires `z3-solver==4.15.3.0`:

```bash
python3 -m pip install z3-solver==4.15.3.0
python3 check_staircase_certificate.py --backend z3
```

Both backends reuse the same occurrence matcher.  They are independent executions with different exact feasibility procedures, **not independent implementations of the search**.  The Z3 backend uses exact linear-real arithmetic, checks every rational model, and rejects unknown answers.  Neither backend permits floating-point feasibility.

## Scripts by section

| Paper section | Script | Check |
|---|---|---|
| Full boards and boundary coefficients | `check_boards.py` | Row/cofactor readings, units, rotation, and faithful homogenization |
| Full boards and boundary coefficients | `check_negative_shape.py` | The negative set is an order ideal, and rotation conjugates it: `lambda(D*) = lambda(D)'` |
| Full boards and boundary coefficients | `check_restoration_growth.py` | The negative count is not stable under common-beta restoration; one restoration of a three-negative core gives the staircase, two or more give `binom(n-1,2)` |
| Through four negatives; the four-row appendix | `check_low_negatives.py` | Formal exceptional identity, tied border coefficient, singleton contexts, reflected equal-endpoint separator |
| Through four negatives; the four-row appendix | `check_four_family_minimum.py` | The exceptional family at its least admissible area: the eight-cell pair at `(c,w,b) = (0,1,2)` |
| Square rigidity | `check_square.py` | Full block expansion, syzygies, all margin regimes, and unit/equal-factor cases |
| The five-negative five-row base | `check_five_cross.py` | Corroborating replay of the complete twelve-branch rational collision graphs |
| The five-negative five-row base | `check_five_within.py` | Corroborating replay of the complete forty-two-branch rational collision graphs |
| The five-negative five-row base | `check_five_negative_algebra.py` | Signed-permutation checks of the sixteen-plus-eight expansion, all marker regimes, finite same-/mixed-opening comparisons, and the prime obstruction including `d <= b` |
| Five negatives above five rows | `check_five_borders.py` | Formal family identities, endpoint isolation, tied monomial separators, and oriented borders |
| The five-row staircase | `check_staircase.py` | Independent support and task inventory, formal family identities, corrected cross-stratum cover |
| The five-row staircase | `check_staircase_certificate.py` | Corroborating execution of all 308 unbounded-parameter matching tasks with exact feasibility |
| Staircase endpoint extensions and borders | `check_staircase_borders.py` | Critical tied coefficients, both endpoint orders, units, and larger-row induction |
| Endpoint-response lemmas | `check_endpoint_responses.py` | Tied exterior data, one-negative component leaders, symmetric controls, and genuine units |
| Certificates and reproducibility | `check_certificate_inventory.py` | Complete retained execution records, equation-space verdicts, and corruption controls |
| Concluding remarks | `check_negative_count_census.py` | Exhaustive connected-profile census in areas eight through thirteen, with translation/rotation conventions, exact Schur fibers, the nine/three/six allocation, and the six residual representatives |
| The five-negative five-row base | `check_opening_coefficient_contacts.py` | Collected maximum-coefficient formulas for M/M, E/E and M/E candidate pairs, with both specialization branches of the prime lemma and a false-constant-generator control |
| Five negatives above five rows; staircase borders | `check_border_domain_boundaries.py` | Five-negative masks through twelve rows, staircase cofactor shifts, border and endpoint coefficients, and failure at the excluded b=g boundary; injects a dropped coefficient into the production comparison routine |
| The five-negative five-row base | `check_five_prime_nondivisibility.py` | Exact multivariate division in Z[H_*] deciding the prime obstruction over the bounded domain, with both specializations and accept/reject division controls |
| Realizability and minimum row count | `check_threshold_budget.py` | Component budgets, negative-pattern realizability, overlap minima, and homogenization |
| Dense endpoints; three-component assembly; sharpness | `check_threshold_identities.py` | Exact parent identities, marker tables, endpoint remainder, quartets, cell unions, and non-dense resonance |
| Disconnected cofactors | `check_threshold_recovery.py` | Full-board degree recovery and all three two-component tie extractions |
| Dense endpoints and component assembly | `check_threshold_ties.py` | Exact collision windows for dense components, end/middle placements, equal factors, and sparse two-component ties |
| Six negatives and minimum row count | `check_six_negative_patterns.py` | Strict endpoint-order denominator, overlap readings, and complete minimum-six component budget |
| Two-negative endpoint coefficients | `check_two_negative_endpoints.py` | Both split-child orders, tied and untied leading coefficients, and same-domain rejecting controls |
| Six-negative classification | `check_six_negative_classes.py` | Exact finite classes, common-beta homogenization, connected borders, and same-domain marker and unit controls |
| Endpoint coefficients for small-negative components | `check_two_negative_endpoint_orders.py` | Complete core windows through eight rows; collected endpoint leaders, tied-child comparisons, and independent permutation checks |
| Singleton contexts and saturated columns | `check_saturated_column.py` | Parent identities, all margin regimes, common-beta recovery, the unbounded family, and the five-row boundary |
| Ten-negative classification | `check_ten_negative_algebra.py` | The complete component budget and negative-pattern inventory, with higher-row child checks |
| Ten-negative endpoint suppliers and placements | `check_ten_negative_endpoints.py` | Generic four-alternant identity, effective leaders, the rank-two correction, lower remainders, cross-resonance exclusions, and hook intermediates |
| Exceptional singleton contexts | `check_ten_negative_contexts.py` | Formal response coefficients, complete row-multiset matching including special ratios, forced interfaces, and the surviving context locus |
| Ten-negative families and borders | `check_ten_negative_families.py` | Formal quartet identities, all separator permutations, reflected-core row exclusions, marked cell unions, and homogenization/parity transfer |
| Minimum row count; negative-count strata | `check_row_count_schur_invariant.py` | The row count is the top h-degree of the Schur function, over every connected diagram to a cell cap and the exceptional families, with controls that fire |
| Minimum row count; negative-count strata | `check_class_invariants.py` | Which board statistics are constant on a Schur class; the negative count, row and column multisets, and minimum row count, with the varying statistics witnessed |
| Sharpness and failures beyond the hypotheses | `check_ten_negative_seven_row_family.py` | The second seven-row ten-negative family: profiles, negative shapes, four-member class, and its legal marked-composition presentation |
| Sharpness and failures beyond the hypotheses | `check_six_row_nonrotation_families.py` | The six-row quartet families at seven, eight and nine negatives, with the staircase families excluded by direct construction |
| Singleton contexts and saturated columns | `check_saturated_column_mate_space.py` | Every row and gap arrangement of saturated-column sources at six and seven rows, by modular evaluation; five-row control fires |
| Disconnected cofactors | `check_separated_support_rigidity.py` | Blocks with disjoint gap supports, full mate space; the known 19-cell nonrotation pair is recovered as a control |
| Sharpness and failures beyond the hypotheses | `check_ten_negative_full_mate_space.py` | The complete classes of both ten-negative families over the full mate space, including parameters outside the census window |
| Ten-negative classification | `check_ten_negative_rigidity_sample.py` | Seven-row ten-negative sources outside the census span: rigid except the two quartet families; every conjugation orbit hit |

## Coverage by section

| Claim | Status | Evidence and scope |
|---|---|---|
| Polynomial readings and homogenization | ✅ Full | Identities checked on every legal profile with two to four rows and row lengths one to four; the paper gives the general proofs |
| Negative set is a partition shape; rotation conjugates it | ✅ Full | Both laws hold with zero violations on every legal profile with two to six rows and row lengths one to four; each has a two-line general proof.  The list of shapes realized at six negatives is a finite-box observation about that range, not a realizability claim |
| Scope of the negative count under restoration | ✅ Full | Every subset of the restoration sites of the core `(2a+1,7,5,3)/(6,4,2,0)` for `a = 5,6,7`; delimits the parameter and asserts nothing about restorations themselves |
| Four-row exceptional family at least area | ✅ Full | Family identity, three negatives, and four distinct members on every admissible `(c,w,b)` with `w <= 4`, `b <= 8`; the area minimum is a closed arithmetic question that the box exhibits |
| Low-negative algebraic reductions | ✅ Full | Formal four-row identity; all singleton margins one to three on the stated three blocks; the equal-endpoint hook control has both doubled tops |
| Square identities | ✅ Full | Every block row length two or three, internal gap zero or one, exterior margin one to three, separation one or two |
| Five-negative cross-pattern certificate replay | ✅ Full | Every node, successor cover, rational Farkas identity, and family implication in the supplied twelve graphs; corroboration of the algebraic proof |
| Five-negative within-pattern certificate replay | ✅ Full | Every node, successor cover, rational Farkas identity, and identity/rotation implication in the supplied forty-two graphs; corroboration of the algebraic proof |
| Five-negative algebraic interface | ✅ Full | Exact collected homogeneous polynomials on the normal-form window specified in `check_five_negative_algebra.py`; includes the independent unit variable and all second-corner regimes.  The prime-obstruction window retains cases with `d <= b`.  These finite tests do not prove exhaustion |
| Five-negative bordering formulas | ✅ Full | Both families with `2 <= g <= 4`, `1 <= q <= b < g`; extensions and margins one to three; formal tied separators |
| Staircase task coverage | ✅ Full | Symbolic support and all task specifications; finite box with gaps one or two and slacks in `(1..2, 1..3, 1..2, 1..3, 1..5)`; explicit S1/S3 and S1/S2 controls |
| Staircase matching execution | ✅ Full | Full exact matching execution, including completed tasks with no equality space; corroboration rather than a premise of the algebraic classification |
| Staircase border identities | ✅ Full | Declared M1–M4 boxes in the script, both endpoint orders, critical margins on both sides of the tie, and induction through eight rows |
| Bounded census | ✅ Full | Every connected full profile of area eight through thirteen, identified up to translation and rotation.  A counted class is one Schur fiber containing multiple rotation orbits.  Exact determinants verify the eighteen classes and their allocation; no absence of legal marked presentations is inferred |
| Minimum-row invariance and component budgets | ✅ Full | Direct partition inventories and realizing lists, with overlap and common-beta checks |
| Dense four-row endpoint and placement formulas | ✅ Full | Exact endpoint, end/middle, and tie comparisons on the parameter windows declared in the four threshold scripts |
| Six-negative minimum-six domain | ✅ Full | All strict endpoint orders through eight rows; all four-row two-negative cores of span at most eleven; complete six-row zero-free span-fourteen and full-board span-nine windows; bordering through eight rows.  The proof, not these windows, supplies the unbounded conclusion |
| Sharpness quartets and non-dense resonance | ✅ Full | Direct determinant identities, connected profiles, negative partitions, unit boundaries, and the ten-negative marked cell unions |
| At-most-two-negative endpoint law | ✅ Full | Every connected zero-free core of orders two through eight and span at most twice its order; three positive shifts, with higher-order rejecting controls |
| Saturated-column rigidity mechanism | ✅ Full | Representative component strata through six rows, seven margin fixtures, full-board unit windows at six through nine rows, and the explicit unbounded family through thirty rows.  The checks corroborate the proof and do not replace arbitrary-mate reconstruction |
| Ten-negative component budget | ✅ Full | All fifteen negative partitions at minimum seven and all four possible cofactor-order inventories; deleting the one-negative three-component case is rejected |
| Five-negative leaders and one-negative four-row replacements | ✅ Full | The full alternant identity in independent affine-label generators, symbolic rank corrections, and all declared strict/tied and symmetric parameter windows; omitted-term controls fire |
| Exceptional singleton-context classification | ✅ Full | Both generic coefficient tables, all linear row-matching cases including nongeneric ratios, and exact interface/locus checks; the symbolic proof supplies the unrestricted conclusion |
| Ten-negative quartet identities and border separation | ✅ Full | Both generic full-determinant equalities, exact degree-eight coefficients and every contributing permutation, literal family-A cell unions, and the full-board parity dictionary |

Here “Full” describes the advertised check, not a claim that a finite box proves the theorem.  The paper's unbounded classification is supplied by its algebraic proofs, not by certificate replay.  The finite profile boxes are not area censuses and need not contain every diagram of an area they reach; the separately labeled bounded-census script does enumerate its entire area window.

### Certificate contents

All data live in `certificates/` and are included in this supplement.

- `five_cross.json.gz`: 12 collision graphs, 22,217 nodes = 439 split nodes + 21,751 rational Farkas leaves + 27 family-implying leaves.
- `five_within.json.gz`: 42 collision graphs, 49,230 nodes = 742 split nodes + 44,368 rational Farkas leaves + 3,853 identity leaves + 267 rotation leaves.
- `staircase_counts.json`: every task ID and its expected counts, not just aggregate totals.
- `staircase_spaces.json.gz`: full task records and recorded equation spaces from the rational Fourier–Motzkin execution.
- `staircase_second.json.gz`: the corresponding records and spaces from the exact linear-real execution.

The staircase has 308 tasks, 183,367 nodes, and 6,183 recorded spaces = 5,038 identity + 1,119 reversal + 26 family.  There are 174,492 Fourier–Motzkin calls; the second backend has 116,921 satisfiable and 159,444 unsatisfiable queries.  These count search work and equation spaces, not distinct diagrams, classes, or disjoint regions.  Both executions have zero unclassified spaces and zero incomplete tasks.  Twenty-seven complete tasks have no equality spaces.

The collision verifiers reconstruct their input independently by border/column identities.  They import neither the certificate producer nor any solver.  Each infeasible leaf carries nonnegative rational multipliers whose sum is one and whose linear combination of the domain forms vanishes modulo the node equations.  Thus anyone can check the exclusion without trusting a solver's `unsat` answer.  Controls deliberately corrupt a multiplier, remove a successor, and change a terminal conclusion; every corruption must be rejected.

The retained staircase spaces are useful for inspection and cross-execution comparison, but inspecting their verdicts alone does not prove that the search was exhaustive.  The default harness therefore **reruns the complete matcher**.  Its task coverage and execution records remain part of the corroborating computation; none replaces a step in the manuscript's algebraic proofs.

## Dependencies

Refer to `requirements.txt`.  Four files assert nothing about the paper and are imported by the checks: `jacobi_trudi.py` (exact full-board polynomials and profile constructions), `formal_polynomial.py` (free complete-function polynomials), `staircase_matching.py` (the rational occurrence matcher) and `staircase_exact.py` (exact feasibility and the independent recognizer).  `check_composition_irreducibility.py` is the composition engine that four of the checks above import (so `run_all.sh` loads it); it is not run on its own, because the paper claims nothing about composition-irreducibility.  Run standalone (about 45 s), it replays the composition decision procedure and the cell-capped Schur-class census.  Beyond those dependencies, the default harness uses only the Python standard library.  The optional second backend needs `z3-solver==4.15.3.0`; it is not required to replay the two Farkas certificates or to run the default staircase search.

## License

MIT; see `LICENSE.txt`.  This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. J. Shields, *Skew Schur equivalence by Jacobi–Trudi negative count*, 2026.

Refer to the paper for references.
