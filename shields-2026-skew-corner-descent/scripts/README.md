# Computational supplement — Corner descent and repeated inners in skew Schur compositions

Cross-check scripts for `shields-2026-skew-corner-descent.tex` construct English cell diagrams, enumerate legal marked end subsets, and compare exact polynomials in algebraically independent complete symmetric functions.  Integer subset determinants, SymPy calculations, and a separate cell model provide distinct checks.  Original Jacobi–Trudi expansion, cyclic enumeration, and raw differentiation test the determinant coefficients without substituting an eliminated response model for the original matrix.  Marked composition uses the conventions of [2].

The paper proves exact cofactor transport under Hypotheses I–IV, bounds the normalization spans, and reduces source-minimal period comparison to discrete-interior outers.  On a separately specified ordinary complete-window domain, exact rational residue matching forces a bounded-order original determinant defect or a specified literal repeated inner.  Function extraction does not establish that window domain or residue matching.  Connected-skew irreducibility uses the corrected argument of [1].

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Use Python 3.10 or later:

```sh
python3 -m pip install -r requirements.txt
bash run_all.sh
```

Every check uses exact arithmetic and exits unsuccessfully on a failed assertion.  The full suite ends with `ALL PASS`.  No private library, network connection, or sibling script is required.

## Scripts by section

| Where | Paper section | Script | Test |
|---|---|---|---|
| §2 | Corner cofactors and common cores | `verify_corner.py` | Full Jacobi–Trudi coefficient versus cell-set interior; northwest/southeast translation; area and component-span bounds |
| §2, §2 Lem 2.1 | Corner cofactors and common cores | `check_corner_structure.py` | Span of products and of disconnected diagrams; largest index only in entry \((1,n)\); decomposition of every connected skew Schur polynomial by its top generator; row-length monomial; irreducibility over \(\mathbb Q\) by factorization and over three finite fields by the affine criterion; discrete-interior criterion on row profiles |
| §2 Lem 2.1 | Corner cofactors and common cores | `check_cofactor_primitivity.py` | Permutation expansion versus extreme minor; integer content and affine coefficient gcd over the rationals and three finite fields; two failing controls |
| §2 Lem 2.3 | Common-core divisibility | `check_shared_core.py` | Symbolic block-determinant divisibility for every row and column choice; actual joined diagrams, exact polynomial divisibility; controls with generic lower blocks and same-end extensions |
| §2 Lem 2.3, §6 | Common-core divisibility, equal windows | `check_overlap_precision.py` | Actual shared-window congruence and its precise normal order, not full corner precision |
| §3 | Marked inners and finite end caps | `verify_transport.py` | End subsets checked against I–IV; row amalgamations, cap decomposition, every normalization-span bound |
| §3 Lem 3.1 | Marked inners and finite end caps | `check_mark_structure.py` | Local mark properties, cap decomposition and hatted-mark identity from cell sets; erosion of row unions; Hypotheses II, III and IV shown necessary, I reported as not changing those conclusions |
| §3, §4 | Marked inners; cofactor transport | `check_cell_model.py` | Brute end-subset enumeration on a separate cell model; literal row decompositions; exact polynomial normalization and child comparisons; multiplicities by division; exponent minima; empty-overlap middle-span bound attained by two-row rectangles |
| §4 | Cofactor transport under composition | `verify_transport.py` | Direct parent minor versus independently constructed child factors; exact exponents; mixed supplemental copies |
| §4 | Cofactor transport under composition | `check_without_v.py` | Ordinary mark outside V, nonconstant hatted mark and caps, transport under connected outers |
| §4 | Cofactor transport under composition | `check_witness_determinant.py` | Hand-entered SymPy determinant for the non-V witness, with no geometry imports |
| §3 Rmk 3.2, §4, §4 Rmk 4.3 | Non-V family and ordinary gauge | `check_non_v_family.py` | The family for every \(k\) in a range: maximality, failure of V, factors, Jacobi–Trudi expansion, row and rectangle transport, finite caps versus full hatted marks; vertical reading of the \(k=4\) member |
| §4 Rmk 4.3 | Ordinary gauge remark | `check_mark_scope.py` | V-failure census, separate mixed/empty conventions, ordinary gauge pairs, empty-edge countercontrol |
| §5 | Period comparison and polynomial obstructions | `verify_periods.py` | Actual periods versus factored corners; congruence and multiplicity controls; descent inequalities; beta/alpha residual fixtures and mutations |
| §5 Lem 5.1 | Period comparison | `check_root_periods.py` | Complete root lists for small parents; source-minimality under changed outers; line-inner countercontrol |
| §5 Prop 5.5, §5 Lem 5.6 | The nonempty discrete residual | `check_residual_pairs.py` | Literal reassociation pairs of charts of one parent: transported child, span relation and area; every chart pair with equal inner functions, spans and corners: isolated-cell count, row gaps and strict bounds |
| §6 Thm 6.1, §7 Lem 7.4, §7 Cor 7.6, §8 Thm 8.6 | Equal windows; original coefficients | `check_original_defect_family.py` | Every square-tile edge word in a range: residue matching, derivative identity in the resolving generator for every length, order of the defect; perturbation control |
| §7 Lem 7.1, §7 Thm 7.3, §8 Lem 8.1, §8 Thm 8.6, §9 Thm 9.1 … §9 Cor 9.4 | Cyclic inventories; scalar refinements | `check_dual_scalar.py` | Dual identities, gcd reparametrization, joint non-vanishing, automatic locus, AM–GM and the two signed-support chains for arbitrary integer data; transition-parity step; controls |
| §7 Lem 7.2, §7 Lem 7.5 | Cyclic inventories | `check_gap_cycles.py` | Mean, maximum and equality of cyclic gap sums with periodicity; constant window counts of occurrence masks force period \(r\) |
| §7 Lem 7.1, §8 Lem 8.2 | Cyclic inventories; endpoint profiles | `check_cyclic_inventory.py` | Every cyclic start, count/complement identities, automatic last-detector zeros, live inverse jets, raw profile derivatives, and the smallest normal inventories |
| §7 Rmk 7.7 | Cyclic inventories and original coefficients | `check_original_transfer.py` | Original five-square determinants versus the signed short-bin derivative and affineness in the resolving generator |
| §8 Lem 8.2 | Endpoint profiles | `check_profile_derivative.py` | Raw derivative of an interval response against the profile product for every generator; chart derivative; internal-term control |
| §8 Lem 8.7 | The full-window boundary | `check_full_window_boundary.py` | Every diagram in a range with equal full windows and matching private cuts is an empty \(b\)-copy row or column composition; the neighboring width is not |

Each verification script states its finite domain in its source and prints its counts.

## Coverage by section

These statuses describe finite computational coverage, not the validity or generality of the paper's proofs.  **✅ Full** means the script's stated finite box is completely checked, not an all-size proof.

| Section or result group | Status | Scope |
|---|---|---|
| Corner coefficient and interior bounds | ✅ Full | Complete stated box; additional square; wrong-sign and wrong-generator controls |
| Characteristic-independent cofactor lemma | ⚠️ Partial | Every connected diagram through nine cells; integer content and affine gcd over QQ, GF(2), GF(3), GF(5); no all-size or all-field computational proof |
| Common-core divisibility | ✅ Full | Generic block identity for the stated block shapes; actual joined diagrams through the stated range; one full-window precision control |
| Marked inners and finite end caps | ✅ Full | All attachment cases and both empty readings in the stated domain; every bound has a nonvacuous firing control |
| Cofactor transport under composition | ✅ Full | All connected outers in the stated domain; non-V witness separately checked by SymPy; non-V family for a range of \(k\) |
| Period comparison and polynomial obstructions | ⚠️ Partial | Polynomial tests, descent arithmetic, discrete geometry, literal and searched residual pairs; bounded complete root lists; descent and source-minimality over all parents are consequences of cited gluing results and are not computed |
| Equal windows and the determinant defect | ⚠️ Partial | Square-tile family and the five-square example from the original matrices; no general detector-or-root certification |
| Actual responses and residue classes | ⚠️ Partial | Residue matching and exponent sums on the square-tile family; elimination, classifier and exposure lemmas are not checked as stated |
| Cyclic inventories and original coefficient transfer | ⚠️ Partial | Dual identities, nonvanishing and signed-support inequalities for arbitrary integer data; transfer identities on the square-tile family |
| Endpoint profiles, early recovery and closure pinning | ⚠️ Partial | Profile derivative identities; early recovery, closure pinning and the normal interface are not computed |
| Full-window boundary | ✅ Full | Every connected diagram in the stated range |
| Scalar and geometric refinements | ⚠️ Partial | Scalar theorem, automatic locus and signed-support corollaries on integer data; cut-independent and row-pencil geometric statements are not computed |
| Concluding remarks | — | Qualitative |

## Dependencies

Refer to `requirements.txt`.  Python 3.10 or later and a POSIX shell are required.

| Component | Used by | Description |
|---|---|---|
| `diagram_tools.py` | `verify_corner.py`, `verify_transport.py`, `verify_periods.py`, `check_corner_structure.py`, `check_shared_core.py`, `check_mark_structure.py`, `check_without_v.py`, `check_non_v_family.py`, `check_mark_scope.py`, `check_residual_pairs.py`, `check_full_window_boundary.py` | Cell geometry and exact free-complete-function polynomial arithmetic, built once for the scripts sharing it |

## License

The code is released under the MIT License; refer to `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. F. Barekat, V. Reiner, and S. van Willigenburg, *Corrigendum to “Coincidences among skew Schur functions”*, Advances in Mathematics 220 (2009), 1655–1656.
2. P. R. W. McNamara and S. van Willigenburg, *Towards a combinatorial classification of skew Schur functions*, Transactions of the American Mathematical Society 361 (2009), 4437–4470.

Refer to the paper for references.
