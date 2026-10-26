# Computational supplement — Skew Schur classes through thirty-five cells and composition necessity

Cross-check scripts for `shields-2026-skew-necessity-census.tex`.  They enumerate every connected skew diagram up to a given area, group the diagrams into Schur classes, search every member of every nonrotation class for marked compositions, compare the keys of minimal compositions, and build the factorizations that the McNamara–van Willigenburg conjecture asks for.  Modular evaluation of Jacobi–Trudi determinants is used only to separate classes; every class with more than one rotation orbit is confirmed by exact polynomial arithmetic, in two independent ways, and every composition is recomposed cell for cell.  All randomness uses fixed seeds.

The paper proves, for every connected skew diagram of at most 35 cells, the complete list of Schur classes with more than one rotation orbit; that every member of these classes is a proper composition satisfying Hypotheses I–IV; that Schur-equal diagrams share the keys of their minimal compositions; and, from these, the necessity direction of McNamara and van Willigenburg's Conjecture 5.7 [1], together with its class-size clause.  The Python scripts here carry the computation through 26 cells.  Two independent Rust programs carry it through 35: `census-rs/` computes the census, and `charts-rs/` computes every chart by forward generation and runs every chart, key, factorization and class-size check on it.  Each has its own README.

The main theorem of the paper is computer-assisted: its proof rests on the computation these scripts perform, and the paper proves the algorithms correct.

## Installation

Use Python 3.10 or later:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
bash run_all.sh
```

The default run takes the census through 16 cells and every check on it, and finishes in about a minute.  `FULL=1 bash run_all.sh` takes the census through 26 cells, runs the chart, key and factorization checks on all of it, and checks the class-size clause on every diagram of at most 22 cells; `python3 verify_conjecture.py --csmin 23 --csmax 24` extends that check to 24 cells.  Set `SKEWBASE_JOBS` to the number of worker processes (default 4) and `SKEWBASE_WORK` to a directory for the per-area checkpoints (default `_work/` here).  The census is resumable: each area is saved when it completes.

Measured on an AMD Ryzen 9 9950X3D (16 cores, 32 threads, 61 GB RAM, shared with other jobs) with twelve worker processes: the census through 26 cells took 43 minutes, every process staying below 1.1 GB resident (1.7 GB in the exact confirmation that follows, which took a further 8 minutes on eight processes); the chart, key and factorization checks on the 3,070 nonrotation classes took about 4 minutes; the class-size check over every diagram of at most 22 cells took 16 minutes, and its extension to 23 and 24 cells took 88 minutes.

Assertions stop the suite on a failure.  Successful completion ends with `ALL PASS`.

## Scripts by section

| Where | Paper section | Script | Checks |
|---|---|---|---|
| §2 | Profiles and Schur invariants | `verify_enumeration.py` | Profiles against all fixed polyominoes through 10 cells (11 in the full run); the row-appending and palindromic DPs against direct enumeration; the table of counts |
| §3 | The census | `verify_classes.py` | The sharded census and its exact confirmation; enumeration counts and self-rotational counts against the DPs; controls: exact-only grouping through 11 cells, a known ribbon pair, gap swaps, a corrupted evaluation, two exact instruments |
| §4 | Marked composition and the conjecture | `check_mvw_examples.py` | McNamara–van Willigenburg's Examples 3.12 and 3.13 and Remark 5.8; Lemma 3.19(ii) and the empty gauge; the marks against a brute-force reading of Hypotheses I–IV |
| §5 | The geometry of a chart and two complete searches | `verify_roots.py` | Both searches on every profile of 2..10 cells (12 in the full run) and on forward compositions; terminal rigidity on every member of every nonrotation class; private diagonals and the size bound on every chart; rotation of charts; controls: a rootless hook, a misaligned search, a 13-cell outer, random profiles |
| §6 | Keys and necessity | `verify_keys.py` | Costs, minimal charts and key sets on every member; equal key sets within every class; the gauge-reduced key; a corrupted key splits classes |
| §6, §7 | Keys and necessity; the computation | `verify_conjecture.py` | Explicit common factorizations for every ordered pair in every nonrotation class; factor reversals stay in the class; every irreducible factorization and the class-size clause on the nonrotation classes and on every diagram up to a given area |

| Directory | Checks |
|---|---|
| `census-rs/` | The census in Rust through 35 cells, compared with the Python census in every count and every class member through 26 |
| `charts-rs/` | Forward generation of every proper chart through 35 cells; both chart searches, keys, presentations, factor reversals and the class-size clause, reproducing every published Python table through 26 |

## Coverage by section

| Section | Computational scope |
|---|---|
| Profiles | Bijection with skew polyominoes through 10 cells (11 in the full run); counts through 30 cells by DP, through 16 by direct enumeration |
| The census | Every connected diagram of at most 16 cells by default, 26 in the full run; exact confirmation of every class with more than one rotation orbit |
| Composition | The published examples; every composition of outers of at most 5 cells with marked inners of at most 6; marks of every inner of at most 9 cells against the brute-force reading |
| Chart searches | Every profile of 2..10 cells (12 in the full run); forward compositions over the factor boxes stated in the script; every member of every nonrotation class in the census range |
| Keys | Every member of every nonrotation class in the census range |
| The conjecture | Every ordered pair of every nonrotation class; the class-size clause on those classes, and on every diagram of at most 12 cells by default, 22 in the full run, 24 with the extension above |

In Python, the census range, the chart searches on the census and the key comparison are complete through 26 cells, and the class-size clause through 24.  With the Rust programs, all of them, the class-size clause on every diagram with a proper chart included, are complete through 35 cells.

## Dependencies

Refer to `requirements.txt`.  `numpy` vectorizes the census enumeration and the modular determinant evaluation.  Every modular product is of two residues below \(2^{31}-1\) in `int64`, so nothing overflows, and the evaluation is a fingerprint rather than a proof: a profile meeting a zero pivot is recomputed by exact integer elimination (`det_mod_exact`), and any equality it suggests is confirmed on the exact Jacobi–Trudi polynomials.  `python-flint` supplies the second, independent exact polynomial routine.

| Component | Used by | Description |
|---|---|---|
| `skew_core.py` | every script | Profiles, enumeration, modular evaluation and the two exact determinant routines |
| `skew_compose.py` | `check_mvw_examples.py`, `verify_roots.py`, `verify_keys.py`, `verify_conjecture.py` | Marks, composition and the two chart searches |

## License

The code is licensed under the MIT License; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

[1] P. R. W. McNamara and S. van Willigenburg, *Towards a combinatorial classification of skew Schur functions*, Trans. Amer. Math. Soc. 361 (2009), 4437–4470.

Refer to the paper for references.
