# Computational supplement — charts, keys and class sizes on the census

A Rust implementation of every chart-level check of the paper, independent of the census.  It produces every proper chart of every connected skew diagram up to a given area by forward composition, checks the class-size clause of McNamara and van Willigenburg's Conjecture 5.7 [1] on every diagram with a proper chart, and runs on every member of every nonrotation class both chart searches of the paper, the key comparison, the explicit common factorizations and the factor-reversal check.

The proofs in the paper are noncomputational and do not depend on the code here.

## Installation

Rust 1.94 or later and Cargo are required; Python 3 is needed only for the cross-check against the pinned Python.

```sh
cargo build --release
target/release/skew-charts validate --max 14
target/release/skew-charts run --min 8 --max 26
python3 cross_check_python.py --binary target/release/skew-charts --max 11
```

`run` reads the census class lists from `../census-rs/results/area-NN.json` (`--census`) and writes `results/size-through-NN.json` and one `results/members-NN.json` per area (`--out`).  `--threads` sets the worker count (default 4, at most 16); `--no-s` skips search S.  Through 26 cells `run` takes seconds; through 35 cells it took about 25 minutes on four threads, most of it search S on the 38,988 members at area 33.

Every check is an assertion, and a run that completes ends with `ALL PASS`.

## What is checked

| Command | Checks |
|---|---|
| `validate --max M` | On every connected profile of 2..M cells, search B, search S and the forward generation return the same chart set, and every chart passes the chart checks below |
| `run --max B` | Forward generation through B.  For every connected diagram of at most B cells with a proper chart: every irreducible factorization is enumerated, \(\lvert[F]\rvert=2^r\) with the same \(r\) for each, the marked and unmarked symmetry counts agree, and the reversal variants of each factorization are exactly the class |
| `run --min A --max B` | On every member of every nonrotation class of A..B cells: search B, search S and the generation agree; every chart is recomposed and its mark re-derived, and the private-diagonal identity, the size bound and the cost formula are asserted; every chart rotates to a chart of the rotation; all members of a class share the keys of their minimal charts, which carry one key modulo the ordinary gauge; every ordered pair has an explicit common factorization, recomposed on both sides; every factor reversal of every chart stays in the class; the class-size clause |
| `check_sixteen.py` | The paper's class of at least sixteen: the 20-cell eight-member class composed with the ribbon \((1,2;0)\) (case (c), period 2) and with its rotation gives 16 distinct connected diagrams of 48 cells, the smallest such construction over inners of at most 6 cells and period at most 3 |
| `cross_check_python.py` | On every connected profile of 2..M cells, the legal marks and the search-B charts equal those of the pinned Python, as sets |

Through 26 cells, `run` asserts every row of the per-area tables published by the Python verification in the parent directory, and the two control counts (2,103 classes split by a transposed outer, 130 by keys of all charts); through 24 it asserts the Python's count of diagrams with a proper chart.

## Forward generation

A proper chart \(F=D\circ_\omega E\) of period \(q\) and width \(w\) satisfies \(\lvert F\rvert\ge q\lvert D\rvert+w\), the size bound of the paper.  It also satisfies \(3\lvert E\rvert\le2\lvert F\rvert-1\).  The copies of the cells of \(D\) on its least and greatest contents both lie in \(F\).  They are disjoint unless \(N_D=2\), and then they meet only on the contents \([q,N_E-1]\), in at most \(\min(a,c)\) cells, where \(a\) and \(c\) count the cells of \(E\) on \([0,w-1]\) and \([q,N_E-1]\).  Since \(E\) has a cell on each of the \(q-w\ge1\) contents \([w,q-1]\), \(a+c\le\lvert E\rvert-1\).  So composing every connected inner of at most \((2B-1)/3\) cells, with each of its legal marks, with every connected outer allowed by the size bound produces every proper chart of every diagram of at most \(B\) cells.  Both bounds are also asserted on every chart produced.

The legal marks are found as in the pinned `skew_compose.py`, except that only the subdiagrams that can be a copy of \(W\) are generated: those containing the southwesternmost (northeasternmost) cell on the contents that Hypothesis II permits.

## Dependencies

Rust dependencies are pinned in `Cargo.lock`: Rayon, rustc-hash and Serde/JSON.  The cross-check imports the checksummed Python snapshot in `../census-rs/_pinned/`.

## License

This directory is licensed under the MIT License; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. P. R. W. McNamara and S. van Willigenburg, *Towards a combinatorial classification of skew Schur functions*, Transactions of the American Mathematical Society 361 (2009), 4437–4470.

Refer to the paper for references.
