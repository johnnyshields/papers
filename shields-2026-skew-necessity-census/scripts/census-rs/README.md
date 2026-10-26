# Computational supplement — connected skew Schur classes

An independent Rust census of connected skew diagrams up to translation, grouped by exact equality of their skew Schur functions.  The supported area bound is 35.  Completed areas, rather than the supported bound, appear in the table below.  Profiles are `(rows, gaps)`, with top-to-bottom row lengths and each gap equal to adjacent overlap minus one.

The census is exhaustive on completed areas.  It records every nonrotation class with every member, counts all other classes, and confirms surviving modular groups in the polynomial ring over the integers.  `roots_keys.py` calls the separate Python chart finders and checks proper charts and source-minimal keys on the resulting member lists.  These are finite computational results, not assertions at uncomputed areas.

## Installation

Rust 1.94 or later, Cargo, Python 3, and Linux utilities `timeout`, `nice`, and `prlimit` are required.  The default output directory is `/mnt/d/mvw-rust/`, configurable with `WORK`.  Set `SCRATCH` to local ext4 storage; build products and sort spills never belong on a Windows-mounted repository filesystem.

```sh
timeout 300s env SCRATCH=/home/shields/r167-lanes/_rust35 bash run.sh
timeout 172800s env FULL=1 SCRATCH=/home/shields/r167-lanes/_rust35 bash run.sh
```

The default computes through area 20 in seconds after compilation.  `FULL=1` reproduces the largest area in the completed-results table, not an unmeasured request for area 35.  `MAX`, `THREADS` (at most 16), `WORK`, `SCRATCH`, and `PYTHON_WORK` are configurable.  Before any area above 26, the driver requires a successful exact cross-check against the separate Python census checkpoints.  `PYTHON_WORK` selects their directory.  Generating those checkpoints is a separate prerequisite, using `verify_classes.py` in the parent scripts directory.

For a detached, resumable computation, build first, then use `timeout 20s env MIN=27 MAX=30 bash launch.sh`.  It uses `nohup`, a hard timeout, niceness 10, and a 24-GiB address-space limit.  Logs are first spooled locally and copied to the output directory as retrying atomic snapshots.  A final JSON checkpoint is written after each row-multiset shard.  Restarting reuses complete checkpoints; interruption loses at most the in-progress shard on each worker.  Do not run two writers against the same output directory.

## Scripts by section

| File | Computation |
|---|---|
| `src/model.rs` | Profiles, independent enumeration, reflection, packing, transfer and row-multiset counts |
| `src/algebra.rs` | Sparse modular determinants and exact exterior-algebra polynomial expansion |
| `src/census.rs` | Bounded-memory sorting, exact refinement, per-shard and per-area counts |
| `src/controls.rs` | Independent small enumeration, exact census, perturbation and collision controls |
| `cross_check.py` | Full comparison with trusted Python checkpoints, including every member set |
| `roots_keys.py` | Measured calls to both complete Python chart finders, roots, and class keys |
| `plan.py` | Measured per-billion profile rates and explicitly labeled projections |
| `campaign.py` | Sequential complete areas with a persistent deadline, projections, and automatic table publication |
| `summarize.py` | Regenerate and check the measured table from result files |
| `run_logged.py` | Local log spool and retrying atomic publication |

## Why the partition is exact

1. Every connected skew diagram has positive row lengths and an adjacent overlap between one and the smaller row length.  Conversely these choices give weakly descending left and right row endpoints and a connected skew diagram.  Enumerating integer partitions, distinct row orderings, and every legal gap therefore enumerates each profile once.  Counts are checked against both a remaining-row-multiset dynamic program and an independent area transfer recurrence.  Reflection-fixed counts are checked separately by closing half profiles with a middle row or middle gap.
2. Row lengths as a multiset are a Schur invariant.  All consecutive-row overlap partitions are Schur invariants by [1, Corollary 8.11, p. 150]; the definition is [1, Definition 8.2, p. 146].  Section 8 concerns connected diagrams, which is exactly the domain enumerated here.  These statements and locators were checked in the published article.  An additive hash of overlap partitions is used only for refinement: a hash collision can retain extra candidates, never separate equal invariants.  No unproved endpoint invariant is used.
3. Rotation reverses rows and gaps.  Its Jacobi–Trudi matrix is the transpose of the original matrix conjugated by the reversal permutation.  Thus rotation preserves the determinant.  Exactly the lexicographically smaller representative of each orbit is evaluated.
4. The first grouping key is evaluation at a fixed point modulo \(2^{61}-1\).  Collisions are refined by overlap data and a second fixed point modulo \(2^{61}-31\).  Both primes are checked with deterministic 64-bit Miller–Rabin.  Every evaluation is a ring homomorphism, so unequal evaluations prove inequality without a probabilistic assumption.  A modular collision is **not** accepted as equality.
5. Every surviving group of two or more rotation orbits is expanded exactly in \(\mathbb Z[h_1,\ldots,h_{35}]\).  Bottom-to-top exterior multiplication tracks column subsets and signed monomials, giving the Jacobi–Trudi determinant by the alternating multilinear definition.  Equal coefficient maps are equivalent to equal symmetric functions because the complete homogeneous generators are algebraically independent.  All coefficient arithmetic is checked; overflow aborts rather than returning a result.  In fact, column supports are nested prefixes of lengths \(c_j\), so there are \(\prod_{j=0}^{n-1}(c_j-j)\) nonzero Leibniz terms.  There are at most \(N-1\) nonzero entries strictly below the diagonal: in row \(i\), their distinct indices \(y_j\) lie in the \(r_i\)-element interval \((y_i,x_i]\).  Since \(t\le 2^{t-1}\), the number of terms is at most \(2^{N-1}\); every partial matching of bottom rows extends to a full matching, so this also bounds intermediate coefficients.  At \(N\le35\) this is far below the checked `i128` range.  The support bound is asserted in every exact expansion.  Polynomial evaluations are also checked against the second modular determinant.  Different groups are separated by a proved invariant or an evaluation, and each retained part is confirmed exactly.

The modular algorithm is not the Python elimination algorithm.  It chooses the lowest available row in each column.  Most pivots are unchanged original entries, whose inverses are precomputed; this exploits the Jacobi–Trudi zero pattern without division-free scaling.  Exact confirmation uses iterative exterior multiplication, not the Python recursive Laplace implementation or its polynomial library.  The numeric matrix workspace is thread-local.  Column supports are nested prefixes; elimination in a column reads only rows in its prefix, which is contained in every later column's prefix.  Every accessed entry is therefore freshly overwritten for the current profile, and structural zeros never need to be read or cleared.  A fresh full census through 26 using this workspace agrees with Python in every count and member set; its additional certificate is `results/workspace-regression/cross-check.json`.

## Memory and resumability

A record occupies 16 bytes: a 61-bit modular value and a reversible 64-bit profile code.  The low 35 bits encode cuts after rows; the remaining bits encode gaps in mixed radix.  The product of gap radices is bounded by the product of row lengths, at most \(3^{35/3}<2^{19}\), so the code fits.  The default cap is 16 million records per worker (256 MB), with at most 16 workers.  Larger row-multiset shards become sorted local runs and are merged in key order; equal keys crossing run boundaries are processed together.  Thus the largest shard need not fit in memory.  Final JSON files use temporary files, file `fsync`, atomic rename, and bounded exponential I/O retries.

Hot-disk reservations bound simultaneous spill payloads to 384 GiB by default, or 75% of currently free hot storage, whichever is smaller (`--spill-gib` is configurable).  A shard with \(P\) profiles has at most \(\lfloor(P+\min(P,S_N))/2\rfloor\) rotation orbits, where \(S_N\) is the separately computed number of reflection-fixed profiles at its area.  The scheduler reserves 16 bytes times this upper bound before processing a spilling shard and releases the reservation only after its spills are discarded and its checkpoint is published.  This prevents 16 large area-35 shards from exhausting the local disk.  The budget concerns record payloads; the free-space margin also covers filesystem metadata and unrelated work.  Merge readers use 256 KiB per run.  Resource summaries record each area's reservation high-water mark.  The shared-machine default also reserves at least 100 GiB of free space: the effective payload budget leaves 128 GiB free, and each sorted-run write waits if free space falls below 120 GiB.  The 20-GiB write margin exceeds all 16 simultaneous maximum-size run writes.  `CENSUS_MIN_FREE_GIB` configures this policy on other machines (zero disables the free-space guard); the reported shared-machine runs use 100.  Exhaustive root-sample caches are discarded before forking root workers.

The full row-multiset size calculation is in `results/scale.json`.  Area 35 has 1,563,756,371,425 profiles in 14,883 row multisets; its largest multiset has 12,235,213,858 profiles.  These are enumeration sizes, not completed class counts.  Per-area timing projections are separate files and are not promoted to results.

## Chart-finder snapshot

The pinned copy is an unmodified snapshot of the paper's finder taken at **2026-10-03 13:10:39.810055 UTC**.  The roots/key adapter imports these immutable copies, defines the score directly as \((N\bmod q, q+N\bmod q)\), and cross-checks the complete chart sets with the independent window finder.  It imports no live paper verification driver.  The snapshot manifest is also recorded in `results/finder-snapshot.json`, and every roots/key checkpoint records the dependency checksums; a checksum change invalidates reuse.

| Snapshot file | SHA-256 |
|---|---|
| `skew_compose.py` | `b10ca1ac2aaf83453d7069fc8e939125c32ff4461d0b5613b2a57e75eb584b21` |
| `skew_core.py` | `8bdab057287c67d3a8e0ec9526eec1c832ad68875f495f535931aef598dd5247` |

## Verification and measured results

**Full cross-check through 26: PASS.** Profiles, rotation orbits, classes, complete size histograms, and all nonrotation member sets agree area by area with the independent Python census.  Through 23 there are 1,104 nonrotation classes and 4,424 members.  `results/cross-check.json` contains the comparison and file checksums.  A deliberately changed class count is rejected.

Every census invocation fires the controls: an independent cut-subset enumeration and exact-only census through area 9, both modular evaluations against exact polynomials, rotation and packing checks, the known 9-cell ribbon pair, an unequal perturbation, a planted wrong value, a deliberately collapsed evaluation split by the exact step, and forced external spills compared with in-memory sorting.  The ordinary runs report actual exact-refinement counts and actual false merges, independently of the planted controls.  A separate four-worker run through 20 with a 10,000-record cap forced 2,630,107 records through external sorting and reproduced every mathematical output and exact-confirmation count from the 16-worker run; see `results/validation-determinism.json`.

Machine: AMD Ryzen 9 9950X3D, 16 cores, shared load; at most 16 census worker threads, niceness 10, address-space limit 24 GiB.  When four root-check workers run concurrently, the census uses 12 workers; each area records its actual thread count.  Times include shard processing and checkpoint publication.  Peak RSS is the process high-water mark through that area, not an isolated per-area allocation measurement.  The result files retain exact seconds and KiB.

<!-- BEGIN MEASURED TABLE -->
| N | Profiles | Rotation orbits | Classes | Nonrotation classes | Members | Seconds | Peak MiB |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 0 | 0 | 0.023 | 3.6 |
| 2 | 2 | 2 | 2 | 0 | 0 | 0.021 | 3.7 |
| 3 | 4 | 3 | 3 | 0 | 0 | 0.024 | 3.7 |
| 4 | 9 | 7 | 7 | 0 | 0 | 0.030 | 3.7 |
| 5 | 20 | 12 | 12 | 0 | 0 | 0.037 | 3.8 |
| 6 | 46 | 29 | 29 | 0 | 0 | 0.053 | 3.8 |
| 7 | 105 | 57 | 57 | 0 | 0 | 0.073 | 3.9 |
| 8 | 242 | 135 | 134 | 1 | 4 | 0.103 | 3.9 |
| 9 | 557 | 289 | 288 | 1 | 4 | 0.143 | 4.0 |
| 10 | 1,285 | 675 | 674 | 1 | 4 | 0.202 | 4.0 |
| 11 | 2,964 | 1,506 | 1,503 | 3 | 12 | 0.231 | 4.1 |
| 12 | 6,842 | 3,497 | 3,490 | 7 | 28 | 0.310 | 4.2 |
| 13 | 15,793 | 7,952 | 7,947 | 5 | 20 | 0.447 | 4.4 |
| 14 | 36,463 | 18,407 | 18,395 | 12 | 48 | 0.576 | 4.6 |
| 15 | 84,187 | 42,222 | 42,193 | 29 | 116 | 0.711 | 4.9 |
| 16 | 194,388 | 97,601 | 97,580 | 21 | 84 | 1.012 | 5.5 |
| 17 | 448,847 | 224,720 | 224,686 | 34 | 136 | 1.265 | 6.4 |
| 18 | 1,036,426 | 519,154 | 519,073 | 81 | 324 | 1.629 | 7.7 |
| 19 | 2,393,208 | 1,197,289 | 1,197,225 | 64 | 256 | 2.185 | 10.4 |
| 20 | 5,526,198 | 2,765,275 | 2,765,141 | 132 | 532 | 2.754 | 13.9 |
| 21 | 12,760,671 | 6,381,918 | 6,381,706 | 212 | 848 | 3.520 | 20.1 |
| 22 | 29,466,050 | 14,738,052 | 14,737,862 | 190 | 760 | 4.370 | 29.0 |
| 23 | 68,041,019 | 34,024,164 | 34,023,851 | 311 | 1,248 | 5.625 | 84.1 |
| 24 | 157,115,917 | 78,569,574 | 78,568,933 | 639 | 2,560 | 8.756 | 168.8 |
| 25 | 362,802,072 | 181,409,476 | 181,408,955 | 519 | 2,080 | 22.307 | 476.4 |
| 26 | 837,759,792 | 418,906,723 | 418,905,913 | 808 | 3,236 | 65.478 | 582.8 |
| 27 | 1,934,502,740 | 967,270,861 | 967,269,326 | 1,531 | 6,132 | 139.126 | 967.3 |
| 28 | 4,467,033,943 | 2,233,578,933 | 2,233,577,372 | 1,557 | 6,236 | 681.336 | 1075.1 |
| 29 | 10,314,998,977 | 5,157,544,498 | 5,157,542,391 | 2,101 | 8,416 | 454.669 | 2942.5 |
| 30 | 23,818,760,154 | 11,909,523,169 | 11,909,519,170 | 3,989 | 15,976 | 1078.473 | 3979.2 |
| 31 | 55,000,815,222 | 27,500,511,548 | 27,500,507,933 | 3,611 | 14,452 | 2121.864 | 3983.4 |
| 32 | 127,004,500,762 | 63,502,580,828 | 63,502,574,667 | 6,141 | 24,604 | 3386.288 | 4052.1 |
| 33 | 293,270,987,832 | 146,635,733,927 | 146,635,724,175 | 9,742 | 38,988 | 12126.443 | 4204.0 |
| 34 | 677,203,347,266 | 338,602,436,712 | 338,602,426,758 | 9,944 | 39,796 | 49461.836 | 2296.2 |
| 35 | 1,563,756,371,425 | 781,878,739,939 | 781,878,724,470 | 15,451 | 61,840 | 90178.310 | 2682.9 |

| N | Rooted members | Classes with source-minimal key | Band/window agreement | Seconds |
|---:|---:|---:|:---:|---:|
| 27 | 6,132 | 1,531 | all members | 59.965 |
| 28 | 6,236 | 1,557 | all members | 66.157 |
| 29 | 8,416 | 2,101 | all members | 116.099 |
| 30 | 15,976 | 3,989 | all members | 88.019 |
| 31 | 14,452 | 3,611 | all members | 89.855 |
| 32 | 24,604 | 6,141 | all members | 186.083 |
| 33 | 38,988 | 9,742 | all members | 274.900 |
| 34 | 39,796 | 9,944 | all members | 968.720 |
| 35 | 61,840 | 15,451 | all members | 437.839 |
<!-- END MEASURED TABLE -->

Per-area `results/area-NN.json` files contain the full histogram and every nonrotation member.  The configurable output directory additionally contains per-shard checkpoints, run logs, and full roots/key witnesses.  The small `results/roots-keys-NN.json` files state the achieved root/key coverage, finder measurements, controls, and timing.  A missing roots/key file means that step has not been established for that area.  Source-minimality uses the completeness theorems for the called Python finders; explicit charts are checked by legal marks, recomposition, the private-diagonal identity, and the size bound.  The independent window finder is compared with the band finder on **every** nonrotation member; the slower exhaustive subdiagram finder is compared on 32 evenly spaced members per area.  The window finder includes both empty-mark readings, whereas the band finder includes only the horizontal reading.  Each empty vertical chart is converted to a horizontal chart by antitransposing its outer.  Within the window output these converted charts must equal its own empty horizontal chart set, and every converted chart is recomposed.  Nonempty marks are never normalized this way.  The full normalized chart sets, including outer, inner, both marked copies, attachment case, and period, must agree.  Result files separately count the extra raw empty vertical charts.

## Dependencies

Rust dependencies are pinned in `Cargo.lock`.  The census itself requires only Rayon and Serde/JSON.  Roots and keys also require the checksummed Python snapshot and its dependencies from the parent `requirements.txt`, plus the independent `w_roots` module selected with `roots_keys.py --window-script`.  Its default is the sibling skew-equivalence scripts' `check_cdp2_vOIM_lib.py`.  All external source files are called read-only, with bytecode writing disabled.

## License

This directory is licensed under the MIT License; see `LICENSE.txt`.
This directory is also subject to the patent and trademark terms in the
LICENSE.txt at the root of the repository.

## References

1. V. Reiner, K. M. Shaw, and S. van Willigenburg, *Coincidences among skew Schur functions*, Advances in Mathematics 216 (2007), 118–152.

Refer to the paper for references.
