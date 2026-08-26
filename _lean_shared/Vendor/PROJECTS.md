# External Lean projects — the surveyed list

The projects looked at before writing Lean of our own, with what each was judged on and the
verdict.  `/lean-check`'s "look before building" step reaches this file after `Shields`, `Vendor`,
the pinned Mathlib and Mathlib's open PR queue; **this is the fifth place to look, and it is a
list, not a search** — a project not on it has not been assessed, and adding one is a row here.

Surveyed against Lean `v4.33.0-rc1` / Mathlib `8e45b0548034eeda677a64e1e0b07837390835b6`.
Checkouts live in `<root>/tmp/leanrepos/` (gitignored); re-clone from the URL rather than
expecting them to be present.

Two sweeps so far, and the licence check has since been re-run a third time on every
blocked row — `TotallyPositive`, `strongpnt`, `RiemannHypothesisCurves`, `CrouzeixConjecture`,
`cofinite-derivative-zeros`, `cross-boundary-moment-kernels` and `SymmetricFun` — with **none
changed**, `cross-boundary-moment-kernels` still deferring its licence despite active commits.
The second sweep re-ran that check and widened the net: 900 repositories from the GitHub repository search across
three star bands, cut to the 611 carrying a licence at all, then a code search by *statement
shape* over all public Lean.  That second axis is what found the sector core, which no
description-level filter would have surfaced: it sits in a computer-algebra package whose
README is about root isolation.

## The five gates a project passes before anything is copied

1. **Licence.** A permissive licence has to be *granted*, in a `LICENSE` file or in so many words
   in the README. **No licence means all rights reserved**, and a repository being public grants
   nothing. This gate alone stops the most topically relevant project on the list.
2. **Mathlib.** The declarations have to be stated over *Mathlib's* objects. A project that builds
   its own `ℝ` proves theorems we cannot consume, however good they are.
3. **A theorem we lack.** Measured against the paper's own recorded gaps — a hypothesis carried in
   a theorem's type, a `Known limitations` entry — not against what sounds adjacent. Check the
   pinned Mathlib first: a vendored copy of something upstream already has is a defect.
4. **It is finished, not work in progress.**  Nothing is copied that carries a `sorry`, an
   `axiom`, a `native_decide`, or an **undischarged hypothesis** — a `structure`/`class` bundling
   an unproved analytic input, which makes a result conditional without ever writing `sorry`.  A
   vendored declaration must be *unconditional*: every binder an ordinary mathematical hypothesis
   or a standard Mathlib typeclass.  The check is `#print axioms` on each headline result, which is
   transitive, plus a scan for bundles; both go in the audit with their numbers.  A project that is
   excellent but mid-flight is recorded below, not copied.
5. **It compiles at our pin**, or the drift is repairable and every repair is marked inline.

## Vendored

| Slug | Project | Licence | What we took | Audit |
|---|---|---|---|---|
| `PNTPlus` | [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | Apache-2.0 | The finite-order Hadamard factorization subtree: 35 files, 9,809 lines, 409 declarations, sorry-free, footprint `[propext, Classical.choice, Quot.sound]` | `Vendor/PNTPlus.lean` |
| `HexRealRootsMathlib` | [leanprover/hex-real-roots-mathlib](https://github.com/leanprover/hex-real-roots-mathlib) | Apache-2.0 | The sector core of the Obreschkoff two-circle theorem: 1 file, 819 lines, 32 declarations, sorry-free, footprint `[propext, Classical.choice, Quot.sound]`, builds unadapted at our pin | `Vendor/HexRealRootsMathlib.lean` |

## Assessed and declined

| Project | Licence | Subject | Verdict |
|---|---|---|---|
| [lukasliehr/TotallyPositive](https://github.com/lukasliehr/TotallyPositive) | **none** | Total positivity, sign changes, variation diminishing, checkerboard inverse of a TP matrix — the frame-set conjecture for totally positive functions | **Blocked on licence, and it is the one we most want.** 48 files touch total positivity, `E4/DFP/TotalPositivity.lean` alone is 5,950 lines, and it carries `signChangesFin`, `signVariationsFin`, `inverse_checkerboard_nonneg_of_totallyPositive` — the Gantmacher–Krein material `rh-toeplitz-nogo` records as absent everywhere. No `LICENSE`, no licence sentence in the README, no copyright header in any file. Watch for one; nothing may be copied until then |
| [UOR-Foundation/F1](https://github.com/UOR-Foundation/F1) | MIT | `Spec ℤ ×_𝔽₁ Spec ℤ`, the arithmetic square whose Hodge-index positivity is RH | **Not consumable.** Zero `import Mathlib` in 693 files: it builds ℚ, ℝ (Bishop regular sequences) and ℂ from scratch on `UOR-Framework`, so every declaration is over its own reals and nothing transports to a Mathlib development without a bridge that does not exist. Pinned to Lean `v4.16.0`. Sound on its own terms — genuinely 0 code-level `sorry` (the 675 raw hits are all prose) and a mechanized honesty gate — but the one thing we would want, the Hodge index for the square, is *deliberately encoded open* (`hodgeIndexHolds = none`), so there is no theorem there to take |
| [seb488/LeanComplexAnalysis](https://github.com/seb488/LeanComplexAnalysis) | Apache-2.0 | Herglotz–Riesz representation for positive harmonic functions on the disc, Poisson integral, Harnack, Bieberbach | **The best remaining candidate; repair unfinished, and now narrower than it looked.** The second sweep found that our pinned Mathlib already carries the disc Poisson half — `herglotzRieszKernel`, `poissonKernel`, the Poisson integral formula and `analyticOnNhd_circleAverage_herglotzRieszKernel_smul`, in `Mathlib/Analysis/Complex/Poisson.lean` and `Analysis/Complex/Harmonic/Poisson.lean` — so seb488's `PoissonIntegral.lean` largely duplicates upstream and the repair spent on it was wasted effort. What Mathlib does **not** carry, and seb488 does, is the **representation theorem**: `HerglotzRiesz_realPos` together with the weak-\* limit construction (`Λ_n`, `K_weak`) that produces the measure. That is the substrate `edrei-spectral-classification`'s `PickEdrei` records as missing, and why `AtomicPickData.hrepr` sits in the type. Written against Mathlib `5352afcc` / Lean `v4.28.0-rc1`; `HerglotzRieszUnique.lean` is still unrepaired — `Continuous.pow` moved to the `Pi` form (fixed by `(continuous_pow m).comp continuous_subtype_val`) and the `@`-application of `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` leaves its three instance binders open (fixed by named `(𝕜 := ℂ) (X := ...)`), but the `convert this A _ using 2` bridge from `A.topologicalClosure = ⊤` to `Dense ↑A` does not survive and wants rewriting. Even repaired it is the *disc* representation: the atomic half-plane Pick form still needs a Cayley transport and Stieltjes inversion. Upstream headers read `Copyright (c) 2025 [Your Name]`, a placeholder, so attribution has to come from the repository owner |
| [mrdouglasny/spectral-positivity](https://github.com/mrdouglasny/spectral-positivity) | Apache-2.0 | Perron–Frobenius for irreducible nonnegative matrices, Jentzsch's theorem, M-matrix inverse positivity | **Sound but unneeded.** 2,635 lines, sorry-free, close pin (`v4.30.0`). It genuinely extends `Shields...Matrix.PerronFrobenius`, which is the entrywise-positive Perron root plus the compound-matrix corollary, by adding `Matrix.IsIrreducible` and the irreducible theorem. No paper here consumes irreducibility — the Edrei arguments run on compounds that are entrywise positive as soon as they are nonzero. Declined on simplicity; revisit if an irreducible-but-not-positive matrix ever appears |
| [math-inc/strongpnt](https://github.com/math-inc/strongpnt) | **none** | The strong prime number theorem, with the complex-analysis infrastructure built for it | Blocked on licence |
| [math-inc/RiemannHypothesisCurves](https://github.com/math-inc/RiemannHypothesisCurves) | **none** | RH for curves over finite fields — the function-field Hodge-index mechanism | Blocked on licence. This is the closest formal statement of the mechanism `hodge-toeplitz` is about |
| [jinshanmu/CrouzeixConjecture](https://github.com/jinshanmu/CrouzeixConjecture) | **none** | Numerical range, Crouzeix's conjecture | Blocked on licence |
| [erichou1/cofinite-derivative-zeros](https://github.com/erichou1/cofinite-derivative-zeros) | **withheld** | Zeros of high derivatives of a transcendental entire function; Jensen's formula | README states "No license has been granted" |
| [FormalMathResearch/cross-boundary-moment-kernels](https://github.com/FormalMathResearch/cross-boundary-moment-kernels) | **deferred** | Total positivity of moment kernels, TP2, one-crossing geometry | README defers licensing "until the release structure is finalized". Topically close to the Edrei papers; recheck |
| [ajdobner/SymmetricFun](https://github.com/ajdobner/SymmetricFun) | **none** | The ring of symmetric functions in infinitely many variables | Blocked on licence. Would otherwise bear on `Shields/Combinatorics/Young` |
| [igorrivin/polya-szego-lean](https://github.com/igorrivin/polya-szego-lean) | MIT (README only) | Pólya–Szegő problem book, machine-formalized | **Not a library.** 398 files named `Problem_NNN.lean` and UUID-stamped machine outputs, 656 code-level `sorry`s. Nothing here is stated in a form another development can import |
| [jinshanmu/Hatano-Nelson](https://github.com/jinshanmu/Hatano-Nelson) | MIT | Pseudospectra of complex tridiagonal Toeplitz matrices | Vendorable and sorry-free, but the subject is pseudospectral connectedness, not Toeplitz determinants or total positivity. Nothing we need |
| [thefundamentaltheor3m/Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) | Apache-2.0 | Viazovska's dimension-8 sphere packing: modular forms, Poisson summation, Fourier | Off our gap list. Its `ForMathlib/` helpers (`tprod`, `SpecificLimits`, `Fourier`) are the part to revisit if a Poisson-summation step ever appears |
| [openai/ten-proofs](https://github.com/openai/ten-proofs) | Apache-2.0 | Ten separate results — sphere packing bounds, metric codes, a non-sofic group, the permanent | Ten unrelated certificates rather than a library; nothing meets a recorded gap |
| [dududuguo/HighDimProb](https://github.com/dududuguo/HighDimProb) | Apache-2.0 | Concentration inequalities, metric entropy, random matrices | Well-built and sorry-free, but our matrices are deterministic and totally nonnegative |
| [scottnarmstrong/DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi) | Apache-2.0 | De Giorgi–Nash–Moser, Sobolev spaces from weak derivatives | Elliptic PDE regularity; no overlap |
| [YaelDillies/mean-fourier](https://github.com/YaelDillies/mean-fourier) | Apache-2.0 | Mean Fourier analysis | No overlap |
| [teorth/analysis](https://github.com/teorth/analysis) | Apache-2.0 | Companion to *Analysis I* | A teaching companion; its 2,080 `sorry`s are exercises |
| [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | Apache-2.0 | Formal *statements* of open conjectures | Not a proof source — the 3,780 `sorry`s are the design. Useful as a **statement reference** when phrasing a conjecture (it carries Montel, Vitali, Hurwitz, Schoenberg and Toeplitz entries); never as something to import |
| [leanprover/hex-real-roots-mathlib](https://github.com/leanprover/hex-real-roots-mathlib) — *the rest of it* | Apache-2.0 | Sturm chains, Descartes parity, root separation, the verified isolator | Partially **vendored** (see above). The remainder is declined: `SturmTheorem.lean`, `Separation.lean`, `TwoCircle.lean` and the isolator reach into the `HexRealRoots`, `HexPolyMathlib` and `HexPolyZMathlib` packages, so taking them means vendoring that stack. `DescartesParity.lean` and `TwoCircleRegion.lean` are Mathlib-only and clean but answer no recorded gap. Note that its `SturmTheorem` is the signed-remainder chain, a different object from `Shields.IsSturmFamily`, which is the interlacing family of the Edrei staircase polynomials |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | A large general Mathlib-downstream library: 2,803 files, 603k lines, 1 `sorry` and 1 `axiom` in the whole tree | **Rigorous and large, but off our subjects.** Zero hits for Toeplitz, Hankel, Pólya frequency, Schoenberg, Obreschkoff or sign variations. Three near misses, all declined: `Analysis/PDE/Harnack/Planar.lean` is Harnack's inequality built on Mathlib's own `herglotzRieszKernel`, not the representation theorem we need; `RingTheory/MvPolynomial/Symmetric/Schur/` defines the Schur polynomial from bounded semistandard tableaux exactly as `Shields.schur` does and adds Kostka, dominance triangularity and branching, but **not** Jacobi–Trudi, which is the part we actually need and already have through `Shields`'s LGV chain — adopting it would rewire our chain onto a foreign definition to gain theory nothing here consumes; `Analysis/CompletelyMonotone/Reciprocal.lean` is the one Stieltjes hit and is about completely monotone functions, not the moment representation. Also pinned one toolchain ahead, at Lean `v4.34.0-rc1` |
| [leanprover-community/physlib](https://github.com/leanprover-community/physlib) | Apache-2.0 | Quantum information; carries the only `compoundMatrix` found anywhere outside `_lean_shared` | **Declined; ours is stronger.** `QuantumInfo/ForMathlib/Majorization.lean` defines `compoundMatrix` on `Matrix d d ℂ` with `compoundMatrix_mul` (Cauchy–Binet), `_conjTranspose`, `_diagonal` and `_unitary`, aimed at singular values and majorization. `Shields.compound` is over an arbitrary `CommRing`, which is what the total-positivity arguments need, and already carries Cauchy–Binet plus the compound characteristic polynomial. Gate 4 would also need a per-file pass: the repository has 33 `sorry`s, 7 `native_decide` and 5 `axiom`s overall |
| [ImperialCollegeLondon/AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge) | Apache-2.0 | Formal *statements* of recent Annals of Mathematics theorems | **Not a proof source**, on the same ground as `google-deepmind/formal-conjectures`: the repository formalizes theorem statements, so its `sorry`s are the design rather than a defect, and gate 4 is failed by construction. Small (85 KB). Useful only as a statement reference. Surfaced by a statement-shape code search for `totallyPositive`, which it carries in the algebraic-number-theory sense — totally positive elements of a number field, a homonym of the matrix property and no relation to it |

## What the survey did not find anywhere

Searched across every checkout, by statement shape as well as by name.

**Found on the second sweep, and no longer a limit:** the **sector core of Obreschkoff's
two-circle theorem** — zeros in the closed `π/3` cone about the negative real axis force
positive log-concave coefficients, hence at most one sign variation.  Vendored as
`HexRealRootsMathlib`.  It had been missed because it lives in a computer-algebra package
indexed under root isolation, not under total positivity.

**Still absent everywhere, and these are the honest limits:**

* **Schoenberg's sector theorem in general** — `PF_r` for `r ≤ π/θ - 1` at an arbitrary
  half-angle `θ`, and for an entire function of order less than one rather than a
  polynomial.  Only the `θ = π/3`, `r = 2`, polynomial corner is now formalized.
* **Obreschkoff's theorem proper** — the hyperbolicity half, `prop:sector`(ii).  The sector
  core above is the sign-variation half of the two-circle theorem, not this.
* **Pólya frequency sequences, compound matrices, Whitney's density theorem and Neville
  elimination** — zero hits outside the licence-blocked `TotallyPositive`.  The one
  `compoundMatrix` found anywhere (`leanprover-community/physlib`) is over `ℂ` only and
  built for singular values; see the declined table.
* **Hartogs, Osgood and polydiscs** — zero hits anywhere, which is why
  `toeplitz-newton-boundary` builds its own.
* **Stationary phase, the Laplace method and saddle-point asymptotics** — zero hits as
  theorems.
* **Stieltjes inversion and the Nevanlinna–Pick class** — zero hits as declarations, on
  either sweep.  Note that the *disc* Herglotz–Riesz **kernel** and the Poisson integral
  formula are now in Mathlib itself (`Mathlib/Analysis/Complex/Poisson.lean` and
  `Mathlib/Analysis/Complex/Harmonic/Poisson.lean`, carrying `herglotzRieszKernel`,
  `poissonKernel` and `analyticOnNhd_circleAverage_herglotzRieszKernel_smul`); what is
  missing is the **representation theorem** — positive harmonic function as the integral of
  a measure — and the half-plane transport.
