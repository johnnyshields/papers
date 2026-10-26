# `_lean_shared/Vendor` — code copied from elsewhere

Shared across the papers in this repository, so a result vendored for one paper
is available to all of them and is copied once.

**Nothing here is our mathematics.**  Two sources feed it: unmerged Mathlib pull
requests, and external Lean projects whose work is not in Mathlib and has no PR
open.  Either way the point is the same — work depending on a result can proceed
without rebuilding it.

**`PROJECTS.md` is the surveyed list of external Lean projects**, with the five
gates each has to pass and the verdict on every one looked at.  Read it before
concluding that something has to be written here from scratch, and add a row
rather than re-surveying.


## Contents

| File | Source PR | Author | Provides |
|---|---|---|---|
| `MathlibPR/PR39232/RectangleResidue.lean` | [#39232](https://github.com/leanprover-community/mathlib4/pull/39232) | Jeremy Tan (`jerwaynejones`) | The residue theorem for a rectangular contour.  The pinned Mathlib has Cauchy--Goursat for rectangles and the residue formula on a circle, but nothing computing a rectangular contour integral from the residues inside it |
| `MathlibPR/PR39834/SchurTriangulation.lean` | [#39834](https://github.com/leanprover-community/mathlib4/pull/39834), part 2/3 of [#39139](https://github.com/leanprover-community/mathlib4/pull/39139); subsumes [#39829](https://github.com/leanprover-community/mathlib4/pull/39829) | Matteo Cipollina (`or4nge19`), with `kuotsanhsu` | Triangularizability via flags: over an algebraically closed field, every endomorphism of a finite-dimensional space has a basis in which its matrix is `Matrix.BlockTriangular id`.  Only the `Eigenspace/Triangularizable.lean` part is copied; the PR's additions to `Basis/Flag.lean` and `Eigenspace/Basic.lean` are in the pinned Mathlib |
| `MathlibPR/PR39837/MatrixSchurTriangulation.lean` | [#39837](https://github.com/leanprover-community/mathlib4/pull/39837), part 3/3 of [#39139](https://github.com/leanprover-community/mathlib4/pull/39139) | Matteo Cipollina (`or4nge19`) | Unitary block-triangular Schur decomposition: Gram--Schmidt preserves `Basis.flag`, giving an orthonormal triangularizing basis, plus the matrix-level wrapper.  Imports `MathlibPR/PR39834/SchurTriangulation.lean` |
| `MathlibPR/PR40473/CauchyBinet.lean` | [#40473](https://github.com/leanprover-community/mathlib4/pull/40473) | Carles Marín (`karlesmarin`) | The Cauchy--Binet formula: `Matrix.det_mul_cauchyBinet` expands `det (A * B)` for rectangular `A`, `B` over `k`-element column selections, and `Matrix.det_mul_eq_sum_det_submatrix_mul_prod` is the Leibniz-type expansion behind it.  The pinned Mathlib carries only the square case `Matrix.det_mul` |
| `MathlibPR/PR42760/RegularizedHypergeometric.lean` | [#42760](https://github.com/leanprover-community/mathlib4/pull/42760), merged upstream after the `v4.34` branch point | Moritz Doll (`mcdoll`) | The ten declarations #42760 adds to Mathlib's `Analysis/SpecialFunctions/RegularizedHypergeometric.lean`, which is itself at our pin: `regularizedHGFun_zero`, the radius at `a = 0`, analyticity of `regularizedHGFun` in the argument for `a.card ≤ b.card` and for `a.card = b.card + 1`, and the reflection `regularizedHGFun_zero_singleton_neg_nat_add_one`.  `F₀₁(a)` **is** the `Z` of `_papers_done/turan-bessel`: `Z(a,λ) = ₀F₁(;a;λ)/Γ(a)` is by definition the regularized `₀F₁`.  Analyticity is in the ARGUMENT only, so it supplies no parameter calculus and no polygamma beyond `digamma`.  Copied verbatim, no adaptations |
| `MathlibPR/PR42760/Bessel.lean` | [#42760](https://github.com/leanprover-community/mathlib4/pull/42760) | Weiyi Wang (`wwylele`) | Bessel function of the first kind, `Complex.besselJ a x = (x/2)^a * F₀₁(a+1) (-(x/2)^2)` with `F₀₁(a) := regularizedHGFun 0 {a}`, with parity in integer order and analyticity on `slitPlane` (everywhere, for integer order).  Note the index: it is `J_{a-1}` whose hypergeometric factor is the paper's `Z(a,·)`.  The modified `I_ν` is the same expression at `+(x/2)^2` and is deliberately deferred by the author, so this does **not** close the Bessel dictionary; it does make `eq:I-Z` a sign of argument.  Verbatim upstream apart from its import of `MathlibPR/PR42760/RegularizedHypergeometric.lean` |
| `ProjectVD/` (18 files, in `Field/`, `LLD/`, `MathlibPending/`, `MathlibSubmitted/`, `SMT/`) | [kebekus/ProjectVD](https://github.com/kebekus/ProjectVD).  Two files are submitted to Mathlib and name their PR in their own header — [#41809](https://github.com/leanprover-community/mathlib4/pull/41809), merged after our pin, and [#42475](https://github.com/leanprover-community/mathlib4/pull/42475), open; the rest have no PR yet.  Four further submitted files, [#41303](https://github.com/leanprover-community/mathlib4/pull/41303), [#41817](https://github.com/leanprover-community/mathlib4/pull/41817), [#41864](https://github.com/leanprover-community/mathlib4/pull/41864) and [#42020](https://github.com/leanprover-community/mathlib4/pull/42020), are in the pinned Mathlib and are imported from there | Stefan Kebekus (`kebekus`) | Value distribution theory for meromorphic functions on the plane: the counting and characteristic estimates, Poisson--Jensen, the lemma on the logarithmic derivative, the Second Main Theorem in its plain, ramified and truncated forms, and little Picard.  Copied verbatim; only the `VD.X` imports become `Vendor.ProjectVD.X`, those of the retired submitted files become the Mathlib modules they landed in, and adaptations to the pin are marked inline |
| `PNTPlus/` (35 files) + `PNTPlus.lean` | No Mathlib PR: [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) at `7715064f`, which writes them under a `Mathlib/`-shaped path but has not opened one | Matteo Cipollina (`mcipollina`), 33 of 35; `Topology/MetricSpace/Annulus.lean` James Sundstrom; `ValueDistribution/LogCounting/Basic.lean` Stefan Kebekus with Matteo Cipollina | The finite-order **Hadamard factorization** of an entire function, `Complex.Hadamard.hadamard_factorization_of_order` and its growth, reindexed, sequence and centered variants, together with everything the classical proof consumes: Weierstrass factors and general-genus canonical products, the zero divisor with its index type and fibers, Cartan's bound and companions, Borel--Carathéodory, `EntireOfOrderAtMost`, log-counting growth, and an annulus API.  9,809 lines, 409 declarations, no `sorry`, no `axiom`, no hypothesis bundle; footprint `[propext, Classical.choice, Quot.sound]`.  Full audit in `PNTPlus.lean` |
| `HexRealRootsMathlib/TwoCircleSector.lean` + `HexRealRootsMathlib.lean` | No Mathlib PR: [leanprover/hex-real-roots-mathlib](https://github.com/leanprover/hex-real-roots-mathlib) at `30c19a42`, whose own docstring calls the file a Hex-free slice intended for Mathlib | Kim Morrison (`kim-em`), for Lean FRO, LLC | The **sector core of the Obreschkoff two-circle theorem**: a monic real polynomial with nonzero constant term whose complex zeros lie in the closed `π/3` cone about the negative real axis has strictly positive, log-concave coefficients (`Polynomial.posLogConcave_of_aeval_mem_sector`), hence at most one sign variation, and none when no zero is outside.  819 lines, 32 declarations, no `sorry`, no `axiom`, no undischarged bundle; footprint `[propext, Classical.choice, Quot.sound]`; builds at our pin unadapted.  Consumed by `rh-toeplitz-nogo`'s `DetectionWindow.SectorCore`.  Full audit in `HexRealRootsMathlib.lean` |
| `AlgebraicCombinatorics/` (47 files) + `AlgebraicCombinatorics.lean` | No Mathlib PR: [facebookresearch/algebraic-combinatorics](https://github.com/facebookresearch/algebraic-combinatorics) at `b6022318`, ported to our pin by its open PRs [#9](https://github.com/facebookresearch/algebraic-combinatorics/pull/9) and [#10](https://github.com/facebookresearch/algebraic-combinatorics/pull/10) | Fabian Gloeckle (`faabian`), Meta | A formalization of Grinberg's *An Introduction to Algebraic Combinatorics*: formal power series, partitions with odd-equals-distinct, q-binomials, the pentagonal number theorem and the Jacobi triple product, permutations and inversions, sign-reversing involutions, Cauchy--Binet, Schur polynomials and the Littlewood--Richardson rule.  The five modules with a `sorry` in their closure are left out, so LGV, Desnanot--Jacobi, Pieri and Jacobi--Trudi are not here.  **Licensed CC BY-NC 4.0, not MIT**; see its own `LICENSE` and `README.md`.  Full audit in `AlgebraicCombinatorics.lean` |

## What may touch a vendored file, and nothing else may

A vendored unit tracks **upstream's** style, not ours.  It is deliberately **not** byte-identical
to its source — every unit here carries an audit header its upstream does not, and several carry
adaptations to the pin — so the rule has to be a list rather than the slogan "do not edit".
**Exactly four operations belong to vendoring:**

1. **Pruning** to the declarations absent from the pinned Mathlib, keeping upstream's namespaces,
   names and section scaffolding, so consuming code is written as it will be against a merged
   Mathlib and retirement is "bump the pin, delete the file".
2. **The audit header** — source, author by name and GitHub handle with co-authors, the upstream
   copyright and `Authors:` line verbatim, licence, retirement condition, scale, the sorry/axiom/
   bundle scan with the transitive `#print axioms` footprint, whether it builds clean at our pin,
   namespace hygiene and a clash probe, overlap with what we already carry, and every adaptation.
3. **An adaptation to the pin, marked inline** at the declaration it touches.
4. **An improvement the audit turns up** — a deprecated lemma, a missing attribution header, a
   warning — applied here **and** offered upstream.

**Everything else is out**, and this list is exhaustive: no style or naming sweep, no
Americanization, no docstring-rate edit, no humanness repair, no declaration of ours added, no
restatement in our vocabulary, no import minimization beyond what pruning forces.  `/lean-check`'s
lint and humanness passes are scoped to exclude this directory and `scripts/leanmetrics.py`
enforces that at both ends; the same four operations are stated in that skill's § Non-negotiables
and the two must not drift.

**Why the distinction matters rather than being pedantry.** The retirement condition is what makes
vendoring cheap: when the PR merges or the pin moves, the directory is deleted and nothing of ours
is lost.  That only holds while nothing of ours is *in* it.  A Britishism swept to American, a
docstring added to raise a rate, a lemma of ours parked alongside — each one turns a deletion into
a merge, and none of them is visible in a green build.

## License

Code is made available under the MIT license (see `LICENSE.txt`), or as
otherwise noted in the comments of the file.
