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
| `MathlibPR/PR39834/SchurTriangulation.lean` | [#39834](https://github.com/leanprover-community/mathlib4/pull/39834), part 2/3 of [#39139](https://github.com/leanprover-community/mathlib4/pull/39139); subsumes [#39829](https://github.com/leanprover-community/mathlib4/pull/39829) | Matteo Cipollina (`or4nge19`), with `kuotsanhsu` | Triangularizability via flags: over an algebraically closed field, every endomorphism of a finite-dimensional space has a basis in which its matrix is `Matrix.BlockTriangular id` |
| `MathlibPR/PR39837/MatrixSchurTriangulation.lean` | [#39837](https://github.com/leanprover-community/mathlib4/pull/39837), part 3/3 of [#39139](https://github.com/leanprover-community/mathlib4/pull/39139) | Matteo Cipollina (`or4nge19`) | Unitary block-triangular Schur decomposition: Gram--Schmidt preserves `Basis.flag`, giving an orthonormal triangularizing basis, plus the matrix-level wrapper.  Imports `MathlibPR/PR39834/SchurTriangulation.lean` |
| `MathlibPR/PR40473/CauchyBinet.lean` | [#40473](https://github.com/leanprover-community/mathlib4/pull/40473) | Carles Marín (`karlesmarin`) | The Cauchy--Binet formula: `Matrix.det_mul_cauchyBinet` expands `det (A * B)` for rectangular `A`, `B` over `k`-element column selections, and `Matrix.det_mul_eq_sum_det_submatrix_mul_prod` is the Leibniz-type expansion behind it.  The pinned Mathlib carries only the square case `Matrix.det_mul` |
| `MathlibPR/PR40533/TranslationInvariance.lean` | [#40533](https://github.com/leanprover-community/mathlib4/pull/40533) | Stefan Kebekus (`kebekus`) | Translation invariance of every meromorphicity notion, with the pointwise-set and analytic-order companions.  Merged upstream, but after the pinned revision.  The PR touches eight Mathlib modules; the declarations absent from the pin are collected here in dependency order |
| `MathlibPR/PR40957/LogCountingFiniteSupport.lean` | [#40957](https://github.com/leanprover-community/mathlib4/pull/40957) | Stefan Kebekus (`kebekus`) | A meromorphic function has finitely many poles exactly when its logarithmic counting function is `O(log)`: `logCounting_single_isBigO_log`, `sum_apply_smul_single_eq_self_on_univ`, `logCounting_isBigO_log_of_finite_support`, `finite_support_of_logCounting_isBigO_log`, `finite_support_iff_logCounting_isBigO_log`, `ValueDistribution.logCounting_isBigO_log_iff_finite_support`.  One proof is adapted to the pin through `Finset.sum_fn`, marked inline |
| `MathlibPR/PR41225/CircleIntegrableFunProp.lean` | [#41225](https://github.com/leanprover-community/mathlib4/pull/41225) | Stefan Kebekus (`kebekus`) | `CircleIntegrable` registered with `fun_prop`, together with `circleIntegrable_id` and the `f • g` and `f * g` companions, and the renames `smul_of_continuousOn`/`mul_of_continuousOn` to `continuousOn_smul`/`continuousOn_mul`.  Two adaptations to the pin are marked inline: the attribute is applied directly, and the new names are introduced as aliases |
| `MathlibPR/PR41496/ECanonicalDecomp.lean` | [#41496](https://github.com/leanprover-community/mathlib4/pull/41496) | Stefan Kebekus (`kebekus`) | Four companion lemmas to `MeromorphicOn.exists_ecanonicalDecomp`, the API for the extended canonical decomposition, added upstream to `Mathlib/Analysis/Complex/CanonicalDecomposition.lean`.  Imports `MathlibPR/PR42570/FunPropTags.lean` for its `fun_prop` discharges |
| `MathlibPR/PR41529/BorelGrowth.lean` | [#41529](https://github.com/leanprover-community/mathlib4/pull/41529) | Stefan Kebekus (`kebekus`) | Émile Borel's growth lemma, upstream `Mathlib/MeasureTheory/Function/BorelGrowth.lean`, copied verbatim apart from the Lean 4.34 module syntax the pin does not accept |
| `MathlibPR/PR41684/MeromorphicLogDeriv.lean` | [#41684](https://github.com/leanprover-community/mathlib4/pull/41684) | Stefan Kebekus (`kebekus`) | The API for logarithmic derivatives of meromorphic functions, upstream `Mathlib/Analysis/Meromorphic/LogDeriv.lean`, followed by the declarations the same PR adds to `Calculus/LogDeriv.lean`, `Meromorphic/Basic.lean` and `Meromorphic/Order.lean` |
| `MathlibPR/PR42000/PosLogEstimates.lean` | [#42000](https://github.com/leanprover-community/mathlib4/pull/42000) | Stefan Kebekus (`kebekus`) | Trivial estimates for the positive part of the logarithm, `Real.posLog`.  Only the declarations absent from the pinned `SpecialFunctions/Log/PosLog.lean` are copied; the PR's widening of `Real.monotoneOn_posLog` from `Set.Ici 0` to `Set.Ici (-1)`, the matching weakening of `Real.posLog_le_posLog`, and `Real.antitoneOn_posLog` are deliberately not reproduced, and call sites pass `neg_one_lt_zero.le.trans h` instead |
| `MathlibPR/PR42227/CodiscreteAPI.lean` | [#42227](https://github.com/leanprover-community/mathlib4/pull/42227) | Stefan Kebekus (`kebekus`) | API for (co)discrete sets: the declarations the PR adds to `Topology/DiscreteSubset.lean`, `Algebra/Polynomial/Roots.lean`, `Topology/Algebra/Polynomial.lean`, `Calculus/FDeriv/Congr.lean` and `Calculus/Deriv/Basic.lean` |
| `MathlibPR/PR42490/LogDerivToFun.lean` | [#42490](https://github.com/leanprover-community/mathlib4/pull/42490) | Stefan Kebekus (`kebekus`); upstream module by Chris Birkbeck | `logDeriv_mul`, `logDeriv_div` and `logDeriv_prod` restated in `Pi` form with `@[to_fun]`, giving the `fun`-variants the later value-distribution files apply pointwise |
| `MathlibPR/PR42570/FunPropTags.lean` | [#42570](https://github.com/leanprover-community/mathlib4/pull/42570) | Stefan Kebekus (`kebekus`) | `fun_prop` tags on `MeromorphicOn` and `AnalyticOnNhd`, mostly `attribute [fun_prop]` commands rather than copied declarations.  It also applies the tags from two neighboring post-pin PRs, on `Complex.meromorphic_canonicalFactor` and `Complex.analyticOnNhd_canonicalFactor`; the statement change at `analyticOnNhd_circleMap` is not reproduced |
| `MathlibPR/PR42760/RegularizedHypergeometric.lean` | [#42760](https://github.com/leanprover-community/mathlib4/pull/42760) (the file itself is already on Mathlib master from an earlier PR, but postdates the pin) | Moritz Doll (`mcdoll`) | The regularized generalized hypergeometric function `Complex.regularizedHGFun`, notated `F₀₁(a)`, with its coefficients, convergence radius and analyticity in the argument, plus the Gaussian `₂F₁` specialization.  `F₀₁(a)` **is** the `Z` of `_papers_done/turan-bessel`: `Z(a,λ) = ₀F₁(;a;λ)/Γ(a)` is by definition the regularized `₀F₁`, and `regularizedHGFunCoeff 0 {a} n = 1/(n!·Γ(a+n))` closes by `simp`.  Analyticity is in the ARGUMENT only, so it supplies no parameter calculus and no polygamma beyond `digamma`.  Backports `Complex.Gamma_add_nat_div_Gamma_eq` and `FormalMultilinearSeries.const_smul_sum_apply` from master `cf65d43b4f`, both absent at the pin; five further adaptations (a reproved `Gamma_add_nat_div_Gamma_eq`, `convert!`, dropped `AnalyticOnNhd` `fun_prop` tags, four `grind` calls, two multiset helpers) are marked inline and listed in the file's audit header |
| `MathlibPR/PR42760/Bessel.lean` | [#42760](https://github.com/leanprover-community/mathlib4/pull/42760) | Weiyi Wang (`wwylele`) | Bessel function of the first kind, `Complex.besselJ a x = (x/2)^a * F₀₁(a) (-(x/2)^2)`, notated `J(a)`, with parity in integer order and analyticity on `slitPlane` (everywhere, for integer order).  Note the index: the local notation is `F₀₁(a) := regularizedHGFun 0 {a+1}`, so it is `J_{a-1}` whose hypergeometric factor is the paper's `Z(a,·)`.  The modified `I_ν` is the same expression at `+(x/2)^2` and is deliberately deferred by the author, so this does **not** close the Bessel dictionary; it does make `eq:I-Z` a sign of argument.  Imports `MathlibPR/PR42760/RegularizedHypergeometric.lean`; two `fun_prop` proofs written out for the pin |
| `ProjectVD/` (22 files, in `Field/`, `LLD/`, `MathlibPending/`, `MathlibSubmitted/`, `SMT/`) | [kebekus/ProjectVD](https://github.com/kebekus/ProjectVD).  Six files are already submitted to Mathlib and name their PR in their own header — [#41303](https://github.com/leanprover-community/mathlib4/pull/41303), [#41809](https://github.com/leanprover-community/mathlib4/pull/41809), [#41817](https://github.com/leanprover-community/mathlib4/pull/41817), [#41864](https://github.com/leanprover-community/mathlib4/pull/41864), [#42020](https://github.com/leanprover-community/mathlib4/pull/42020), [#42475](https://github.com/leanprover-community/mathlib4/pull/42475); the rest have no PR yet | Stefan Kebekus (`kebekus`) | Value distribution theory for meromorphic functions on the plane: the counting and characteristic estimates, Poisson--Jensen, the lemma on the logarithmic derivative, the Second Main Theorem in its plain, ramified and truncated forms, and little Picard.  Copied verbatim; only the `VD.X` imports become `Vendor.ProjectVD.X`, and the two post-pin Mathlib modules it depends on come from their own `PR<number><Slug>` copies |
| `PNTPlus/` (35 files) + `PNTPlus.lean` | No Mathlib PR: [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) at `7715064f`, which writes them under a `Mathlib/`-shaped path but has not opened one | Matteo Cipollina (`mcipollina`), 33 of 35; `Topology/MetricSpace/Annulus.lean` James Sundstrom; `ValueDistribution/LogCounting/Basic.lean` Stefan Kebekus with Matteo Cipollina | The finite-order **Hadamard factorization** of an entire function, `Complex.Hadamard.hadamard_factorization_of_order` and its growth, reindexed, sequence and centered variants, together with everything the classical proof consumes: Weierstrass factors and general-genus canonical products, the zero divisor with its index type and fibers, Cartan's bound and companions, Borel--Carathéodory, `EntireOfOrderAtMost`, log-counting growth, and an annulus API.  9,809 lines, 409 declarations, no `sorry`, no `axiom`, no hypothesis bundle; footprint `[propext, Classical.choice, Quot.sound]`.  Full audit in `PNTPlus.lean` |
| `HexRealRootsMathlib/TwoCircleSector.lean` + `HexRealRootsMathlib.lean` | No Mathlib PR: [leanprover/hex-real-roots-mathlib](https://github.com/leanprover/hex-real-roots-mathlib) at `30c19a42`, whose own docstring calls the file a Hex-free slice intended for Mathlib | Kim Morrison (`kim-em`), for Lean FRO, LLC | The **sector core of the Obreschkoff two-circle theorem**: a monic real polynomial with nonzero constant term whose complex zeros lie in the closed `π/3` cone about the negative real axis has strictly positive, log-concave coefficients (`Polynomial.posLogConcave_of_aeval_mem_sector`), hence at most one sign variation, and none when no zero is outside.  819 lines, 32 declarations, no `sorry`, no `axiom`, no undischarged bundle; footprint `[propext, Classical.choice, Quot.sound]`; builds at our pin unadapted.  Consumed by `rh-toeplitz-nogo`'s `DetectionWindow.SectorCore`.  Full audit in `HexRealRootsMathlib.lean` |

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
