/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Vendor.AlgebraicCombinatorics.CauchyBinet
import Vendor.AlgebraicCombinatorics.Details.DominoBridge
import Vendor.AlgebraicCombinatorics.Details.DominoTilings
import Vendor.AlgebraicCombinatorics.Details.InfiniteProducts2
import Vendor.AlgebraicCombinatorics.Details.Limits
import Vendor.AlgebraicCombinatorics.Determinants.PermFinset
import Vendor.AlgebraicCombinatorics.DeterminantsBasic
import Vendor.AlgebraicCombinatorics.DividingFPS
import Vendor.AlgebraicCombinatorics.Extra.Pfaffian
import Vendor.AlgebraicCombinatorics.FPS.CommutativeRings
import Vendor.AlgebraicCombinatorics.FPS.Derivatives
import Vendor.AlgebraicCombinatorics.FPS.ExpLog
import Vendor.AlgebraicCombinatorics.FPS.InfiniteProducts
import Vendor.AlgebraicCombinatorics.FPS.InfiniteProducts1
import Vendor.AlgebraicCombinatorics.FPS.InfiniteProducts2
import Vendor.AlgebraicCombinatorics.FPS.IntegerCompositions
import Vendor.AlgebraicCombinatorics.FPS.LaurentSeries
import Vendor.AlgebraicCombinatorics.FPS.Limits
import Vendor.AlgebraicCombinatorics.FPS.Multivariate
import Vendor.AlgebraicCombinatorics.FPS.NonIntegerPowers
import Vendor.AlgebraicCombinatorics.FPS.NotationsExamples
import Vendor.AlgebraicCombinatorics.FPS.Polynomials
import Vendor.AlgebraicCombinatorics.FPS.Substitution
import Vendor.AlgebraicCombinatorics.FPS.WeightedSets
import Vendor.AlgebraicCombinatorics.FPS.XnEquivalence
import Vendor.AlgebraicCombinatorics.FPSDefinition
import Vendor.AlgebraicCombinatorics.Fin.SkipTwo
import Vendor.AlgebraicCombinatorics.LaurentSeries
import Vendor.AlgebraicCombinatorics.Partitions.Basics
import Vendor.AlgebraicCombinatorics.Partitions.QBinomialFormulas
import Vendor.AlgebraicCombinatorics.PentagonalJacobi
import Vendor.AlgebraicCombinatorics.Permutations.Basics
import Vendor.AlgebraicCombinatorics.Permutations.CycleDecomposition
import Vendor.AlgebraicCombinatorics.Permutations.Inversions1
import Vendor.AlgebraicCombinatorics.Permutations.Inversions2
import Vendor.AlgebraicCombinatorics.Permutations.Signs
import Vendor.AlgebraicCombinatorics.QBinomialBasic
import Vendor.AlgebraicCombinatorics.SignedCounting.AlternatingSums
import Vendor.AlgebraicCombinatorics.SignedCounting.BooleanMobiusInversion
import Vendor.AlgebraicCombinatorics.SignedCounting.InclusionExclusion1
import Vendor.AlgebraicCombinatorics.SignedCounting.SubtractiveMethods
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.MonomialSymmetric
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.NPartition
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.OmegaInvolution
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.SchurBasics

/-!
# VENDORED FROM AN EXTERNAL LEAN PROJECT: algebraic-combinatorics

**This directory is not our mathematics.**  It reproduces 47 of the 52 modules of
facebookresearch/algebraic-combinatorics, a formalization of Darij Grinberg's textbook
*An Introduction to Algebraic Combinatorics* (arXiv:2506.00738, `Grinberg2025AlgebraicCombinatorics`
in `refs/`), so that work depending on it can proceed while none of it is in Mathlib.

* **Project:** algebraic-combinatorics, <https://github.com/facebookresearch/algebraic-combinatorics>
  (blueprint <https://faabian.github.io/algebraic-combinatorics/>).
* **Revision copied:** upstream `main` at `b6022318e986a0c20764569208ba8ebbe1c04dbf`
  (1 April 2026), as ported to Lean/Mathlib `v4.34.1` by two open pull requests:
  [#9](https://github.com/facebookresearch/algebraic-combinatorics/pull/9) (the version upgrade)
  and [#10](https://github.com/facebookresearch/algebraic-combinatorics/pull/10) (restatements of
  Mathlib lemmas proved directly from Mathlib), stacked; the files are those of #10's head,
  `7ab1d77025dc2da016617d05d43e17fefc3520a6` on `johnnyshields/algebraic-combinatorics`.
* **Author:** Fabian Gloeckle (GitHub `faabian`), Meta; the formalization was produced with the
  RepoProver system <https://github.com/facebookresearch/repoprover>.  The upstream header,
  `Copyright (c) Meta Platforms, Inc. and affiliates.  All rights reserved.`, and the
  `Authors: AlgebraicCombinatorics Contributors` lines are preserved in every file.
* **Licence:** Creative Commons Attribution-NonCommercial 4.0 International (CC BY-NC 4.0), **not**
  MIT; the full text is `AlgebraicCombinatorics/LICENSE`.  Used here non-commercially, with
  attribution in `AlgebraicCombinatorics/README.md`.
* **Upstream pin:** Lean/Mathlib `v4.28.0`.  Built here against Lean `v4.34.1`, Mathlib `v4.34.1`
  (`d13f23b723b8a846827a245b89c10fc7d3f11612`), which is the pin of pull request #9 itself.

## What it provides

Formal power series and generating functions (compositions, weighted sets, infinite products,
exp/log, non-integer powers, Laurent series); integer partitions with Euler's odd-equals-distinct
theorem (`Nat.Partition.odd_eq_distinct`), q-binomial coefficients, Euler's pentagonal number
theorem (`AlgebraicCombinatorics.euler_pentagonal_number_theorem`) and the Jacobi triple product
(`AlgebraicCombinatorics.jacobi_triple_product`, `jacobi_triple_product_fps'`); permutations,
inversions, Lehmer codes and cycle decomposition; sign-reversing involutions and
inclusion--exclusion; determinant basics and Cauchy--Binet; domino tilings; and symmetric
polynomials through Schur polynomials, the omega involution and the Littlewood--Richardson rule
via Bender--Knuth (`AlgebraicCombinatorics.littlewoodRichardson`).

## What we did not take

* **Five modules are excluded**, because each contains a `sorry` or imports one that does:
  `DesnanotJacobi` (`desnanot_jacobi_cauchy_identity_gen`), `Determinants.LGV2`
  (`catalan_hankel_det_general`), `SymmetricFunctions.PieriJacobiTrudi` (`pieri_horizontal`,
  `pieri_vertical`, `jacobiTrudi_e`), and `Determinants.LGV1` and `SymmetricFunctions.SSYTEquiv`,
  which import them.  So the LGV lemma, Desnanot--Jacobi, Pieri and Jacobi--Trudi are **not** here.
* **Twenty examples are pruned from `Partitions/Basics.lean`**, with their docstrings and the two
  section headings left empty by the pruning: the small-value checks
  `Fintype.card (Partition 5) = 7`, `partitionCount 5 = 7`, `partsCount k 5` for `k = 0..5`,
  `oddPartsCount`/`distinctPartsCount` at 3 and 7, and eight `partsAndLargestCountTotal` values.
  Each was a `native_decide`, and `decide +kernel` cannot replace it because the `Decidable`
  instance does not reduce in the kernel.  No theorem depends on them.
* The upstream root file `AlgebraicCombinatorics.lean` is replaced by this one.

## Quality audit

Read against this pin.

* **Scale.** 47 files, 100,884 lines, 3,767 declarations (excluding compiler-generated ones), of
  which 2,815 are theorems.
* **Sorry-free and axiom-clean.**  No `sorry`, no `axiom`, no `unsafe`, no `partial def`.
  `#print axioms`, collected over **every one of the 2,815 theorems**, reports exactly
  `[propext, Classical.choice, Quot.sound]`.
* **No `native_decide`.**  Upstream uses it 45 times in these files.  The 25 that survive pruning
  are `decide +kernel`, each marked inline `-- vendored: was `native_decide``, so the trust base is
  the kernel and not the compiler.
* **No undischarged hypothesis.**  The `structure`s declared (`WeightedSet`, `NPartition`,
  `YoungTableau`, `SSYT`, `DominoTiling`, `BinaryRepresentation` and the like) are combinatorial
  objects, not bundles of unproved inputs; the headline theorems carry ordinary hypotheses only.
* **Builds clean at our pin**, with no errors and **no deprecation warnings**.  The remaining
  warnings are style-linter output from the host lakefiles' `mathlibStandardSet` (long lines,
  long files, flexible tactics), and four `set_option maxHeartbeats` overrides are upstream's.
* **Namespace hygiene is weak, and is upstream's.**  2,214 declarations sit in
  `AlgebraicCombinatorics`, but the rest spread over Mathlib's namespaces (`PowerSeries` 286,
  `Nat` 123, `Equiv` 110) and over short top-level ones (`DominoTilings`, `DominoTilingsZ`,
  `NPartition`, `FPS`, `WeightedSet`, `YoungTableau`, `SSYT`, ...), with 128 in the root
  namespace.  Elaborating this tree together with `Shields`, `Mathlib` and
  `edrei-spectral-classification`'s `EdreiClass` reports no clash, but a future Mathlib name in
  `PowerSeries` or `Nat.Partition` can collide; the upgrade to `v4.34.1` already met one
  (`PowerSeries.constantCoeff_subst_of_constantCoeff_zero`, renamed with a prime upstream in #9).
* **Overlap with Mathlib.**  41 theorems restate a Mathlib lemma under the textbook's numbering,
  and are proved by it.  They are kept rather than pruned: the blueprint and the rest of the tree
  consume them by name, and pruning them would mean rewriting their callers.
* **Overlap with what we carry.**  `Shields.Combinatorics.Young` has its own Schur polynomials,
  Jacobi--Trudi and LGV; `Vendor/MathlibPR/PR40473` has Mathlib's Cauchy--Binet.  Neither is the
  same statement in the same namespace, and all are kept.

## Adaptations

None to the mathematics.  The port to `v4.34.1` is upstream's, in pull requests #9 and #10; the
changes made here are the vendoring operations above: imports rewritten from
`AlgebraicCombinatorics.*` to `Vendor.AlgebraicCombinatorics.*`, `native_decide` replaced and
marked, the five modules excluded and the twenty examples pruned.

## Retiring

Re-copy from upstream `main` once #9 and #10 merge, and drop this note's references to them.  Delete
a module when its content reaches Mathlib, and delete the directory when no paper imports it.
-/
