/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnny Shields
-/
module

public import Vendor.HexRealRootsMathlib.TwoCircleSector

/-!
# `hex-real-roots-mathlib` — the vendored slice, and its quality audit

## Source

* **Project** `hex-real-roots-mathlib`, the Mathlib-semantics layer of
  [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library for Lean 4.
  <https://github.com/leanprover/hex-real-roots-mathlib>
* **Author** Kim Morrison ([@kim-em](https://github.com/kim-em)), for Lean FRO, LLC.  The
  vendored file's upstream header reads
  `Copyright (c) 2026 Lean FRO, LLC. All rights reserved.` / `Authors: Kim Morrison`, and
  it is reproduced verbatim at the top of the copy.
* **Revision** `30c19a426b3c195e067f2c15d5a6ca06eff7df66`
* **Licence** Apache 2.0, granted in the repository's `LICENSE`.
* **Upstream pins** Lean `v4.33.0-rc1`, Mathlib at tag `v4.33.0-rc1`.  Ours are Lean
  `v4.33.0-rc1` and Mathlib `8e45b0548034eeda677a64e1e0b07837390835b6`, a slightly later
  master.

## What we took, and why

One file, `HexRealRootsMathlib/TwoCircleSector.lean`: the **sector core of the Obreschkoff
two-circle theorem**.  A monic real polynomial with nonzero constant term whose complex
zeros all lie in the closed sector `{z | Re z ≤ -‖z‖/2}` — half-angle `π/3` about the
negative real axis — has strictly positive and log-concave coefficients
(`Polynomial.posLogConcave_of_aeval_mem_sector`), hence at most one sign variation
(`Polynomial.signVariations_le_one_of_sector`), and none when no zero is outside
(`Polynomial.signVariations_eq_zero_of_sector`).

This meets a gap this repository had recorded as absent everywhere.
`rh-toeplitz-nogo/lean/README.md` carries `prop:sector` as a hypothesis structure and names
Schoenberg's sector theorem and Obreschkoff's as what would discharge it; the `θ → 0` case
(zeros on the negative real axis, every order) was already closed there by
`toeplitzMinor_rootProdSeq_nonneg`, and what remained was **a cone of positive half-angle**.
At `θ = π/3` the proposition asserts `PF_r` for `r ≤ π/θ - 1 = 2`, whose consecutive form is
exactly log-concavity — so this file closes that corner.  `DetectionWindow.SectorCore` is
the consumer.

Upstream's own docstring records that no formalization of the two-circle theorem, or of this
sector core, is known in any proof assistant.

**What we did not take.** The rest of the project is the executable root isolator and its
soundness proof, which reaches into the `HexRealRoots`, `HexPolyMathlib` and
`HexPolyZMathlib` packages; taking any of it would mean vendoring that stack.  Three further
files are Mathlib-only and were still declined for want of a gap they answer:
`DescartesParity.lean` (the parity refinement of Descartes' rule, over Mathlib's own
`Polynomial.signVariations`), `TwoCircleRegion.lean` (the two-circle region of an interval),
and `SturmTheorem.lean` with `SturmChainDefs.lean` (classical Sturm chains and the half-open
root count).  The last is **not** what `Shields.IsSturmFamily` is about: ours is the
interlacing family of the Edrei staircase polynomials, theirs the signed-remainder chain, and
the shared word names two different objects.

## Quality audit

**Scale.**  Upstream is 24 files and 9,825 lines.  The vendored slice is 1 file, 819 lines,
32 declarations.

**Sorry-free and axiom-clean.**  Zero `sorry`, zero `axiom`, zero `native_decide` in the
vendored file, and zero of each across all 24 upstream files (comments stripped).  The
footprint is transitive rather than textual: at our pin, each of

* `Polynomial.posLogConcave_of_aeval_mem_sector`
* `Polynomial.signVariations_le_one_of_sector`
* `Polynomial.signVariations_eq_zero_of_sector`
* `Polynomial.PosLogConcave.mul_X_add_C`
* `Polynomial.PosLogConcave.mul_quadratic`

reports `[propext, Classical.choice, Quot.sound]`.

**No undischarged hypothesis.**  Zero `class`.  The single `structure` is
`Polynomial.PosLogConcave`, and it is a `Prop`-valued *predicate on a polynomial* — two
fields, positivity and log-concavity of the coefficients — that the file **proves** from
ordinary hypotheses in `posLogConcave_of_aeval_mem_sector`.  It is a conclusion, not an
assumed analytic input, so it is unlike our own `AtomicPickData` or `PacketFamily`; every
binder of every vendored theorem is an ordinary mathematical hypothesis or a Mathlib
typeclass.

**Builds clean at our pin**, unadapted and with zero warnings.  No proof was touched and no
import was rewritten: the file's only import is `Mathlib`.

**Namespace hygiene.**  All 32 declarations are under `Polynomial` (28) and
`Polynomial.PosLogConcave` (4); none is at the root.  Nothing clashes with Mathlib — the
build against full Mathlib is that check, since a duplicate declaration would fail to
elaborate — and a grep of `_lean_shared/Shields` and all seven paper trees for
`PosLogConcave`, `Polynomial.sector`, `posLogConcave_of_aeval_mem_sector`,
`signVariations_le_one_of_sector` and `signVariations_eq_zero_of_coeff_nonneg` returns
nothing.  `Vendor` and `DetectionWindow` elaborate together.

**Overlap with what we already carry.**  None.  Mathlib supplies `Polynomial.signVariations`
and Descartes' rule (`Mathlib/Algebra/Polynomial/RuleOfSigns.lean`), which this file consumes
rather than duplicates.  `Shields.Order.SignChanges` counts sign changes of a **vector**, for
the variation-diminishing property of a totally nonnegative matrix — a different object from
a polynomial's coefficient variations, and not a duplicate of either.

**Non-vacuity, and that the hypothesis does work.**  Checked in `DetectionWindow.SectorCore`
rather than asserted: `X² + X + 1` has both zeros on the sector boundary and attains
`D_{2,1} = 0`, while `X² + (1/2)X + 1`, whose zeros have `Re z = -1/4 > -1/2 = -‖z‖/2` and so
sit just outside, has `D_{2,1} = -3/4 < 0`.  Both are compiled examples.

**Adaptations to the pin.**  None.

## Retiring this file

The module is written as an upstreamable Mathlib slice and its author says so, but **no
Mathlib pull request carries it yet** — searched open PRs by title and body for
`Obreshkoff`, `Obreschkoff`, `two-circle`, and the statement shape, with no hit.  So this is
the project-vendoring route rather than the PR route, and the retirement condition is that
the author upstreams it: when it merges, bump the pin and delete
`Vendor/HexRealRootsMathlib/`.  `DetectionWindow.SectorCore` then needs only its import line
changed, the declaration names being upstream's already.
-/
