/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Vendor.PNTPlus.Mathlib.Analysis.Complex.HadamardFactorization.Order
public import Vendor.PNTPlus.Mathlib.Analysis.Complex.HadamardFactorization.Growth

/-!
# VENDORED FROM AN EXTERNAL LEAN PROJECT: PNT+

**This directory is not our mathematics.**  It reproduces the finite-order Hadamard
factorization subtree of PrimeNumberTheoremAnd (PNT+), so that work depending on it can
proceed while it is not in Mathlib and has no pull request open.

* **Project:** PrimeNumberTheoremAnd, <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>
* **Revision copied:** `7715064f690d0689f30889846f4e2c5e7ec0c47e` (15 August 2026)
* **Authors of the copied files:** Matteo Cipollina (GitHub `mcipollina`) wrote 33 of the 35;
  `Topology/MetricSpace/Annulus.lean` is James Sundstrom's, and
  `ValueDistribution/LogCounting/Basic.lean` is Stefan Kebekus's with Matteo Cipollina.
* **Licence:** Apache 2.0, as all of Mathlib.  Each file's copyright and `Authors:` line are
  upstream's and are preserved deliberately.
* **Upstream pin:** Lean `v4.32.2`, Mathlib `905b95818e`.  Copied here against Lean
  `v4.33.0-rc1`, Mathlib `8e45b0548034eeda677a64e1e0b07837390835b6`.

## What it provides

`Complex.Hadamard.hadamard_factorization_of_order`: an entire `f` of order at most `ρ`, not
identically zero, factors as

    f z = exp (P z) * z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct ⌊ρ⌋ f univ z

with `P` a polynomial of degree at most `⌊ρ⌋`.  `..._of_growth` is the same conclusion from a
`log (1 + ‖f z‖)` growth bound; `..._reindex` and `..._sequence` restate the canonical product
over an arbitrary index type and over `ℕ` (as `Complex.canonicalProduct`); `..._centered` and its
two variants move the construction to an arbitrary center.

Underneath sit the pieces the classical proof consumes, each in its own file and each stated in
the form a Mathlib pull request would take: Weierstrass factors and canonical products, the zero
divisor of an entire function with its index type and fibers, convergence and removability of the
Hadamard quotient, Cartan's bound and its majorant/product/inverse-factor companions,
Borel--Carathéodory, `Real.posLog` and dyadic-log estimates, `EntireOfOrderAtMost`, log-counting
growth, and an annulus API in `Metric`.

## Quality audit

Read against this pin, not against the upstream CI.

* **Scale.** 35 files, 9,809 lines, 409 declarations.
* **Sorry-free and axiom-clean.**  No `sorry`, no `axiom`, no `native_decide`, no `unsafe`, no
  `partial def`, no `set_option maxHeartbeats`/`maxRecDepth` override anywhere in the subtree.
  `#print axioms` on `hadamard_factorization_of_order`, `hadamard_factorization_of_growth`,
  `hadamard_factorization_of_order_sequence` and `exists_entire_nonzero_hadamardQuotient` reports
  exactly `[propext, Classical.choice, Quot.sound]`, which is transitive and so covers the whole
  dependency chain rather than the headline files alone.
* **No undischarged hypothesis.**  The subtree declares **no `structure` and no `class` at all**, so
  there is no bundle standing in for an unproved analytic input -- the pattern our own trees use
  (`AtomicPickData`, `PacketFamily`) and the one that makes a result conditional without a `sorry`.
  Every binder on every headline theorem is an ordinary mathematical hypothesis (`0 ≤ ρ`, `f` not
  identically zero, `EntireOfOrderAtMost ρ f`, the last being a *definition* of finite order), and
  every instance binder is a standard Mathlib typeclass.  The results are unconditional.
* **Builds clean at our pin, with zero warnings**, as part of the shared `Vendor` library.
* **Namespace hygiene is good.**  `Complex.Hadamard` 160 declarations, `Complex` 77, `Metric` 70,
  `Complex.CartanBound` 38, `Real` 35, `Function.locallyFinsuppWithin` 10,
  `Complex.Hadamard.EntireOfOrderAtMost` 7, `MeromorphicOn` 6.  Six sit in the root namespace, and
  two of those (`Finset.prod_le_exp_sum`, `Differentiable.divisor_nonneg`) are dot-notation names
  rather than pollution; the other four are `hasProd_*` helpers in `CartanProductBound.lean`.
  Elaborating this subtree together with `Shields`, `Mathlib` and a paper's own library reports no
  clash.
* **Overlap with `Shields`.**  `Shields.Analysis.Complex.CanonicalProduct` is the genus-zero
  product `∏' n, (1 - z / aₙ)` under `∑ ‖aₙ‖⁻¹ < ∞`, indexed by `ℕ`; this subtree's
  `Complex.canonicalProduct` and `divisorCanonicalProduct` carry general genus `m` over the zero
  divisor.  Neither subsumes the other in the form each is stated, the names do not collide, and
  both are kept.
* **Attribution defect, repaired.**  `Analysis/Complex/Norm.lean`, `Analysis/Complex/AbsMax.lean`
  and `Analysis/Complex/BorelCaratheodory.lean` carry no copyright block upstream.  Each is given
  one here naming the author its commit history records, marked in the file as supplied.
* **Duplication of Mathlib, checked.**  `Analysis/Complex/BorelCaratheodory.lean` names the same
  theorem as Mathlib's own `Analysis/Complex/BorelCaratheodory.lean`, which exists at this pin; the
  vendored file is a different statement on a closed ball with an explicit constant, and it is kept
  because `CartanBound` consumes that form.  Nothing else in the subtree restates a declaration the
  pin already has -- the whole set elaborates without a duplicate-declaration error.

### Adaptations to the pin

Three, each marked inline at its site.

1. `HadamardFactorization/Summability.lean` -- `Ne.elim` is absent at this pin; `absurd` closes the
   same goal.
2. `Analysis/Complex/CartanBound.lean` -- `intervalIntegral.integral_lt_integral_of_ae_le_of_`
   `measure_setOf_lt_ne_zero` is deprecated in favour of the `setOfPred` spelling.
3. `Analysis/Complex/BorelCaratheodory.lean` -- `Set.mem_setOf_eq` is deprecated in favour of
   `Set.mem_ofPred_eq`.

## Retiring this directory

PNT+ writes these files under a `Mathlib/`-shaped path because they are meant to go upstream, but
**no Mathlib pull request carries them** as of this revision -- searched by title and body for
"Hadamard factorization", "canonical product" and "Weierstrass factor".  So the retirement
condition is not a merge of one PR: when the material lands in Mathlib, bump the pin and delete
this directory.  If the pin is bumped first, Lean reports duplicate declarations, which is the
intended failure mode.
-/
