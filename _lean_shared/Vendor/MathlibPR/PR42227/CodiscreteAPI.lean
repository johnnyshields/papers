/-
Vendored from Mathlib pull request #42227, `feat: API for (co)discrete sets`, by Stefan Kebekus
(GitHub `kebekus`).

  https://github.com/leanprover-community/mathlib4/pull/42227

The pull request is merged upstream but lands after the Mathlib revision pinned by this repository.
Copied here are the declarations it adds to `Mathlib/Topology/DiscreteSubset.lean`,
`Mathlib/Algebra/Polynomial/Roots.lean`, `Mathlib/Topology/Algebra/Polynomial.lean`,
`Mathlib/Analysis/Calculus/FDeriv/Congr.lean` and `Mathlib/Analysis/Calculus/Deriv/Basic.lean`,
keeping upstream's namespaces, names, statements and proofs, so consuming code is written exactly
as it will be against a merged Mathlib.  The declarations the pinned Mathlib already carries are not
copied.

One of the pull request's declarations is dropped on that rule.
`Polynomial.eventually_cofinite_not_isRoot` is already in the pinned Mathlib, at
`Mathlib/Analysis/Polynomial/Basic.lean`, with the same statement and the same proof.  Copying it
makes any module that reaches both this file and that one fail to import, so
`Mathlib.Analysis.Polynomial.Basic` is imported here instead and `eventually_eval_ne_zero_cofinite`
below resolves to the upstream copy.

When the Mathlib pin is bumped past the merge, delete this file and import the upstream modules.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Bhavik Mehta, Daniel Weber, Stefan Kebekus
-/

/-
The `Polynomial` section below is taken from two further modules, whose own copyright lines are:

Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin

Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Algebra.Polynomial

open Set Filter Function Topology

variable {X Z : Type*} [TopologicalSpace X] {s : Set X} {g₁ g₂ : X → Z}

section codiscrete_filter

/-- A set `S` is codiscrete within `T` iff it is a punctured neighborhood within `T` of every
point of `T`. -/
theorem mem_codiscreteWithin_iff_forall_mem_nhdsWithin {S T : Set X} :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, S ∈ 𝓝[T \ {x}] x := by
  simp [codiscreteWithin]

/-- At every point `x` of `T`, the punctured neighborhood filter within `T` is finer than
`codiscreteWithin T`. -/
theorem nhdsWithin_le_codiscreteWithin {T : Set X} {x : X} (hx : x ∈ T) :
    𝓝[T \ {x}] x ≤ codiscreteWithin T :=
  le_iSup₂ (f := fun y (_ : y ∈ T) ↦ 𝓝[T \ {y}] y) x hx

/-- A property holds along `codiscreteWithin U` iff, for every point `x` of `U`, it holds along
the punctured neighborhood of `x`, at every point of `U`. -/
theorem eventually_codiscreteWithin_iff_forall_eventually_nhdsNE {p : X → Prop} :
    (∀ᶠ x in codiscreteWithin s, p x) ↔ ∀ x ∈ s, ∀ᶠ y in 𝓝[≠] x, y ∈ s → p y := by
  simp [mem_codiscreteWithin_iff_forall_mem_nhdsNE, Filter.eventually_iff, Set.union_def,
    imp_iff_not_or, or_comm]

/-- Two functions agree along `codiscreteWithin U` iff, for every point `x` of `U`, they agree
along the punctured neighborhood of `x`, at every point of `U`. -/
theorem eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE :
    g₁ =ᶠ[codiscreteWithin s] g₂ ↔ ∀ x ∈ s, ∀ᶠ y in 𝓝[≠] x, y ∈ s → g₁ y = g₂ y :=
  eventually_codiscreteWithin_iff_forall_eventually_nhdsNE

/-- A property holds along `codiscreteWithin U` iff, for every point `x` of `U`, it holds along
the punctured neighborhood within `U` of `x`. -/
theorem eventually_codiscreteWithin_iff_forall_eventually_nhdsWithin {p : X → Prop} :
    (∀ᶠ x in codiscreteWithin s, p x) ↔ ∀ x ∈ s, ∀ᶠ y in 𝓝[s \ {x}] x, p y :=
  mem_codiscreteWithin_iff_forall_mem_nhdsWithin

/-- Two functions agree along `codiscreteWithin U` iff, for every point `x` of `U`, they agree
along the punctured neighborhood within `U` of `x`. -/
theorem eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsWithin :
    g₁ =ᶠ[codiscreteWithin s] g₂ ↔ ∀ x ∈ s, g₁ =ᶠ[𝓝[s \ {x}] x] g₂ :=
  eventually_codiscreteWithin_iff_forall_eventually_nhdsWithin

/-- A set is codiscrete iff it is a punctured neighborhood of every point. -/
lemma mem_codiscrete_iff_forall_mem_nhdsNE :
    s ∈ Filter.codiscrete X ↔ ∀ x, s ∈ 𝓝[≠] x := by
  simp [Filter.codiscrete, mem_codiscreteWithin_iff_forall_mem_nhdsNE]

/-- At every point, the punctured neighborhood filter is finer than the codiscrete filter. -/
lemma nhdsNE_le_codiscrete (x : X) : 𝓝[≠] x ≤ Filter.codiscrete X := by
  simpa [Filter.codiscrete, ← compl_eq_univ_sdiff] using
    nhdsWithin_le_codiscreteWithin (T := univ) (mem_univ x)

/--
A property holds along the codiscrete filter iff it holds along the punctured neighborhood of
every point. -/
lemma eventually_codiscrete_iff_forall_eventually_nhdsNE {p : X → Prop} :
    (∀ᶠ x in Filter.codiscrete X, p x) ↔ ∀ x, ∀ᶠ y in 𝓝[≠] x, p y :=
  mem_codiscrete_iff_forall_mem_nhdsNE

/--
Two functions agree along the codiscrete filter iff they agree along the punctured neighborhood of
every point. -/
lemma eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE :
    g₁ =ᶠ[Filter.codiscrete X] g₂ ↔ ∀ x, g₁ =ᶠ[𝓝[≠] x] g₂ :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE

end codiscrete_filter

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Nonzero polynomials are nonzero away from a finite set. -/
lemma eventually_eval_ne_zero_cofinite {p : R[X]} (hp : p ≠ 0) :
    ∀ᶠ x in Filter.cofinite, p.eval x ≠ 0 :=
  eventually_cofinite_not_isRoot hp

variable {F : Type*} [CommRing F]

/-- Nonzero polynomials are nonzero away from a codiscrete set. -/
lemma eventually_eval_ne_zero_codiscrete [IsDomain F] [TopologicalSpace F] [T1Space F]
    {g : F[X]} (hg : g ≠ 0) :
    ∀ᶠ z in codiscrete F, g.eval z ≠ 0 :=
  (eventually_eval_ne_zero_cofinite hg).filter_mono codiscrete_le_cofinite

end Polynomial

section FDerivCongr

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable {f f₁ : E → F}
variable {s t : Set E}

/-- If two functions agree on a codiscrete subset of `s`, then so do their derivatives within
any subset `t` of `s`. -/
theorem Filter.EventuallyEq.codiscreteWithin_fderivWithin'
    (h : f₁ =ᶠ[codiscreteWithin s] f) (ht : t ⊆ s) :
    fderivWithin 𝕜 f₁ t =ᶠ[codiscreteWithin s] fderivWithin 𝕜 f t := by
  filter_upwards [h, self_mem_codiscreteWithin s] with x hx hxs
  have hsx : f₁ =ᶠ[𝓝[s] x] f := by
    rw [← insert_sdiff_self_of_mem hxs, nhdsWithin_insert, EventuallyEq,
      eventually_sup, eventually_pure]
    exact ⟨hx, eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsWithin.1 h x hxs⟩
  exact (hsx.filter_mono <| nhdsWithin_mono x ht).fderivWithin_eq hx

/-- If two functions agree on a codiscrete subset of `s`, then so do their derivatives
within `s`. -/
theorem Filter.EventuallyEq.codiscreteWithin_fderivWithin
    (h : f₁ =ᶠ[codiscreteWithin s] f) :
    fderivWithin 𝕜 f₁ s =ᶠ[codiscreteWithin s] fderivWithin 𝕜 f s :=
  h.codiscreteWithin_fderivWithin' Subset.rfl

/-- If two functions agree on a codiscrete subset of an open set `s`, then so do their
derivatives. -/
theorem Filter.EventuallyEq.codiscreteWithin_fderiv
    (h : f₁ =ᶠ[codiscreteWithin s] f) (hs : IsOpen s) :
    fderiv 𝕜 f₁ =ᶠ[codiscreteWithin s] fderiv 𝕜 f := by
  filter_upwards [h.codiscreteWithin_fderivWithin (𝕜 := 𝕜), self_mem_codiscreteWithin s]
  intro x hx hxs
  simp_all [fderivWithin_of_isOpen]

/-- If two functions agree on a codiscrete subset of `E`, then so do their derivatives within
any subset `s` of `E`. -/
theorem Filter.EventuallyEq.codiscrete_fderivWithin
    (h : f₁ =ᶠ[codiscrete E] f) :
    fderivWithin 𝕜 f₁ s =ᶠ[codiscrete E] fderivWithin 𝕜 f s :=
  h.codiscreteWithin_fderivWithin' <| subset_univ _

/-- If two functions agree on a codiscrete subset of `E`, then so do their derivatives. -/
theorem Filter.EventuallyEq.codiscrete_fderiv
    (h : f₁ =ᶠ[codiscrete E] f) :
    fderiv 𝕜 f₁ =ᶠ[codiscrete E] fderiv 𝕜 f :=
  h.codiscreteWithin_fderiv isOpen_univ

end FDerivCongr

section DerivBasic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f f₁ : 𝕜 → F}
variable {s t : Set 𝕜}

/--
If two functions agree on a codiscrete subset of `s`, then so do their derivatives within any
subset `t` of `s`.
-/
theorem Filter.EventuallyEq.codiscreteWithin_derivWithin'
    (h : f₁ =ᶠ[codiscreteWithin s] f) (ht : t ⊆ s) :
    derivWithin f₁ t =ᶠ[codiscreteWithin s] derivWithin f t := by
  filter_upwards [h.codiscreteWithin_fderivWithin' (𝕜 := 𝕜) ht] with y hy
  simp [derivWithin, hy]

/--
If two functions agree on a codiscrete subset of `s`, then so do their derivatives within `s`.
-/
theorem Filter.EventuallyEq.codiscreteWithin_derivWithin
    (h : f₁ =ᶠ[codiscreteWithin s] f) :
    derivWithin f₁ s =ᶠ[codiscreteWithin s] derivWithin f s :=
  h.codiscreteWithin_derivWithin' Subset.rfl

/--
If two functions agree on a codiscrete subset of an open set `s`, then so do their derivatives.
-/
theorem Filter.EventuallyEq.codiscreteWithin_deriv (h : f₁ =ᶠ[codiscreteWithin s] f)
    (hs : IsOpen s) :
    deriv f₁ =ᶠ[codiscreteWithin s] deriv f := by
  filter_upwards [h.codiscreteWithin_fderiv (𝕜 := 𝕜) hs] with y hy
  simp_rw [deriv, hy]

/-- If two functions agree on a codiscrete subset of `𝕜`, then so do their derivatives within
any subset `s` of `𝕜`. -/
theorem Filter.EventuallyEq.codiscrete_derivWithin
    (h : f₁ =ᶠ[codiscrete 𝕜] f) :
    derivWithin f₁ s =ᶠ[codiscrete 𝕜] derivWithin f s :=
  h.codiscreteWithin_derivWithin' <| subset_univ _

/-- If two functions agree on a codiscrete subset of `𝕜`, then so do their derivatives. -/
theorem Filter.EventuallyEq.codiscrete_deriv
    (h : f₁ =ᶠ[codiscrete 𝕜] f) :
    deriv f₁ =ᶠ[codiscrete 𝕜] deriv f :=
  h.codiscreteWithin_deriv isOpen_univ

end DerivBasic
