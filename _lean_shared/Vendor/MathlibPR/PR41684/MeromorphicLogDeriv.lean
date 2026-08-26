/-
Vendored from Mathlib pull request #41684, `feat: API for logarithmic derivatives of meromorphic functions`,
by Stefan Kebekus (GitHub `kebekus`).

  https://github.com/leanprover-community/mathlib4/pull/41684

The pull request is merged upstream but lands after the Mathlib revision pinned by this
repository, so the file is copied here verbatim, at upstream path `Mathlib/Analysis/Meromorphic/LogDeriv.lean`,
keeping upstream's namespaces, names and section scaffolding.  Only the Lean 4.34 module-system
syntax (`module`, `public import`, `public section`) is dropped, which the pinned toolchain does
not parse; no declaration, statement or proof is changed.  The pull request also adds declarations
to `Mathlib/Analysis/Calculus/LogDeriv.lean`, `Mathlib/Analysis/Meromorphic/Basic.lean` and
`Mathlib/Analysis/Meromorphic/Order.lean`, which the pinned Mathlib carries in their
pre-pull-request form; those declarations are copied at the end of this file.

When the Mathlib pin is bumped past the merge, delete this file and import the upstream module.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.Meromorphic.Order
-- Adapted to the pinned revision: upstream reaches `logDeriv` transitively through
-- `Mathlib.Analysis.Meromorphic.Order`, which the pinned `Order.lean` does not pull in.
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.IsolatedZeros

-- Adapted to the pinned revision: upstream's `MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero`
-- is the same statement under its pre-rename name.
alias MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero :=
  MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero

/-!
# Meromorphic API for the Logarithmic Derivative
-/

section

open Filter Function Set Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f g : 𝕜 → 𝕜'} {x : 𝕜} {U : Set 𝕜}

/-!
## Arithmetic on Codiscrete Sets

The pointwise lemma `logDeriv_mul` requires differentiability and nonvanishing of the factors at the
point in question. For meromorphic functions whose order is nowhere `⊤`, both conditions hold away
from a codiscrete set, turning the pointwise arithmetic into arithmetic of codiscrete equivalence
classes.
-/

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun MeromorphicOn.logDeriv_fun_mul_eventuallyEq]
theorem MeromorphicOn.logDeriv_mul_eventuallyEq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h'f : ∀ x ∈ U, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x ∈ U, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscreteWithin U] logDeriv f + logDeriv g := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero h'f,
    hg.eventually_codiscreteWithin_apply_ne_zero h'g]
    with y h₁y h₂y h₃y h₄y
  rw [Pi.add_apply]
  exact logDeriv_mul y h₃y h₄y h₁y.differentiableAt h₂y.differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun Meromorphic.logDeriv_fun_mul_eventuallyEq]
theorem Meromorphic.logDeriv_mul_eventuallyEq (hf : Meromorphic f) (hg : Meromorphic g)
    (h'f : ∀ x, meromorphicOrderAt f x ≠ ⊤) (h'g : ∀ x, meromorphicOrderAt g x ≠ ⊤) :
    logDeriv (f * g) =ᶠ[codiscrete 𝕜] logDeriv f + logDeriv g :=
  (meromorphicOn_univ.2 hf).logDeriv_mul_eventuallyEq (meromorphicOn_univ.2 hg)
    (fun x _ ↦ h'f x) (fun x _ ↦ h'g x)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun MeromorphicOn.logDeriv_fun_prod_eventuallyEq]
theorem MeromorphicOn.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, MeromorphicOn (F i) U)
    (h' : ∀ i ∈ s, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ i ∈ s, F i) =ᶠ[codiscreteWithin U] ∑ i ∈ s, logDeriv (F i) := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ s, F i y ≠ 0 :=
    (eventually_all_finset s).2 fun i hi ↦ (h i hi).eventually_codiscreteWithin_apply_ne_zero
      (h' i hi)
  filter_upwards [hA, hN] with y h₁y h₂y
  rw [Finset.sum_apply]
  -- Adapted to the pinned revision: the pointwise form of the Pi-type product is no longer
  -- definitionally transparent to `exact`, so it is rewritten first.
  have hfun : (∏ i ∈ s, F i) = fun x ↦ ∏ i ∈ s, F i x := funext fun x ↦ Finset.prod_apply x s F
  rw [hfun]
  exact logDeriv_prod h₂y fun i hi ↦ (h₁y i hi).differentiableAt

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
@[to_fun Meromorphic.logDeriv_fun_prod_eventuallyEq]
theorem Meromorphic.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, Meromorphic (F i)) (h' : ∀ i ∈ s, ∀ x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ i ∈ s, F i) =ᶠ[codiscrete 𝕜] ∑ i ∈ s, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_prod_eventuallyEq (fun i hi ↦ meromorphicOn_univ.mpr (h i hi))
  aesop

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
theorem MeromorphicOn.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscreteWithin U] ∑ᶠ i, logDeriv (F i) := by
  have hsub : support (fun i ↦ logDeriv (F i)) ⊆ hF.toFinset := by
    simp +contextual [Set.subset_def, not_imp_not, Pi.one_def]
  rw [finprod_eq_prod_of_mulSupport_subset F (s := hF.toFinset) (by simp),
    finsum_eq_sum_of_support_subset _ hsub]
  exact logDeriv_prod_eventuallyEq (fun i _ ↦ h i) (fun i _ ↦ h' i)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
theorem Meromorphic.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i) =ᶠ[codiscrete 𝕜] ∑ᶠ i, logDeriv (F i) := by
  apply MeromorphicOn.logDeriv_finprod_eventuallyEq hF (fun i ↦ meromorphicOn_univ.mpr (h i))
  aesop

/--
Away from a codiscrete subset of `U`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
-/
@[to_fun MeromorphicOn.logDeriv_fun_zpow_eventuallyEq]
theorem MeromorphicOn.logDeriv_zpow_eventuallyEq (hf : MeromorphicOn f U) (n : ℤ) :
    logDeriv (f ^ n) =ᶠ[codiscreteWithin U] n • logDeriv f := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  rw [Pi.smul_apply, zsmul_eq_mul, show f ^ n = (f · ^ n) from rfl]
  exact logDeriv_fun_zpow hy.differentiableAt n

/--
Away from a codiscrete subset of `𝕜`, the logarithmic derivative of the `n`-th power of a
meromorphic function is `n` times the logarithmic derivative.
-/
@[to_fun Meromorphic.logDeriv_fun_zpow_eventuallyEq]
theorem Meromorphic.logDeriv_zpow_eventuallyEq (hf : Meromorphic f) (n : ℤ) :
    logDeriv (f ^ n) =ᶠ[codiscrete 𝕜] n • logDeriv f := by
  apply MeromorphicOn.logDeriv_zpow_eventuallyEq (meromorphicOn_univ.mpr hf)


/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of integer powers of meromorphic functions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of statement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a divisor.
-/
theorem MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i, ∀ x ∈ U, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscreteWithin U] fun z ↦ ∑ᶠ i, d i • logDeriv (F i) z := by
  have hA : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, AnalyticAt 𝕜 (F i) y :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).analyticAt_mem_codiscreteWithin
  have hN : ∀ᶠ y in codiscreteWithin U, ∀ i ∈ hd.toFinset, F i y ≠ 0 :=
    (eventually_all_finset hd.toFinset).2 fun i _ ↦ (h i).eventually_codiscreteWithin_apply_ne_zero
      (h' i)
  filter_upwards [hA, hN] with y h₁y h₂y
  have h₀ : ∏ᶠ i, F i ^ d i = ∏ i ∈ hd.toFinset, F i ^ d i :=
    finprod_eq_prod_of_mulSupport_subset _ <| by simp +contextual [Set.subset_def, not_imp_not]
  have hsub : support (fun i ↦ d i • logDeriv (F i) y) ⊆ hd.toFinset := by
    simp +contextual [-support_mul, -mul_eq_zero, Set.subset_def, not_imp_not]
  calc logDeriv (∏ᶠ i, F i ^ d i) y
      = logDeriv (∏ i ∈ hd.toFinset, F i ^ d i) y := by rw [h₀]
    _ = ∑ i ∈ hd.toFinset, logDeriv (F i ^ d i) y := by
        -- Adapted to the pinned revision: the Pi-type product is rewritten pointwise before
        -- `logDeriv_prod`, which no longer unifies with it directly.
        have hfun : (∏ i ∈ hd.toFinset, F i ^ d i : 𝕜 → 𝕜')
            = fun x ↦ ∏ i ∈ hd.toFinset, (F i ^ d i) x :=
          funext fun x ↦ Finset.prod_apply x hd.toFinset _
        rw [hfun]
        exact logDeriv_prod (fun i hi ↦ zpow_ne_zero _ (h₂y i hi))
          (fun i hi ↦ ((h₁y i hi).zpow (h₂y i hi)).differentiableAt)
    _ = ∑ i ∈ hd.toFinset, d i • logDeriv (F i) y := by
        -- Adapted to the pinned revision: `Pi.pow_def` no longer puts the Pi-type power in the
        -- pointwise form `logDeriv_fun_zpow` expects, so the conversion is done by `rfl`.
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        have hfun : ((F i) ^ (d i) : 𝕜 → 𝕜') = fun x ↦ (F i x) ^ (d i) := rfl
        rw [hfun, zsmul_eq_mul]
        exact logDeriv_fun_zpow (h₁y i hi).differentiableAt (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) y := (finsum_eq_sum_of_support_subset _ hsub).symm

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `𝕜`, the
logarithmic derivative of a finite product of integer powers of meromorphic functions is the
corresponding weighted sum of logarithmic derivatives. This is the shape of statement used in the
differentiated Poisson–Jensen formula, where the exponents are given by a divisor.
-/
theorem Meromorphic.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x ≠ ⊤) :
    logDeriv (∏ᶠ i, F i ^ d i)
      =ᶠ[codiscrete 𝕜] fun z ↦ ∑ᶠ i, d i • logDeriv (F i) z := by
  apply MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd (fun i ↦ meromorphicOn_univ.mpr (h i))
  aesop

/-!
## Declarations the pull request adds to `Mathlib/Analysis/Calculus/LogDeriv.lean` and
`Mathlib/Analysis/Meromorphic/Order.lean`
-/

section CalculusLogDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

/-- If two functions agree in a neighborhood of `x`, then so do their logarithmic derivatives. -/
lemma logDeriv_congr_nhds {f g : 𝕜 → 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝 x] g) :
    logDeriv f =ᶠ[𝓝 x] logDeriv g := h.deriv.div h

/--
If two functions agree in a punctured neighborhood of `x`, then so do their logarithmic derivatives.
-/
lemma logDeriv_congr_nhdsNE {f g : 𝕜 → 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝[≠] x] g) :
    logDeriv f =ᶠ[𝓝[≠] x] logDeriv g := h.nhdsNE_deriv.div h

/--
If two functions agree on a codiscrete subset of an open set `U`, then so do their logarithmic
derivatives.
-/
theorem logDeriv_congr_codiscreteWithin {f g : 𝕜 → 𝕜'} {U : Set 𝕜} (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) :
    logDeriv f =ᶠ[codiscreteWithin U] logDeriv g := by
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx ↦ ?_
  refine mem_of_superset (logDeriv_congr_nhdsNE ?_) Set.subset_union_left
  filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx,
    nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz hzU
  exact hz.resolve_right (not_not_intro hzU)

/--
If two functions agree on a codiscrete subset of `𝕜`, then so do their logarithmic derivatives.
-/
theorem logDeriv_congr_codiscrete {f g : 𝕜 → 𝕜'} (h : f =ᶠ[codiscrete 𝕜] g) :
    logDeriv f =ᶠ[codiscrete 𝕜] logDeriv g :=
  logDeriv_congr_codiscreteWithin isOpen_univ h

end CalculusLogDeriv

section MeromorphicOrder

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}

/--
At zeros and poles of a meromorphic function `f`, the logarithmic derivative has a simple pole: its
meromorphic order equals `-1`.
-/
theorem meromorphicOrderAt_logDeriv_eq_neg_one [CharZero 𝕜] (hf : MeromorphicAt f x)
    (h₁ : meromorphicOrderAt f x ≠ 0) (h₂ : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicOrderAt (logDeriv f) x = -1 := by
  lift meromorphicOrderAt f x to ℤ using h₂ with n hn
  rw [logDeriv, meromorphicOrderAt_div hf.deriv hf,
    meromorphicOrderAt_deriv_eq_sub_one (Int.cast_ne_zero.mpr (by exact_mod_cast h₁)) hn.symm,
    ← hn]
  norm_cast
  simp

/--
At points where a meromorphic function has order zero, the meromorphic order of the logarithmic
derivative is nonnegative.
-/
theorem meromorphicOrderAt_logDeriv_nonneg (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x = 0) :
    0 ≤ meromorphicOrderAt (logDeriv f) x := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by exact_mod_cast h)
  have h₄ : f =ᶠ[𝓝[≠] x] g := by
    filter_upwards [h₃g] with z hz using by simpa using hz
  rw [meromorphicOrderAt_congr (logDeriv_congr_nhdsNE h₄)]
  exact (h₁g.deriv.div h₁g h₂g).meromorphicOrderAt_nonneg

end MeromorphicOrder

section MeromorphicBasic

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {x : 𝕜}

-- Adapted to the pinned revision: the pull request also moves `MeromorphicOn.logDeriv` and
-- `Meromorphic.logDeriv` into this module from
-- `Mathlib/Analysis/SpecialFunctions/Complex/LogDeriv.lean`, where the pinned Mathlib already
-- carries them under the same names, so only the new `MeromorphicAt` statement is copied.
/-- If `f` is meromorphic at a point, then so is its logarithmic derivative. -/
@[fun_prop] theorem MeromorphicAt.logDeriv [CompleteSpace 𝕜'] {f : 𝕜 → 𝕜'}
    (hf : MeromorphicAt f x) :
    MeromorphicAt (logDeriv f) x := hf.deriv.div hf

end MeromorphicBasic
