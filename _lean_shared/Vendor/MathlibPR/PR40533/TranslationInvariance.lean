/-
Vendored from Mathlib pull request #40533, `feat: translation invariance of meromorphicity`,

  https://github.com/leanprover-community/mathlib4/pull/40533

by Stefan Kebekus (GitHub `kebekus`).  The pull request is merged upstream but postdates the
Mathlib revision pinned by this repository.

The pull request establishes that every notion carrying the word "meromorphic" is invariant under
translation, together with the pointwise-set and analytic-order lemmas the proofs consume.  It
touches eight Mathlib modules; the declarations absent from the pinned revision are collected here
in dependency order, keeping upstream namespaces, names, statements and proofs, so consuming code is
written exactly as it will be against a merged Mathlib.

When this material reaches the Mathlib pin, delete this file.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Pointwise

/-!
## Translation invariance of meromorphicity
-/

/-!
### `Mathlib/Analysis/Normed/Group/Basic.lean`
-/

section NormedGroupBasic

open Metric Set

variable {E : Type*} [SeminormedCommGroup E] {a : E} {r : ℝ}

-- Adapted to the pinned revision, twice: at the pin the norm characterizations of ball, closed ball
-- and sphere membership require `SeminormedCommGroup`, where upstream states them over
-- `SeminormedGroup`, so these three are vendored at the narrower typeclass; and the proofs go
-- through `dist_eq_norm_div` rather than the membership lemmas, which the pin's `simp` set does not
-- apply after it has already normalized membership to a distance inequality.
/-- A scaled ball is a ball. -/
@[to_additive setOf_sub_mem_ball_eq_ball /-- A translated ball is a ball. -/]
theorem setOf_div_mem_ball_eq_ball'' :
    {x | x / a ∈ ball 1 r} = Metric.ball a r := by
  ext x
  simp [dist_eq_norm_div]

/-- A scaled closed ball is a closed ball. -/
@[to_additive setOf_sub_mem_closedBall_eq_closedBall
  /-- A translated closed ball is a closed ball. -/]
theorem setOf_div_mem_closedBall_eq_closedBall'' :
    {x | x / a ∈ closedBall 1 r} = Metric.closedBall a r := by
  ext x
  simp [dist_eq_norm_div]

/-- A scaled sphere is a sphere. -/
@[to_additive setOf_sub_mem_sphere_eq_sphere /-- A translated sphere is a sphere. -/]
theorem setOf_div_mem_sphere_eq_sphere'' :
    {x | x / a ∈ sphere 1 r} = Metric.sphere a r := by
  ext x
  simp

end NormedGroupBasic

/-!
### `Mathlib/Analysis/Normed/Group/Pointwise.lean`
-/

section NormedGroupPointwise

open Metric Set Pointwise Topology

variable {E : Type*} [SeminormedCommGroup E] {δ : ℝ} {x y : E}

@[to_additive (attr := simp)]
theorem inv_sphere : (sphere x δ)⁻¹ = sphere x⁻¹ δ :=
  (IsometryEquiv.inv E).preimage_sphere x δ

@[to_additive (attr := simp 1100)]
theorem singleton_mul_sphere : {x} * sphere y δ = sphere (x * y) δ := by
  simp_rw [singleton_mul, ← smul_eq_mul, image_smul, smul_sphere]

@[to_additive (attr := simp 1100)]
theorem singleton_div_sphere : {x} / sphere y δ = sphere (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_sphere, singleton_mul_sphere]

@[to_additive (attr := simp 1100)]
theorem sphere_mul_singleton : sphere x δ * {y} = sphere (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]

@[to_additive (attr := simp 1100)]
theorem sphere_div_singleton : sphere x δ / {y} = sphere (x / y) δ := by
  simp [div_eq_mul_inv]

@[to_additive]
theorem singleton_mul_sphere_one : {x} * sphere 1 δ = sphere x δ := by simp

@[to_additive]
theorem singleton_div_sphere_one : {x} / sphere 1 δ = sphere x δ := by
  rw [singleton_div_sphere, div_one]

@[to_additive]
theorem sphere_one_mul_singleton : sphere 1 δ * {x} = sphere x δ := by simp

@[to_additive]
theorem sphere_one_div_singleton : sphere 1 δ / {x} = sphere x⁻¹ δ := by simp

@[to_additive (attr := simp 1100)]
theorem smul_sphere_one : x • sphere (1 : E) δ = sphere x δ := by simp

end NormedGroupPointwise

/-!
### `Mathlib/Analysis/Analytic/Order.lean`
-/

section AnalyticOrder

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The analytic order of the function `(· - c)` at `x` is one if `x = c`. -/
@[simp] theorem analyticOrderAt_id_sub_const_self {c : 𝕜} :
    analyticOrderAt (· - c) c = 1 := by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := c)
  simp_all [pow_one]

/-- The analytic order of the function `(· - c)` at `x` is zero if `x ≠ c`. -/
@[simp] theorem analyticOrderAt_id_sub_const_of_ne {c x : 𝕜} (h : x ≠ c) :
    analyticOrderAt (· - c) x = 0 := by
  apply analyticOrderAt_eq_zero.2
  grind

end AnalyticOrder

/-!
### `Mathlib/Analysis/Meromorphic/Basic.lean`
-/

section MeromorphicBasic

open Filter Metric Set
open scoped Pointwise Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {x : 𝕜} {f : 𝕜 → E}

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_add_const_iff_meromorphicAt]
theorem meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· + c)) x ↔ MeromorphicAt f (x + c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show f = ((f ∘ fun x ↦ x + c) ∘ fun z ↦ z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_sub_const_iff_meromorphicAt]
theorem meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· - c)) x ↔ MeromorphicAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicAt_comp_add_const_iff_meromorphicAt]

namespace MeromorphicOn

/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_add_const_iff_meromorphicOn]
theorem meromorphicOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· + c)) U ↔ MeromorphicOn f (U + {c}) := by
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicAt_comp_add_const_iff_meromorphicAt] using h x h₁x
  · rw [meromorphicAt_comp_add_const_iff_meromorphicAt]
    aesop

/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_sub_const_iff_meromorphicOn]
theorem meromorphicOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· - c)) U ↔ MeromorphicOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicOn_comp_add_const_iff_meromorphicOn, neg_singleton]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicOn_ball_fun_comp_sub_const_iff_meromorphicOn_ball]
theorem meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicOn f (ball 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, ball_sub_singleton, sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a closed ball. -/
@[to_fun (attr := simp) meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall]
theorem meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicOn f (closedBall 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, closedBall_sub_singleton, sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicOn_sphere_fun_comp_sub_const_iff_meromorphicOn_sphere]
theorem meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicOn f (sphere 0 R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, sphere_sub_singleton, sub_self]

end MeromorphicOn

namespace Meromorphic

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· + c)) ↔ Meromorphic f := by
  rw [Meromorphic, Meromorphic, (Equiv.subRight c).surjective.forall]
  simp [meromorphicAt_comp_add_const_iff_meromorphicAt]

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_fun_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z ↦ f (z + c)) ↔ Meromorphic f :=
  meromorphic_comp_add_const_iff_meromorphic

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· - c)) ↔ Meromorphic f := by
  nth_rw 2 [← meromorphic_comp_add_const_iff_meromorphic (c := -c)]
  simp_rw [sub_eq_add_neg]

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_fun_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z ↦ f (z - c)) ↔ Meromorphic f :=
  meromorphic_comp_sub_const_iff_meromorphic

end Meromorphic

end MeromorphicBasic

/-!
### `Mathlib/Analysis/Meromorphic/Order.lean`
-/

section MeromorphicOrder

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {x : 𝕜}

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
theorem meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ (· + c)) x = meromorphicOrderAt f (x + c) := by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicOrderAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E} :
    meromorphicOrderAt (f ∘ (· - c)) x = meromorphicOrderAt f (x - c) := by
  simp_rw [sub_eq_add_neg, ← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

end MeromorphicOrder

/-!
### `Mathlib/Analysis/Meromorphic/Divisor.lean`
-/

namespace MeromorphicOn

open Filter Metric Topology
open scoped Pointwise

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The divisor of a function `f` evaluates to zero if `f` is not meromorphic. -/
@[simp] theorem divisor_eq_zero_of_not_meromorphicOn {f : 𝕜 → E} (hf : ¬ MeromorphicOn f U) :
    divisor f U z = 0 := by
  unfold divisor
  aesop

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_add_const_eq_divisor]
theorem divisor_comp_add_const_eq_divisor {c x : 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· + c)) U (x - c) = divisor f (U + {c}) x := by
  by_cases h : ¬ MeromorphicOn f (U + {c})
  · have := meromorphicOn_comp_add_const_iff_meromorphicOn.not.2 h
    simp_all
  rw [not_not] at h
  have := meromorphicOn_comp_add_const_iff_meromorphicOn.2 h
  by_cases h₁ : ¬ x ∈ (U + {c})
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    <;> simp_all [← sub_eq_add_neg]
  rw [divisor_apply, divisor_apply]
  <;> simp_all [← sub_eq_add_neg, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_sub_const_eq_divisor]
theorem divisor_comp_sub_const_eq_divisor {c : 𝕜} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) U (z + c) = divisor f (U - {c}) z := by
  rw [sub_eq_add_neg, Set.neg_singleton, ← divisor_comp_add_const_eq_divisor]
  simp_rw [← sub_eq_add_neg, sub_neg_eq_add]

/-- Divisors are invariant under translation, special case where the set is a ball.. -/
@[to_fun (attr := simp) divisor_ball_fun_comp_sub_const_eq_divisor_ball]
theorem divisor_ball_comp_sub_const_eq_divisor_ball {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (ball c R) (z + c) = divisor f (ball 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor, ball_sub_singleton, sub_self]

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[to_fun (attr := simp) divisor_closedBall_fun_comp_sub_const_eq_divisor_closedBall]
theorem divisor_closedBall_comp_sub_const_eq_divisor_closedBall {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (closedBall c R) (z + c) = divisor f (closedBall 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor, closedBall_sub_singleton, sub_self]

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) divisor_sphere_fun_comp_sub_const_eq_divisor_sphere]
theorem divisor_sphere_comp_sub_const_eq_divisor_sphere {c : 𝕜} {R : ℝ} {f : 𝕜 → E} :
    divisor (f ∘ (· - c)) (sphere c R) (z + c) = divisor f (sphere 0 R) z := by
  rw [divisor_comp_sub_const_eq_divisor, sphere_sub_singleton, sub_self]

end MeromorphicOn

/-!
### `Mathlib/Analysis/Meromorphic/TrailingCoefficient.lean`
-/

section MeromorphicTrailingCoefficient

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {x : 𝕜} {f : 𝕜 → E}

/--
If `g` is analytic at `x` and not locally constant, and `f` is meromorphic at `g x`, express the
trailing coefficient of `f ∘ g` at `x` in terms of `g` and `f`.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_comp {g : 𝕜 → 𝕜} (hf : MeromorphicAt f (g x))
    (hg : AnalyticAt 𝕜 g x) (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicTrailingCoeffAt (f ∘ g) x =
      (meromorphicTrailingCoeffAt (g · - g x) x) ^ (meromorphicOrderAt f (g x)).untop₀ •
      meromorphicTrailingCoeffAt f (g x) := by
  by_cases h : meromorphicOrderAt f (g x) = ⊤
  · have : meromorphicTrailingCoeffAt (f ∘ g) x = 0 := by
      apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      rw [meromorphicOrderAt_eq_top_iff] at *
      exact (hg.map_nhdsNE hg_nc) h
    aesop
  · set r := (meromorphicOrderAt f (g x)).untop₀
    obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    have h₁ : meromorphicTrailingCoeffAt (f ∘ g) x
        = meromorphicTrailingCoeffAt ((g · - g x) ^ r • (F ∘ g)) x := by
      apply meromorphicTrailingCoeffAt_congr_nhdsNE
      apply Filter.Tendsto.eventually (hg.map_nhdsNE hg_nc) h₃F
    rw [h₁, MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop) (by fun_prop),
      (h₁F.comp hg).meromorphicTrailingCoeffAt_of_ne_zero h₂F,
      h₁F.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂F h₃F]
    simp_all only [ne_eq, Function.comp_apply, not_false_eq_true, smul_left_inj]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)

/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt]
theorem meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt {c : 𝕜} :
    meromorphicTrailingCoeffAt (f ∘ (· + c)) x = meromorphicTrailingCoeffAt f (x + c) := by
  classical
  by_cases h : ¬ MeromorphicAt f (x + c)
  · simp_all [meromorphicAt_comp_add_const_iff_meromorphicAt.not.2 h]
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (by simp_all) (by fun_prop)
    (by simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top])]
  simp [meromorphicTrailingCoeffAt_id_sub_const]

/-- `meromorphicTrailingCoefficientAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_sub_const_eq_meromorphicTrailingCoeffAt]
theorem meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt {c : 𝕜} :
    meromorphicTrailingCoeffAt (f ∘ (· - c)) x = meromorphicTrailingCoeffAt f (x - c) := by
  simp [sub_eq_add_neg, ← meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt]

end MeromorphicTrailingCoefficient

/-!
### `Mathlib/Analysis/Meromorphic/NormalForm.lean`
-/

section MeromorphicNormalForm

open Metric Set Topology WithTop
open scoped Pointwise

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {x : 𝕜} {f : 𝕜 → E}

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt]
theorem meromorphicNFAt_comp_add_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicNFAt (f ∘ (· + c)) x ↔ MeromorphicNFAt f (x + c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show f = ((f ∘ fun x ↦ x + c) ∘ fun z ↦ z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_sub_const_iff_meromorphicNFAt]
theorem meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicNFAt (f ∘ (· - c)) x ↔ MeromorphicNFAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_add_const_iff_meromorphicNFOn]
theorem meromorphicNFOn_comp_add_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· + c)) U ↔ MeromorphicNFOn f (U + {c}) := by
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicNFAt_comp_add_const_iff_meromorphicNFAt] using h h₁x
  · rw [meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]
    aesop

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_sub_const_iff_meromorphicNFOn]
theorem meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· - c)) U ↔ MeromorphicNFOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicNFOn_comp_add_const_iff_meromorphicNFOn, neg_singleton]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicNFOn_ball_fun_comp_sub_const_iff_meromorphicNFOn_ball]
theorem meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicNFOn f (ball 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, ball_sub_singleton, sub_self]

/--
`MeromorphicNFOn` is invariant under translation, special case where the set is a closed ball.
-/
@[to_fun (attr := simp)
  meromorphicNFOn_closedBall_fun_comp_sub_const_iff_meromorphicNFOn_closedBall]
theorem meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicNFOn f (closedBall 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, closedBall_sub_singleton, sub_self]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicNFOn_sphere_fun_comp_sub_const_iff_meromorphicNFOn_sphere]
theorem meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicNFOn f (sphere 0 R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, sphere_sub_singleton, sub_self]

end MeromorphicNormalForm
