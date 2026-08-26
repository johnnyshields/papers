/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.InteriorSupply

/-!
# The arc meets a zero of `B` never or exactly once

`PhaseVariationBlocks.sum_eVariationOn_branch_le` takes its state as a
**disjunction**: either the arc misses the zero `β` of `B` across the whole block
range, and one branch based at `a` serves every block; or it meets `β` at a single
`m`, and the blocks left of `m` take the branch based at `a` while those right of it
take the one based at `b`.

**What makes that disjunction exhaustive rather than a case list with a gap** is
that the branch is injective on the arc, so it cannot meet `β` twice.  There is no
third state, and this module is where that is established — before any of the
block bookkeeping, because everything downstream is shaped by it.

`InteriorSupply.injOn_ftPrincipal` is the injectivity: `arg (t_+(θ)) = θ` on
`Ioo 0 π` once the radius is positive, so distinct angles give distinct points.
The dichotomy below needs nothing else, and is stated for an arbitrary injective
map because nothing about the pencil enters it.

## Main statements

* `miss_or_meet_once` — an injective map either misses a value on a set or attains
  it at exactly one point of that set.
* `ftPrincipal_miss_or_meet_once` — the same at the principal branch, which is the
  form `hstate` is built from.
* `ftPrincipal_miss_and_meet_both_occur` — both branches are reachable, so the
  disjunction is not one case dressed as two.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `lem:viewing-angle`,
  `cor:linear-phase-variation`, `eq:principal-pair`.

## Tags

principal branch, injectivity, viewing angle, phase variation, block state
-/

namespace ForgacsTran

open Set Filter Complex
open scoped Topology

/-- **An injective map misses a value or attains it once.**  No third state, and
that is what makes the block-state disjunction exhaustive.

Stated for an arbitrary `Set.InjOn` because nothing about the pencil, the arc or
the polynomial enters: it is injectivity and excluded middle. -/
theorem miss_or_meet_once {α β : Type*} {γ : α → β} {K : Set α}
    (hinj : Set.InjOn γ K) (w : β) :
    (∀ x ∈ K, γ x ≠ w) ∨ (∃ m ∈ K, γ m = w ∧ ∀ x ∈ K, x ≠ m → γ x ≠ w) := by
  classical
  by_cases h : ∃ m ∈ K, γ m = w
  · obtain ⟨m, hm, hmw⟩ := h
    exact Or.inr ⟨m, hm, hmw, fun x hx hxm hxw => hxm (hinj hx hm (by rw [hxw, hmw]))⟩
  · push Not at h
    exact Or.inl h

/-- **The principal branch meets a zero of `B` never or exactly once.**  This is
the state `PhaseVariationBlocks.sum_eVariationOn_branch_le` splits on, before the
blocks are placed relative to the meeting point. -/
theorem ftPrincipal_miss_or_meet_once {τ : ℝ → ℝ} {K : Set ℝ} (hK : K ⊆ Ioo 0 Real.pi)
    (hτ : ∀ θ ∈ K, 0 < τ θ) (β : ℂ) :
    (∀ x ∈ K, ftPrincipal τ x ≠ β)
      ∨ (∃ m ∈ K, ftPrincipal τ m = β ∧ ∀ x ∈ K, x ≠ m → ftPrincipal τ x ≠ β) :=
  miss_or_meet_once (injOn_ftPrincipal hK hτ) β

/-- **Both branches occur.**  A value off the unit circle is missed on the whole
arc; a value on it is met, at one point.  Without this the dichotomy could be one
case wearing two names, and the composition would read as covering more than it
does — the same defect the dominance grid carried until its partition was checked. -/
theorem ftPrincipal_miss_and_meet_both_occur :
    (∃ (τ : ℝ → ℝ) (β : ℂ), (∀ θ ∈ Ioo 0 Real.pi, 0 < τ θ)
        ∧ ∀ x ∈ Ioo 0 Real.pi, ftPrincipal τ x ≠ β)
      ∧ (∃ (τ : ℝ → ℝ) (β : ℂ) (m : ℝ), (∀ θ ∈ Ioo 0 Real.pi, 0 < τ θ)
        ∧ m ∈ Ioo 0 Real.pi ∧ ftPrincipal τ m = β) := by
  constructor
  · refine ⟨fun _ => 1, 0, fun θ _ => one_pos, fun x _ hx => ?_⟩
    have hnorm : ‖ftPrincipal (fun _ => (1 : ℝ)) x‖ = 1 := by
      rw [ftPrincipal]
      simp [Complex.norm_exp]
    rw [hx] at hnorm
    simp at hnorm
  · refine ⟨fun _ => 1, ftPrincipal (fun _ => 1) (Real.pi / 2), Real.pi / 2,
      fun θ _ => one_pos, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩

/-! ### The crossing set is finite

`hstate` asks for a `Finset` containing every parameter where the two continuous
angles differ by an integer multiple of `π`.  That condition is one real equation —
the branch is tangent to the line from `β`, `Im(γ'·conj(γ - β)) = 0` — so the
crossing set is the zero set of a single real function and the `∀ j : ℤ` is
discharged once rather than per `j`.

**Finiteness needs the zeros to be isolated, and there are two ways to get that.**
Real-analyticity would do it, and is not available: nothing in this tree carries
analyticity of the branch, and the regularity that exists stops at `C²` and is
itself a hypothesis.  What is available is that the zeros are **simple** — the
tangency function crosses rather than touches — and a simple zero is isolated by
the derivative alone.  That is the route taken here, and it needs only `C¹`.

**Non-constancy is a real hypothesis, not a formality.**  A branch that ran
straight through `β` would make the tangency function vanish identically and the
crossing set would be the whole interval, with no finite set at all.  The
simple-zero hypothesis below is what excludes that, and supplying it at the
pencil's own branch is where the remaining work is. -/

/-- **A real function whose zeros are all simple has finitely many on a compact
set.**  If the zero set were infinite it would accumulate somewhere in the compact,
the limit point would itself be a zero by continuity, and its nonvanishing
derivative would keep the other zeros away from it.

Stated for an arbitrary differentiable `f`: no analyticity, and nothing about the
branch or the pencil. -/
theorem finite_zeros_of_hasDerivAt_ne_zero {f f' : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hd : ∀ x ∈ K, HasDerivAt f (f' x) x)
    (hsimple : ∀ x ∈ K, f x = 0 → f' x ≠ 0) :
    {x | x ∈ K ∧ f x = 0}.Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨p, hpK, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK (fun x hx => hx.1)
  haveI : (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0}).NeBot := hacc
  -- the accumulation point is itself a zero, by continuity along the zeros
  have hfp : f p = 0 := by
    have h1 : Filter.Tendsto f (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0})
        (𝓝 (f p)) :=
      (hd p hpK).continuousAt.tendsto.mono_left
        (le_trans inf_le_left nhdsWithin_le_nhds)
    have h2 : Filter.Tendsto f (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0})
        (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hz
      exact hz.2.symm
    exact tendsto_nhds_unique h1 h2
  -- and a simple zero keeps the others away
  have hev : ∀ᶠ z in 𝓝[≠] p, f z ≠ f p :=
    (hd p hpK).tendsto_nhdsNE (hsimple p hpK hfp) self_mem_nhdsWithin
  have hbad : ∀ᶠ _z in (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0}), False := by
    filter_upwards [Filter.mem_inf_of_left hev,
      Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z h1 h2
    exact h1 (by rw [h2.2, hfp])
  exact (Filter.eventually_false_iff_eq_bot.1 hbad ▸ (by infer_instance :
    (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0}).NeBot)).ne rfl

/-- **The finiteness is not vacuous on the side that matters.**  A conclusion of
finiteness is satisfied by having no zeros at all, so the witness carries one:
`f = id` on `Icc (-1) 1` has a simple zero at `0`, and the zero set is the
singleton rather than the empty set. -/
theorem finite_zeros_witness_nonempty :
    ∃ (f f' : ℝ → ℝ) (K : Set ℝ), IsCompact K ∧ (∀ x ∈ K, HasDerivAt f (f' x) x)
      ∧ (∀ x ∈ K, f x = 0 → f' x ≠ 0) ∧ (0 : ℝ) ∈ {x | x ∈ K ∧ f x = 0} := by
  refine ⟨id, fun _ => 1, Icc (-1) 1, isCompact_Icc, fun x _ => ?_,
    fun x _ _ => one_ne_zero, ⟨⟨by norm_num, by norm_num⟩, rfl⟩⟩
  simpa using hasDerivAt_id x

end ForgacsTran
