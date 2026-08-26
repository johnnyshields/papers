/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ViewingAngle

/-!
# Producing the constants of `cor:linear-phase-variation`

`PhaseVariation.linear_phase_variation_regular` bounds the summed phase variation
by `κ₀ + (𝒦_γ + π)·deg B`, and takes both finite constants as hypotheses -- `𝒦_γ`
through a variation bound on the tangent angle, `κ₀` through one on the fixed
factor's branch.  `cor:linear-phase-variation` does not assume them: it *derives*
both from the closed-interval regularity of the arc, which is where its "depending
only on the denominator" comes from.

This module produces them.  A branch of the argument built by `logLift` has
derivative `Im(dγ/(γ-β))` at every parameter, so on a compact interval where the
arc misses `β` that derivative is bounded, the branch is Lipschitz, and a
Lipschitz function of a parameter has variation at most its constant times the
interval's length.  Nothing here is specific to the tangent angle, so one lemma
serves both constants: `𝒦_γ` is the case `γ := dγ`, `β := 0`, and `κ₀` the case of
whatever fixed factor the paper's last paragraph handles.

## Main statements

* `eVariationOn_polarAngle_le` -- a branch of `arg(γ - β)` has variation at most
  `K·(b-a)` on `[a,b]` when its derivative is bounded by `K` there.
* `exists_eVariationOn_polarAngle_le` -- the constant exists, from continuity on
  the compact interval alone, with no bound supplied.
-/

namespace ForgacsTran

open Set Filter

variable {γ dγ : ℝ → ℂ} {U : Set ℝ} {a b : ℝ} {β : ℂ}

/-- **The variation of an argument branch, from a bound on its derivative.**
`hasDerivAt_polarAngle` gives the branch derivative `Im(dγ/(γ-β))`; a pointwise
bound on a convex set makes the branch Lipschitz, and a Lipschitz function's
variation over an interval is at most its constant times the length.

**Differs from the paper's route.**  `cor:linear-phase-variation` gets finiteness
from real-analyticity of the arc on the closed interval, which makes the tangent
angle real-analytic and hence of bounded variation.  Here the bound is quantitative
and comes from the mean value theorem instead: `C^1` regularity plus a pointwise
derivative bound gives a Lipschitz constant, and Lipschitz gives variation.  The
paper's route yields finiteness with no constant; this one names the constant, and
needs one derivative rather than analyticity. -/
theorem eVariationOn_polarAngle_le (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hne : ∀ s ∈ Icc a b, γ s ≠ β)
    {K : ℝ} (hK : 0 ≤ K) (hbd : ∀ s ∈ Icc a b, |(dγ s / (γ s - β)).im| ≤ K) :
    eVariationOn (polarAngle γ dγ β a) (Icc a b) ≤ ENNReal.ofReal (K * (b - a)) := by
  classical
  set C : NNReal := ⟨K, hK⟩ with hC
  have hCK : ((C : NNReal) : ℝ) = K := rfl
  -- the branch is `C`-Lipschitz on the interval
  have hlip : LipschitzOnWith C (polarAngle γ dγ β a) (Icc a b) := by
    refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f := polarAngle γ dγ β a)
      (f' := fun s => (dγ s / (γ s - β)).im) (convex_Icc a b)
      (fun s hs => (hasDerivAt_polarAngle hU hsub hd hc hne hs).hasDerivWithinAt)
      (fun s hs => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, hCK]
    simpa [Real.norm_eq_abs] using hbd s hs
  -- variation of the identity over the interval is its length
  have hid : eVariationOn (id : ℝ → ℝ) (Icc a b) ≤ ENNReal.ofReal (b - a) := by
    have hmono : MonotoneOn (id : ℝ → ℝ) (Icc a b) := fun _ _ _ _ h => h
    have h := hmono.eVariationOn_eq (a := a) (b := b) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
    simpa using h.le
  have hcomp := hlip.comp_eVariationOn_le (g := (id : ℝ → ℝ)) (s := Icc a b)
    (Set.mapsTo_id _)
  rw [Function.comp_id] at hcomp
  refine hcomp.trans ?_
  calc (C : ENNReal) * eVariationOn (id : ℝ → ℝ) (Icc a b)
      ≤ (C : ENNReal) * ENNReal.ofReal (b - a) := by gcongr
    _ = ENNReal.ofReal (K * (b - a)) := by
        rw [← ENNReal.ofReal_coe_nnreal, hCK, ← ENNReal.ofReal_mul hK]

/-- **`cor:linear-phase-variation`'s constants exist**, from the arc's regularity
on the closed interval and nothing else.  This is the statement
`linear_phase_variation_regular` takes as `hKvar` and `h0`: on a compact interval
the branch derivative is continuous, hence bounded, so the variation is finite and
a constant can be named. -/
theorem exists_eVariationOn_polarAngle_le (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hγc : ContinuousOn γ U) (hne : ∀ s ∈ Icc a b, γ s ≠ β) :
    ∃ K : ℝ, 0 ≤ K ∧
      eVariationOn (polarAngle γ dγ β a) (Icc a b) ≤ ENNReal.ofReal (K * (b - a)) := by
  classical
  rcases eq_empty_or_nonempty (Icc a b) with hemp | hne'
  · refine ⟨0, le_rfl, ?_⟩
    rw [hemp, eVariationOn.subsingleton _ (by simp)]
    exact zero_le
  -- the branch derivative is continuous on the compact interval, hence bounded
  have hcont : ContinuousOn (fun s => |(dγ s / (γ s - β)).im|) (Icc a b) := by
    refine ContinuousOn.abs (Complex.continuous_im.comp_continuousOn ?_)
    exact ((hc.mono hsub).div ((hγc.mono hsub).sub continuousOn_const)
      fun s hs => sub_ne_zero.2 (hne s hs))
  obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMaxOn hne' hcont
  refine ⟨|(dγ s₀ / (γ s₀ - β)).im|, abs_nonneg _,
    eVariationOn_polarAngle_le hab hU hsub hd hc hne (abs_nonneg _) fun s hs => hmax hs⟩

/-- **`linear_phase_variation_regular`'s `hKvar`, produced.**  The tangent angle is
the argument branch of `dγ` about `0`, so `exists_eVariationOn_polarAngle_le` at
`γ := dγ`, `β := 0` gives the constant `𝒦_γ` of `cor:linear-phase-variation`
directly, from `C^2` regularity and regularity of the arc alone.

Stated in the binder's own shape -- a bare `ofReal Kγ` rather than the
`ofReal (K·(b-a))` the previous lemma produces -- so it composes with no bridging
step, and the length is absorbed into the constant exactly as the corollary's
"depending only on the denominator" permits. -/
theorem exists_tangent_angle_variation_bound {d2γ : ℝ → ℂ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hdc : ContinuousOn dγ U) (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0) :
    ∃ Kγ : ℝ, 0 ≤ Kγ ∧
      eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) ≤ ENNReal.ofReal Kγ := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_eVariationOn_polarAngle_le (γ := dγ) (dγ := d2γ) (β := 0) hab hU hsub hd2 hc2 hdc
      (by simpa using hreg)
  exact ⟨K * (b - a), mul_nonneg hK (by linarith), hbound⟩

end ForgacsTran
