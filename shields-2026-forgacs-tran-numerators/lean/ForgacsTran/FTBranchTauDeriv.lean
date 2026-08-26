/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchDeriv

/-!
# The `τ`-derivative of the angle system

The second partial derivative of the angle system of
`Forgacs2017RationalDenominator` Lemma 2, and the joint continuity that the
implicit function argument of `FTBranchRegularity` needs.

## Main statements

* `hasDerivAt_ftAngle_tau` — `∂θ_k/∂τ = -sin²θ_k · τ_k /(τ² sin θ)`, and
  `ftAngleSumDerivTau` sums it.
* `ftAngleSumDerivTau_neg` — it is strictly negative, which is the
  non-degeneracy the branch equation is solved with.
* `continuousOn_ftAngleSumDerivTau` — joint continuity in `(τ, θ)`.
* `exists_hasDerivAt_eq_sub_uIcc` — the mean value theorem on `uIcc`, so the
  degenerate case `x = y` needs no separate treatment.

## Implementation notes

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

angle system, derivative, branch radius
-/

namespace ForgacsTran

open Real Set

/-- `∑_k ∂θ_k/∂τ`, the `τ`-partial of the angle sum. -/
noncomputable def ftAngleSumDerivTau {n : ℕ} (a : Fin n → ℝ) (τ s : ℝ) : ℝ :=
  ∑ k, -(Real.sin (ftAngle (a k) τ s) ^ 2 * a k / (τ ^ 2 * Real.sin s))

/-- `∑_k ∂θ_k/∂θ`, the `θ`-partial, named for symmetry with the above. -/
noncomputable def ftAngleSumDerivAngle {n : ℕ} (a : Fin n → ℝ) (τ s : ℝ) : ℝ :=
  ∑ k, Real.sin (ftAngle (a k) τ s) * Real.cos (ftAngle (a k) τ s - s) / Real.sin s

/-- `∂θ_k/∂τ = -sin²θ_k · τ_k/(τ² sin θ)`.  Unlike the `θ`-partial this one has a
sign visible on its face. -/
theorem hasDerivAt_ftAngle_tau {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    HasDerivAt (fun u => ftAngle a u s)
      (-(Real.sin (ftAngle a τ s) ^ 2 * a / (τ ^ 2 * Real.sin s))) τ := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hsin' : Real.sin s ≠ 0 := hsin.ne'
  have hτ' : τ ≠ 0 := hτ.ne'
  have hymem := ftAngle_mem_Ioo ha hτ hs
  have hsy : 0 < Real.sin (ftAngle a τ s) :=
    sin_pos_of_pos_of_lt_pi (lt_trans hs.1 hymem.1) hymem.2
  set y := ftAngle a τ s with hy
  set g : ℝ → ℝ := fun u => Real.cos s / Real.sin s - a / (u * Real.sin s) with hgdef
  have hgs : Real.cos y = g τ * Real.sin y := cos_ftArccot _
  have hgval : g τ = Real.cos y / Real.sin y := by
    rw [eq_div_iff hsy.ne']; exact hgs.symm
  have hone : 1 + g τ ^ 2 = 1 / Real.sin y ^ 2 := by
    rw [hgval]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq y)
  have hden : τ * Real.sin s ≠ 0 := mul_ne_zero hτ' hsin'
  have h2 : HasDerivAt (fun u : ℝ => a / (u * Real.sin s))
      ((0 * (τ * Real.sin s) - a * (1 * Real.sin s)) / (τ * Real.sin s) ^ 2) τ :=
    (hasDerivAt_const τ a).div ((hasDerivAt_id τ).mul_const (Real.sin s)) hden
  have hcomp := (hasDerivAt_ftArccot (g τ)).comp τ
    ((hasDerivAt_const τ (Real.cos s / Real.sin s)).sub h2)
  have hfun : (ftArccot ∘ g) = fun u => ftAngle a u s := rfl
  rw [hfun] at hcomp
  refine hcomp.congr_deriv ?_
  rw [hone]
  field

theorem hasDerivAt_ftAngleSum_tau {n : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {τ s : ℝ}
    (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    HasDerivAt (fun u => ftAngleSum a u s) (ftAngleSumDerivTau a τ s) τ :=
  HasDerivAt.fun_sum fun k _ => hasDerivAt_ftAngle_tau (ha k) hτ hs

theorem hasDerivAt_ftAngleSum_angle {n : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) {τ s : ℝ}
    (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) :
    HasDerivAt (fun t => ftAngleSum a τ t) (ftAngleSumDerivAngle a τ s) s :=
  hasDerivAt_ftAngleSum ha hτ hs

/-- **The non-degeneracy.**  The `τ`-partial is strictly negative, so the branch
equation can be solved for `τ`. -/
theorem ftAngleSumDerivTau_neg {n : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    {τ s : ℝ} (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) : ftAngleSumDerivTau a τ s < 0 := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  refine Finset.sum_neg (fun k _ => ?_)
    (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn))
  have hymem := ftAngle_mem_Ioo (ha k) hτ hs
  have hsy : 0 < Real.sin (ftAngle (a k) τ s) :=
    sin_pos_of_pos_of_lt_pi (lt_trans hs.1 hymem.1) hymem.2
  have : 0 < Real.sin (ftAngle (a k) τ s) ^ 2 * a k / (τ ^ 2 * Real.sin s) := by
    apply div_pos (mul_pos (by positivity) (ha k))
    positivity
  linarith

theorem continuousOn_ftAngle_prod (a : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ftAngle a p.1 p.2) (Ioi 0 ×ˢ Ioo 0 π) := by
  refine continuous_ftArccot.comp_continuousOn ?_
  refine ContinuousOn.sub ?_ ?_
  · exact (Real.continuous_cos.comp continuous_snd).continuousOn.div
      (Real.continuous_sin.comp continuous_snd).continuousOn
      fun p hp => ne_of_gt (sin_pos_of_pos_of_lt_pi (hp.2).1 (hp.2).2)
  · refine continuousOn_const.div
      (continuous_fst.continuousOn.mul (Real.continuous_sin.comp continuous_snd).continuousOn) ?_
    exact fun p hp => mul_ne_zero (ne_of_gt hp.1)
      (ne_of_gt (sin_pos_of_pos_of_lt_pi (hp.2).1 (hp.2).2))

theorem continuousOn_ftAngleSumDerivTau {n : ℕ} (a : Fin n → ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ftAngleSumDerivTau a p.1 p.2) (Ioi 0 ×ˢ Ioo 0 π) := by
  refine continuousOn_finsetSum _ fun k _ => ContinuousOn.neg ?_
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (((Real.continuous_sin.continuousOn.comp (continuousOn_ftAngle_prod (a k))
      (Set.mapsTo_image _ _ |>.mono_right le_rfl)).pow 2).mul continuousOn_const)
  · exact (continuous_fst.continuousOn.pow 2).mul
      (Real.continuous_sin.comp continuous_snd).continuousOn
  · exact fun p hp => mul_ne_zero (pow_ne_zero _ (ne_of_gt hp.1))
      (ne_of_gt (sin_pos_of_pos_of_lt_pi (hp.2).1 (hp.2).2))

/-- The mean value theorem on `uIcc`, which covers `x = y` without a case split:
the degenerate interval makes both sides zero. -/
theorem exists_hasDerivAt_eq_sub_uIcc (f f' : ℝ → ℝ) {x y : ℝ}
    (hd : ∀ u ∈ uIcc x y, HasDerivAt f (f' u) u) :
    ∃ ξ ∈ uIcc x y, f y - f x = f' ξ * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have hsub : Icc x y ⊆ uIcc x y := by rw [uIcc_of_le h.le]
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun u hu => (hd u (hsub hu)).continuousAt.continuousWithinAt)
      (fun u hu => hd u (hsub (Ioo_subset_Icc_self hu)))
    exact ⟨c, hsub (Ioo_subset_Icc_self hc), by
      rw [hc']; field_simp⟩
  · exact ⟨x, left_mem_uIcc, by rw [h]; ring⟩
  · have hsub : Icc y x ⊆ uIcc x y := by rw [uIcc_comm, uIcc_of_le h.le]
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun u hu => (hd u (hsub hu)).continuousAt.continuousWithinAt)
      (fun u hu => hd u (hsub (Ioo_subset_Icc_self hu)))
    refine ⟨c, hsub (Ioo_subset_Icc_self hc), ?_⟩
    rw [hc']
    field

end ForgacsTran
