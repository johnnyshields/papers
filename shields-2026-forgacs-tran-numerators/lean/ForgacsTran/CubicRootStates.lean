/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CubicCollisionWitness
import ForgacsTran.PhaseTangency
import ForgacsTran.TangentVariationBound
import ForgacsTran.BranchSupply
import ForgacsTran.BranchSupplyCubicWitness
import ForgacsTran.PencilIndex
import ForgacsTran.ComplexPart

/-!
# Root states at the cubic pencil

`BranchSupply.RootBranchState` is what `exists_uniform_ftBranchSupply`'s `hstates` asks
for, and `CubicPhaseSupplyComposition` leaves `hbranch` as the last hypothesis of an
otherwise unconditional `FTPhaseSupply` at `Q = (1-t)³`, `r = 1`, `B = 3t² + 1`.  This
module takes the state to that pencil.

**The general producer is extracted rather than rebuilt.**
`PhaseTangency.sum_eVariationOn_of_curvature` constructs a `RootBranchState` on its way to
the variation bound and discards it; `exists_rootBranchState_of_curvature` is that
construction, stated as its own theorem, so the two consumers meet without either being
rewritten.

**Every hypothesis is discharged at the cubic except one, and the exception is at a single
point.**  `hcurv` is free — `wedge γ'' γ'` is the polar curvature numerator
`τ² + 2τ'² - ττ''` (`cubic_wedge_eq`), which `CubicCollisionWitness.cubic_curvature_pos`
proves equal to `(8/9)τ² > 0` on the **closed** arc.  `hreg` holds everywhere, `hinj`
follows from `τ > 0` and the injectivity of `cos` on `[0, π]`.  What fails is the
producer's request for the two derivatives on an *open* set containing `[0, π]`:

**`cubicTau` has a corner at `θ = 0`.**  It is even (`CubicWitness.cubicTau_neg`), so a
two-sided derivative there is its own negative and hence zero; and it agrees with its
closed form on `[0, π]`, whose slope at `0` is `-√3/3 ≠ 0`.  Both cannot hold, and
`not_hasDerivAt_cubicTau_zero` proves it.  The geometry behind it: at `θ = 0` the branch
point is a **double** root of `2cos θ·τ³ - 3τ² + 1`, so the implicit function theorem does
not apply and the branch leaves it as `τ(θ) = 1 - |θ|/√3 + O(θ²)`.

**The obstruction is at the lower endpoint only.**  At `θ = π` the one-sided slopes are
both `0` and there is no corner — measured in
`../scripts/check_cubic_branch_corner.py`, which asserts it, because a reading of "the
endpoints are bad" would be wrong at half of them.

So `cubic_rootBranchState` runs on every closed sub-arc of `(0, π)` and not on `[0, π]`.
The tree already records the cause twice — `Amplitude.amplitude_endpoint_form`'s docstring
for the general branch, and `CubicWitnessInterior.hasDerivAt_cubicTauCF`'s note that the
closed form is kept separate because "the endpoints need it too, and there `cubicTau`
matches it only on one side".  What the producer would need is those endpoint hypotheses
one-sided.

## Main statements

* `cubicTauDeriv_zero`, `not_hasDerivAt_cubicTau_zero`,
  `not_hasDerivAt_ftPrincipal_cubicTau_zero` — the corner, and what it costs.
* `exists_rootBranchState_of_curvature` — the general producer.
* `cubic_wedge_eq`, `cubic_wedge_ne_zero` — `hcurv` at this branch, from `K = (8/9)τ²`.
* `injOn_ftPrincipal_cubicTau` — `hinj`.
* `cubic_rootBranchState` — the state, on any closed sub-arc of the open arc.
* `cubic_rootStates` — that in the shape `exists_uniform_ftBranchSupply` states `hstates`,
  with `Q` and `z` arbitrary, since neither is named by the state.
* `normSq_cubicGammaDeriv`, `cubic_im_tangentRate`, `cubic_abs_im_tangentRate_le`,
  `cubic_hKvar` — the tangent turns at `(8/9)τ²/(τ²+τ'²) ≤ 8/9`, so `hKvar` holds at
  `Kγ = 8π/9`.  The bound is a curvature ratio and does **not** use `τ` being bounded.
* `cubicArcAmp_eq_cubicAmp`, `cubicArcAmpDeriv_eq_cubicAmpDeriv`,
  `cubicArc_region_bounds`, `cubicArc_rootStates` — the same in the arc spelling, crossed
  by congruence at each point rather than left to unfolding.
* `cubic_branchSupply` — `exists_uniform_ftBranchSupply` applied at the cubic pencil, every
  hypothesis from a named producer.
* `ftTauArc_pi_ne_cubicArcTau_pi` — why the composition onto `FTPhaseSupply` does not close.
* `cubicAmpDeriv`, `cubic_abs_im_logDeriv_le`, `cubic_region_bounds` — `h₁`, `h₂`, `h₃` at
  the single constant `3/2`, since `CubicPhaseDerivative.abs_im_cubicAmpLogDeriv_le`
  already bounds `|Im(W'/W)|` uniformly over the arc: the three regions are one estimate
  restricted three ways, with no collar analysis at all.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`,
`cor:linear-phase-variation`, `eq:linear-phase-variation`, `thm:FT-geometry`.

## Tags

root state, curvature, branch corner, non-vacuity, Forgács–Tran
-/
namespace ForgacsTran

open Polynomial Set Real Complex
open scoped Topology

/-! ### The branch has a corner at the lower endpoint -/

/-- The closed form's slope at `0`: `-sin(π/3)/(6cos²(π/3)) = -√3/3`. -/
theorem cubicTauDeriv_zero : cubicTauDeriv 0 = -(Real.sqrt 3 / 3) := by
  rw [cubicTauDeriv, sub_zero, Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring

/-- **`cubicTau` is not differentiable at the lower endpoint.**  It is even
(`cubicTau_neg`), so any two-sided derivative there is its own negative and hence
zero; and it agrees with its closed form on `[0, π]`, whose slope at `0` is
`-√3/3 ≠ 0`.  The two cannot both hold.

**This is the geometry, not an artifact of the definition.**  Near `0` the branch
is `τ(θ) = 1 - |θ|/√3 + O(θ²)`: the pencil's root at `θ = 0` is a *double* root of
`2cos θ·τ³ - 3τ² + 1`, so the implicit function theorem does not apply and the
branch leaves it with a square-root singularity in the parameter.  `Amplitude`'s
`amplitude_endpoint_form` records the same fact for the general branch, and
`CubicWitnessInterior.hasDerivAt_cubicTauCF` is kept separate from
`hasDerivAt_cubicTau` for exactly this reason.

What it costs is stated in `not_rootBranchState_route_at_zero`. -/
theorem not_hasDerivAt_cubicTau_zero (d : ℝ) : ¬ HasDerivAt cubicTau d 0 := by
  intro hd
  have hpi := Real.pi_pos
  -- evenness forces any two-sided derivative to vanish
  have hneg : HasDerivAt cubicTau (-d) 0 := by
    have hcomp : HasDerivAt (fun θ : ℝ => cubicTau (0 - θ)) (-d) 0 :=
      HasDerivAt.comp_const_sub 0 0 (by simpa using hd)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp [cubicTau_neg]
  have hzero : d = 0 := by
    have := hd.unique hneg
    linarith
  -- the closed form's slope at `0` is not zero
  have hcne : Real.cos ((Real.pi - 0) / 3) ≠ 0 := by
    rw [sub_zero, Real.cos_pi_div_three]; norm_num
  have hcf := hasDerivAt_cubicTauCF hcne
  have hR : HasDerivWithinAt cubicTau (cubicTauDeriv 0) (Icc 0 Real.pi) 0 := by
    rw [cubicTauDeriv]
    exact hcf.hasDerivWithinAt.congr (fun y hy => cubicTau_closed_form hy)
      (cubicTau_closed_form ⟨le_rfl, hpi.le⟩)
  have hU : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) Real.pi) 0 :=
    uniqueDiffOn_Icc hpi 0 ⟨le_rfl, hpi.le⟩
  have heq : cubicTauDeriv 0 = d := by
    have h1 := hU.eq_deriv _ hR (hd.hasDerivWithinAt (s := Icc (0 : ℝ) Real.pi))
    exact h1
  rw [cubicTauDeriv_zero, hzero] at heq
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  linarith [heq]

/-! ### A `RootBranchState` producer, from curvature -/

/-- **The root state from the curvature hypothesis.**
`PhaseTangency.sum_eVariationOn_of_curvature` builds one of these on its way to the
variation bound and then discards it; `BranchSupply.exists_uniform_ftBranchSupply` asks
for one directly.  This is that construction extracted, so the two meet without either
being rewritten.

Nothing is new: the tangency set is `finite_tangency_zeros`', the dichotomy is
`PhaseStateDichotomy.miss_or_meet_once`, and the bridge from the polar-angle condition to
`tangency = 0` is `tangency_eq_zero_of_polarAngle_sub`.

`hfree` is over **closed** blocks, degenerate ones included, which is what excludes a
block collapsed onto the parameter the arc meets `β` at — the side clause can place that
block on neither side. -/
theorem exists_rootBranchState_of_curvature {γ dγ d2γ : ℝ → ℂ} {U : Set ℝ} {a b : ℝ} {β : ℂ}
    {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hcurv : ∀ s ∈ Icc a b, wedge (d2γ s) (dγ s) ≠ 0)
    (hinj : Set.InjOn γ (Icc a b))
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a b)
    (hfree : ∀ i, ∀ x ∈ Icc (Lb i) (Rb i), γ x ≠ β) :
    ∃ ψ : Fin k → ℝ → ℝ, RootBranchState γ dγ d2γ β a b Lb Rb ψ := by
  classical
  have hfin := finite_tangency_zeros (β := β) hU hsub hd hd2 hc2 hreg hcurv
  set S : Finset ℝ := hfin.toFinset with hSdef
  have hSmem : ∀ x, x ∈ Icc a b → tangency γ dγ β x = 0 → x ∈ S := by
    intro x hx hz
    rw [hSdef, Set.Finite.mem_toFinset]
    exact ⟨hx, hz⟩
  have hSsub : ∀ x ∈ S, x ∈ Icc a b := by
    intro x hx
    rw [hSdef, Set.Finite.mem_toFinset] at hx
    exact hx.1
  rcases miss_or_meet_once hinj β with hmiss | ⟨m, hm, hmβ, hother⟩
  · refine ⟨fun _ => polarAngle γ dγ β a,
      Or.inl ⟨S, hmiss, hSsub, fun x hx j hj => ?_, fun _ => rfl⟩⟩
    exact hSmem x (Ioo_subset_Icc_self hx)
      (tangency_eq_zero_of_polarAngle_sub hab hU hsub hd hd2 hc2 hreg hab (subset_refl _)
        hmiss ⟨le_rfl, hab⟩ (Ioo_subset_Icc_self hx) hj)
  · have hmne : ∀ x ∈ Icc a b, x ≠ m → γ x ≠ β := hother
    have hnotmem : ∀ i, m ∉ Icc (Lb i) (Rb i) := fun i hmem => hfree i m hmem hmβ
    refine ⟨fun i => if Rb i < m then polarAngle γ dγ β a else polarAngle γ dγ β b, Or.inr ?_⟩
    refine ⟨m, hm.1, hm.2, S, S, hmβ, hmne, fun x hx j hj => ?_, fun x hx j hj => ?_,
      fun i => ?_⟩
    · have hxab : x ∈ Icc a b := ⟨hx.1.le, hx.2.le.trans hm.2⟩
      refine hSmem x hxab (tangency_eq_zero_of_polarAngle_sub hab hU hsub hd hd2 hc2 hreg
        (a' := a) (b' := x) hx.1.le (Icc_subset_Icc le_rfl hxab.2)
        (fun s hs => hmne s ⟨hs.1, hs.2.trans hxab.2⟩ (ne_of_lt (lt_of_le_of_lt hs.2 hx.2)))
        ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hj)
    · have hxab : x ∈ Icc a b := ⟨hm.1.trans hx.1.le, hx.2.le⟩
      refine hSmem x hxab (tangency_eq_zero_of_polarAngle_sub hab hU hsub hd hd2 hc2 hreg
        (a' := x) (b' := b) hx.2.le (Icc_subset_Icc hxab.1 le_rfl)
        (fun s hs => hmne s ⟨hxab.1.trans hs.1, hs.2⟩ (ne_of_gt (lt_of_lt_of_le hx.1 hs.1)))
        ⟨hx.2.le, le_rfl⟩ ⟨le_rfl, hx.2.le⟩ hj)
    · by_cases hlt : Rb i < m
      · exact Or.inl ⟨fun x hx => ⟨(hJ i hx).1, lt_of_le_of_lt hx.2 hlt⟩, by simp [hlt]⟩
      · refine Or.inr ⟨fun x hx => ⟨?_, (hJ i hx).2⟩, by simp [hlt]⟩
        rcases le_or_gt (Lb i) (Rb i) with hLR | hLR
        · have hmlt : m < Lb i := by
            rcases lt_trichotomy m (Lb i) with h | h | h
            · exact h
            · exact absurd ⟨h.ge, le_trans h.le hLR⟩ (hnotmem i)
            · exact absurd ⟨h.le, not_lt.1 hlt⟩ (hnotmem i)
          exact lt_of_lt_of_le hmlt hx.1
        · exact absurd (le_trans hx.1 hx.2) (not_le.2 hLR)

/-! ### The state at the cubic pencil -/

/-- **`hcurv` at the cubic branch, in the tree's own variables.**  `wedge γ'' γ'` is the
polar curvature numerator `τ² + 2τ'² - ττ''`: the modulus-one factor `e^{iθ}` cancels
against its own conjugate and what is left is that expression.  So
`CubicCollisionWitness.cubic_curvature_pos` — which proves it equals `(8/9)τ² > 0` — is
`exists_rootBranchState_of_curvature`'s hypothesis at this branch. -/
theorem cubic_wedge_eq (θ : ℝ) :
    wedge (cubicGammaDeriv2 θ) (cubicGammaDeriv θ)
      = cubicTau θ ^ 2 + 2 * cubicTauDeriv θ ^ 2 - cubicTau θ * cubicTauDeriv2 θ := by
  simp only [wedge, cubicGammaDeriv, cubicGammaDeriv2, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  norm_num
  linear_combination (2 * cubicTauDeriv θ ^ 2
    - (cubicTauDeriv2 θ - cubicTau θ) * cubicTau θ) * Real.sin_sq_add_cos_sq θ

theorem cubic_wedge_ne_zero {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    wedge (cubicGammaDeriv2 θ) (cubicGammaDeriv θ) ≠ 0 := by
  rw [cubic_wedge_eq]
  exact (cubic_curvature_pos hθ).ne'

/-- **The branch is injective on the arc.**  Its modulus is `τ > 0` and its argument is
`θ`, so two parameters with the same image have the same cosine, and `cos` is injective
on `[0, π]`.  Nothing about the pencil enters beyond `τ > 0`. -/
theorem injOn_ftPrincipal_cubicTau {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π) :
    Set.InjOn (ftPrincipal cubicTau) (Icc a b) := by
  intro x hx y hy hxy
  have hxm : x ∈ Icc (0 : ℝ) π := ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
  have hym : y ∈ Icc (0 : ℝ) π := ⟨le_trans ha hy.1, le_trans hy.2 hb⟩
  have hnorm : ∀ t : ℝ, ‖ftPrincipal cubicTau t‖ = cubicTau t := by
    intro t
    rw [ftPrincipal, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (cubicTau_pos t)]
  have hτ : cubicTau x = cubicTau y := by rw [← hnorm x, ← hnorm y, hxy]
  have hre : ∀ t : ℝ, (ftPrincipal cubicTau t).re = cubicTau t * Real.cos t := by
    intro t
    rw [ftPrincipal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re]
    ring
  have hcos : Real.cos x = Real.cos y := by
    have h := congrArg Complex.re hxy
    rw [hre, hre, hτ] at h
    exact mul_left_cancel₀ (cubicTau_pos y).ne' h
  exact Real.injOn_cos hxm hym hcos

/-- **`RootBranchState` at the cubic pencil, on any closed sub-arc of `(0, π)`.**
Every hypothesis of `exists_rootBranchState_of_curvature` is discharged: the branch
modules give the two derivatives and the continuity on the open arc,
`CubicClockSpacing.cubicGammaDeriv_ne_zero` gives `hreg` everywhere, `cubic_wedge_ne_zero`
gives `hcurv` from `K = (8/9)τ² > 0`, and `injOn_ftPrincipal_cubicTau` gives `hinj`.

**It is a sub-arc and not `[0, π]`, and `not_hasDerivAt_cubicTau_zero` is why.**  The
producer asks for the two derivatives on an *open* set containing the closed arc, and the
branch has a corner at `0`, so no such set exists there.  Every hypothesis other than that
holds on the closed arc, `hcurv` included. -/
theorem cubic_rootBranchState {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < π)
    {β : ℂ} {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a b)
    (hfree : ∀ i, ∀ x ∈ Icc (Lb i) (Rb i), ftPrincipal cubicTau x ≠ β) :
    ∃ ψ : Fin k → ℝ → ℝ,
      RootBranchState (ftPrincipal cubicTau) cubicGammaDeriv cubicGammaDeriv2 β a b
        Lb Rb ψ := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) π := fun s hs =>
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have harc : ∀ s ∈ Icc a b, s ∈ Icc (0 : ℝ) π := fun s hs =>
    ⟨(hsub hs).1.le, (hsub hs).2.le⟩
  exact exists_rootBranchState_of_curvature hab isOpen_Ioo hsub
    (fun s hs => hasDerivAt_ftPrincipal_cubicTau hs)
    (fun s hs => hasDerivAt_cubicGammaDeriv hs)
    (fun s hs => (continuousAt_cubicGammaDeriv2 hs).continuousWithinAt)
    (fun s _ => cubicGammaDeriv_ne_zero s)
    (fun s hs => cubic_wedge_ne_zero (harc s hs))
    (injOn_ftPrincipal_cubicTau ha.le hb.le) hJ hfree

/-- **What the corner costs, at the object the producer names.**
`exists_rootBranchState_of_curvature` asks for `HasDerivAt γ (dγ s) s` at every `s` of an
*open* set containing the closed arc.  At `s = 0` that is a two-sided derivative of the
branch point, and there is none: dividing off the unit factor recovers `cubicTau`, which
has a corner there.  So no open `U ⊇ [0, π]` exists and the route reaches a closed
sub-arc only — not because of the tangency set, the curvature, or the numerator, all of
which are fine on the closed arc. -/
theorem not_hasDerivAt_ftPrincipal_cubicTau_zero (d : ℂ) :
    ¬ HasDerivAt (ftPrincipal cubicTau) d 0 := by
  intro hd
  have hE : HasDerivAt (fun θ : ℝ => Complex.exp (-((θ : ℝ) : ℂ) * I)) (-I) 0 := by
    have h : HasDerivAt (fun w : ℂ => Complex.exp (-w * I))
        (Complex.exp (-((0 : ℝ) : ℂ) * I) * -I) (((0 : ℝ) : ℂ)) := by
      simpa using (((hasDerivAt_id (((0 : ℝ) : ℂ))).neg).mul_const I).cexp
    simpa using h.comp_ofReal
  have hprod : HasDerivAt
      (fun θ : ℝ => ftPrincipal cubicTau θ * Complex.exp (-((θ : ℝ) : ℂ) * I))
      (d * Complex.exp (-((0 : ℝ) : ℂ) * I) + ftPrincipal cubicTau 0 * -I) 0 := hd.mul hE
  have heq : (fun θ : ℝ => ftPrincipal cubicTau θ * Complex.exp (-((θ : ℝ) : ℂ) * I))
      = fun θ : ℝ => ((cubicTau θ : ℝ) : ℂ) := by
    funext θ
    rw [ftPrincipal, mul_assoc, ← Complex.exp_add]
    simp
  rw [heq] at hprod
  have hre := hprod.re
  simp only [Complex.ofReal_re] at hre
  exact not_hasDerivAt_cubicTau_zero _ hre

/-! ### `hstates` in the producer's own shape -/

/-- **`hstates` at the cubic pencil**, in the shape
`BranchSupply.exists_uniform_ftBranchSupply` now states it: an arbitrary closed
sub-interval of the **open** arc, blocks inside it, and the amplitude nonvanishing on each
closed block.

`PhaseBranchSplit.ne_root_of_ftAmp_ne_zero` is what joins the two nonvanishing clauses:
the supply's blocks carry `W ≠ 0` while `RootBranchState` asks the branch to avoid `β`,
and `W` has `B(γ)` in its numerator.

**`Q` and `z` are arbitrary.**  `RootBranchState` names neither, and they enter only
through the nonvanishing clause, which is used only to keep the branch off `β`.  So this
is a statement about the cubic *branch*, not about the cubic pencil, and it holds at
whatever weight and spectral parameter the supply is instantiated with.

**Nothing is asked at `0` or `π`.**  That is the whole difference from the earlier shape:
`not_hasDerivAt_cubicTau_zero` made the closed-arc version unreachable, and the open-arc
version never meets the corner. -/
theorem cubic_rootStates {Q B : Polynomial ℂ} {z : ℝ → ℝ} {a' b' : ℝ} (hab : a' ≤ b')
    (hsub : Icc a' b' ⊆ Ioo (0 : ℝ) π)
    {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hL : ∀ i, Lb i ∈ Icc a' b') (hR : ∀ i, Rb i ∈ Icc a' b')
    (hne : ∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
      ftAmp Q B 1 ((z θ : ℝ) : ℂ) (ftPrincipal cubicTau θ) ≠ 0) :
    ∀ β ∈ B.roots, ∃ ψ : Fin k → ℝ → ℝ,
      RootBranchState (ftPrincipal cubicTau) cubicGammaDeriv cubicGammaDeriv2 β a' b'
        Lb Rb ψ := by
  intro β hβ
  have ha : 0 < a' := (hsub ⟨le_rfl, hab⟩).1
  have hb : b' < π := (hsub ⟨hab, le_rfl⟩).2
  refine cubic_rootBranchState hab ha hb
    (fun i x hx => ⟨le_trans (hL i).1 hx.1, le_trans hx.2 (hR i).2⟩) ?_
  exact fun i x hx => ne_root_of_ftAmp_ne_zero (hne i x hx) hβ

/-! ### The tangent's turning rate, and `hKvar` -/

/-- `‖γ'‖² = τ² + τ'²`: the unit factor drops out. -/
theorem normSq_cubicGammaDeriv (θ : ℝ) :
    Complex.normSq (cubicGammaDeriv θ) = cubicTau θ ^ 2 + cubicTauDeriv θ ^ 2 := by
  have h1 : Complex.normSq (Complex.exp ((θ : ℂ) * I)) = 1 := by
    simp only [Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [cubicGammaDeriv, map_mul, h1, one_mul]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The tangent turns at `(8/9)τ²/(τ² + τ'²)`.**  An identity: `Im(γ''/γ')` is
`wedge γ'' γ'` over `‖γ'‖²`, the numerator is the curvature `K` (`cubic_wedge_eq`), and
`K = (8/9)τ²` at this branch (`CubicCollisionWitness.cubic_curvature_eq`). -/
theorem cubic_im_tangentRate {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    (cubicGammaDeriv2 θ / cubicGammaDeriv θ).im
      = 8 / 9 * cubicTau θ ^ 2 / (cubicTau θ ^ 2 + cubicTauDeriv θ ^ 2) := by
  rw [im_div_eq_wedge_div_normSq, cubic_wedge_eq, cubic_curvature_eq hθ,
    normSq_cubicGammaDeriv]

/-- **`κ = 8/9` bounds the tangent's turning rate on the whole arc.**

**The bound does not come from `τ` being bounded**, and the distinction matters because a
`κ` that did would be a fact about this pencil's radius rather than about its curvature.
`Im(γ''/γ') = (8/9)τ²/(τ² + τ'²)`, and dropping `τ'² ≥ 0` from the denominator gives
`≤ 8/9` — only `τ ≠ 0` is used.  `τ` runs from `1` to `1/2` here and never enters the
estimate; the value `8/9` is `K/τ²`, a pure curvature ratio.

It is attained in the limit at `θ = π`, where `τ' → 0`. -/
theorem cubic_abs_im_tangentRate_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    |(cubicGammaDeriv2 θ / cubicGammaDeriv θ).im| ≤ 8 / 9 := by
  have hτ : 0 < cubicTau θ := cubicTau_pos θ
  have hden : 0 < cubicTau θ ^ 2 + cubicTauDeriv θ ^ 2 := by positivity
  rw [cubic_im_tangentRate hθ, abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (cubicTauDeriv θ), sq_nonneg (cubicTau θ)]

/-- **`hKvar` at the cubic branch, end to end.**  `eVariationOn_polarAngle_tangent_le_of_le`
at `κ = 8/9` over `(0, π)`, so the tangent's total turning is at most `8π/9`.

Every hypothesis is the branch modules' own: the second derivative and its continuity on
the open arc, and `cubicGammaDeriv_ne_zero` everywhere. -/
theorem cubic_hKvar :
    ∀ c ∈ Ioo (0 : ℝ) π,
      eVariationOn (polarAngle cubicGammaDeriv cubicGammaDeriv2 0 c) (Ioo (0 : ℝ) π)
        ≤ ENNReal.ofReal (8 / 9 * π) := by
  refine eVariationOn_polarAngle_tangent_le_of_le
    (fun s hs => hasDerivAt_cubicGammaDeriv hs)
    (fun s hs => (continuousAt_cubicGammaDeriv2 hs).continuousWithinAt)
    (fun s _ => cubicGammaDeriv_ne_zero s) (by norm_num)
    (fun s hs => cubic_abs_im_tangentRate_le ⟨hs.1.le, hs.2.le⟩) ?_
  rw [sub_zero]

/-! ### The three region bounds -/

/-- The amplitude's derivative along the arc, `W' = (W'/W)·W`, in the shape
`exists_ftBranchSupply_of_rootStates` names `dW`. -/
noncomputable def cubicAmpDeriv (θ : ℝ) : ℂ := cubicAmpLogDeriv θ * cubicAmp θ

theorem hasDerivAt_cubicAmp' {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) (hhalf : θ ≠ π / 2) :
    HasDerivAt cubicAmp (cubicAmpDeriv θ) θ := hasDerivAt_cubicAmp hθ hhalf

/-- **The amplitude vanishes only at `π/2` on the open arc.**  Its closed form is
`γ(3γ²+1)/((1-γ)²(2γ+1))`, whose numerator is `γ·B(γ)` up to the constant, and `γ ≠ 0`. -/
theorem cubicAmp_ne_zero_of_ne_pi_div_two {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π)
    (hhalf : θ ≠ π / 2) : cubicAmp θ ≠ 0 := by
  rw [cubicAmp, ftAmp_cubic_eq hθ]
  refine div_ne_zero (mul_ne_zero (ftPrincipal_cubicTau_ne_zero θ) ?_) ?_
  · exact three_mul_sq_ftPrincipal_add_one_ne_zero hθ hhalf
  · exact mul_ne_zero (pow_ne_zero 2 (one_sub_ftPrincipal_cubicTau_ne_zero hθ))
      (two_mul_ftPrincipal_cubicTau_add_one_ne_zero hθ)

theorem cubicAmp_pi_div_two_eq_zero : cubicAmp (π / 2) = 0 := by
  have hpi := Real.pi_pos
  have hmem : π / 2 ∈ Ioo (0 : ℝ) π := ⟨by linarith, by linarith⟩
  have hB : witB.eval (ftPrincipal cubicTau (π / 2)) = 0 :=
    (witB_eval_ftPrincipal_eq_zero_iff ⟨by linarith, by linarith⟩).2 rfl
  rw [cubicAmp, ftAmp, hB, zero_div, neg_zero]

/-- **`eq:phase-derivative-bound` on the whole closed arc at the cubic pencil**, at the
single constant `κ = 3/2`.

**All three regions share one constant, and there is no collar analysis here at all.**
`CubicPhaseDerivative.abs_im_cubicAmpLogDeriv_le` already bounds `|Im(W'/W)|` uniformly
over `(0,π) ∖ {π/2}` — the phase derivative is a rational function of `τ` with no `θ` in
it — so the interior and the two collars are the same estimate restricted.  `3/2` is not
sharp: `ψ'` runs over `[47/63, 7/6]`.

**The endpoints are carried by the guard, not by an estimate.**  `s = 0` and `s = π` are
in the interval and outside `abs_im_cubicAmpLogDeriv_le`'s domain; what excludes them is
`hW0` and `hWπ`, which say the amplitude vanishes there, so the hypothesis
`cubicAmp s ≠ 0` is unsatisfiable at those two points.  Those are separate clauses of
`exists_ftBranchSupply_of_rootStates` and are taken as hypotheses here rather than
reproved. -/
theorem cubic_abs_im_logDeriv_le (hW0 : cubicAmp 0 = 0) (hWπ : cubicAmp π = 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) π) (hne : cubicAmp s ≠ 0) :
    |(cubicAmpDeriv s / cubicAmp s).im| ≤ 3 / 2 := by
  have hs0 : s ≠ 0 := by rintro rfl; exact hne hW0
  have hsπ : s ≠ π := by rintro rfl; exact hne hWπ
  have hmem : s ∈ Ioo (0 : ℝ) π :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hsπ⟩
  have hhalf : s ≠ π / 2 := by rintro rfl; exact hne cubicAmp_pi_div_two_eq_zero
  rw [cubicAmpDeriv, mul_div_assoc, div_self hne, mul_one]
  exact abs_im_cubicAmpLogDeriv_le hmem hhalf

/-- **The three regions, at any cut points.**  `h₁`, `h₂` and `h₃` of
`exists_ftBranchSupply_of_rootStates` at `c₁ = c₂ = c₃ = 3/2`, for whatever `b₁ ≤ b₂` the
caller picks inside the arc.  They are one statement restricted three ways, which is what
a `θ`-free phase derivative buys. -/
theorem cubic_region_bounds (hW0 : cubicAmp 0 = 0) (hWπ : cubicAmp π = 0)
    {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₁₂ : b₁ ≤ b₂) (hb₂ : b₂ ≤ π) :
    (∀ s ∈ Icc (0 : ℝ) b₁, cubicAmp s ≠ 0 →
        |(cubicAmpDeriv s / cubicAmp s).im| ≤ 3 / 2)
      ∧ (∀ s ∈ Icc b₁ b₂, cubicAmp s ≠ 0 →
        |(cubicAmpDeriv s / cubicAmp s).im| ≤ 3 / 2)
      ∧ (∀ s ∈ Icc b₂ π, cubicAmp s ≠ 0 →
        |(cubicAmpDeriv s / cubicAmp s).im| ≤ 3 / 2) := by
  have hmain : ∀ s ∈ Icc (0 : ℝ) π, cubicAmp s ≠ 0 →
      |(cubicAmpDeriv s / cubicAmp s).im| ≤ 3 / 2 :=
    fun s hs hne => cubic_abs_im_logDeriv_le hW0 hWπ hs hne
  refine ⟨fun s hs => hmain s ⟨hs.1, by linarith [hs.2]⟩,
    fun s hs => hmain s ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    fun s hs => hmain s ⟨by linarith [hs.1], hs.2⟩⟩

/-! ### Crossing to the arc spelling

`BranchSupplyCubicWitness` states its groups at `cubicArcTau`/`cubicArcZ`, the extension
that carries the upper endpoint's value; everything above is at `cubicTau`/`cubicZ`.  The
two agree on `Icc 0 π` and **only there**, so the crossing is made by congruence at each
point rather than left to definitional unfolding — the same-object-different-term seam. -/

theorem cubicArcAmp_eq_cubicAmp {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    cubicArcAmp witB θ = cubicAmp θ := by
  rw [cubicArcAmp, cubicAmp, cubicArcZ, cubicArcTau_eq hθ, ftPrincipal_cubicArcTau_eq hθ]

theorem cubicAmp_zero : cubicAmp 0 = 0 := by
  rw [← cubicArcAmp_eq_cubicAmp ⟨le_rfl, Real.pi_pos.le⟩]
  exact cubicArcAmp_zero witB

theorem cubicAmp_pi : cubicAmp π = 0 := by
  rw [← cubicArcAmp_eq_cubicAmp ⟨Real.pi_pos.le, le_rfl⟩]
  exact cubicArcAmp_pi witB

/-- **The two derivative spellings agree off the divisor.**  Not by unfolding: they are
different expressions — a quotient rule against `∂_tD`, and `(W'/W)·W` — and what makes
them equal is that both are derivatives of the same function at `θ`, so uniqueness
settles it.  At `π/2` only `cubicArcAmpDeriv` is available, which is why `hWd` holds on
the whole open arc and this does not. -/
theorem cubicArcAmpDeriv_eq_cubicAmpDeriv {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π)
    (hhalf : θ ≠ π / 2) : cubicArcAmpDeriv witB θ = cubicAmpDeriv θ := by
  have hEq : cubicArcAmp witB =ᶠ[nhds θ] cubicAmp := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
    exact cubicArcAmp_eq_cubicAmp ⟨hs.1.le, hs.2.le⟩
  exact (hasDerivAt_cubicArcAmp witB hθ).unique
    ((hasDerivAt_cubicAmp' hθ hhalf).congr_of_eventuallyEq hEq)

/-- **`h₁`, `h₂`, `h₃` in the arc spelling**, which is what
`exists_uniform_ftBranchSupply` reads. -/
theorem cubicArc_region_bounds {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₁₂ : b₁ ≤ b₂) (hb₂ : b₂ ≤ π) :
    (∀ s ∈ Icc (0 : ℝ) b₁, cubicArcAmp witB s ≠ 0 →
        |(cubicArcAmpDeriv witB s / cubicArcAmp witB s).im| ≤ 3 / 2)
      ∧ (∀ s ∈ Icc b₁ b₂, cubicArcAmp witB s ≠ 0 →
        |(cubicArcAmpDeriv witB s / cubicArcAmp witB s).im| ≤ 3 / 2)
      ∧ (∀ s ∈ Icc b₂ π, cubicArcAmp witB s ≠ 0 →
        |(cubicArcAmpDeriv witB s / cubicArcAmp witB s).im| ≤ 3 / 2) := by
  have hmain : ∀ s ∈ Icc (0 : ℝ) π, cubicArcAmp witB s ≠ 0 →
      |(cubicArcAmpDeriv witB s / cubicArcAmp witB s).im| ≤ 3 / 2 := by
    intro s hs hne
    rw [cubicArcAmp_eq_cubicAmp hs] at hne ⊢
    have hs0 : s ≠ 0 := by rintro rfl; exact hne cubicAmp_zero
    have hsπ : s ≠ π := by rintro rfl; exact hne cubicAmp_pi
    have hmem : s ∈ Ioo (0 : ℝ) π :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hsπ⟩
    have hhalf : s ≠ π / 2 := by rintro rfl; exact hne cubicAmp_pi_div_two_eq_zero
    rw [cubicArcAmpDeriv_eq_cubicAmpDeriv hmem hhalf]
    exact cubic_abs_im_logDeriv_le cubicAmp_zero cubicAmp_pi hs hne
  refine ⟨fun s hs => hmain s ⟨hs.1, by linarith [hs.2]⟩,
    fun s hs => hmain s ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    fun s hs => hmain s ⟨by linarith [hs.1], hs.2⟩⟩

/-- **`hstates` in the arc spelling.**  `RootBranchState` names the branch as a *function*,
so the crossing cannot be left to `Icc 0 π`: the state is rebuilt at `ftPrincipal
cubicArcTau` from `exists_rootBranchState_of_curvature`, with each hypothesis transferred
pointwise. -/
theorem cubicArc_rootStates {Q B : Polynomial ℂ} {z : ℝ → ℝ} {a' b' : ℝ} (hab : a' ≤ b')
    (hsub : Icc a' b' ⊆ Ioo (0 : ℝ) π)
    {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hL : ∀ i, Lb i ∈ Icc a' b') (hR : ∀ i, Rb i ∈ Icc a' b')
    (hne : ∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
      ftAmp Q B 1 ((z θ : ℝ) : ℂ) (ftPrincipal cubicArcTau θ) ≠ 0) :
    ∀ β ∈ B.roots, ∃ ψ : Fin k → ℝ → ℝ,
      RootBranchState (ftPrincipal cubicArcTau) cubicGammaDeriv cubicGammaDeriv2 β a' b'
        Lb Rb ψ := by
  intro β hβ
  have harc : ∀ s ∈ Icc a' b', s ∈ Icc (0 : ℝ) π := fun s hs =>
    ⟨(hsub hs).1.le, (hsub hs).2.le⟩
  refine exists_rootBranchState_of_curvature hab isOpen_Ioo hsub
    (fun s hs => hasDerivAt_ftPrincipal_cubicArcTau hs)
    (fun s hs => hasDerivAt_cubicGammaDeriv hs)
    (fun s hs => (continuousAt_cubicGammaDeriv2 hs).continuousWithinAt)
    (fun s _ => cubicGammaDeriv_ne_zero s)
    (fun s hs => cubic_wedge_ne_zero (harc s hs)) ?_
    (fun i x hx => ⟨le_trans (hL i).1 hx.1, le_trans hx.2 (hR i).2⟩)
    (fun i x hx => ne_root_of_ftAmp_ne_zero (hne i x hx) hβ)
  -- injectivity, transferred pointwise from the `cubicTau` spelling
  intro x hx y hy hxy
  refine injOn_ftPrincipal_cubicTau (a := a') (b := b') (hsub ⟨le_rfl, hab⟩).1.le
    (hsub ⟨hab, le_rfl⟩).2.le hx hy ?_
  rw [← ftPrincipal_cubicArcTau_eq (harc x hx), ← ftPrincipal_cubicArcTau_eq (harc y hy)]
  exact hxy

/-! ### The application -/

/-- **`exists_uniform_ftBranchSupply` at the cubic pencil.**  Every hypothesis discharged
from a named producer: the geometry and amplitude groups and `κ₀` from
`BranchSupplyCubicWitness`, `hKvar` and the three region bounds and `hstates` from this
module.  Nothing is assumed and nothing is stubbed.

`b₁ = π/3`, `b₂ = 2π/3` and `c₁ = c₂ = c₃ = 3/2`: the cut points are arbitrary because the
phase bound is uniform, and choosing them at all is a formality of the interface. -/
theorem cubic_branchSupply :
    ∃ κ₀' κ₁' : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧ ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M →
      ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) π) → (∀ i, Rb i ∈ Icc (0 : ℝ) π) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), cubicArcAmp witB θ ≠ 0) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          cubicArcAmp witB θ
            = ((ftPrincipalAmp cubicQ witB 1 cubicArcZ cubicArcTau θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀' + κ₁' * witB.natDegree := by
  have hpi := Real.pi_pos
  have h1 : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  obtain ⟨κ₀, hκ₀, h0⟩ := cubicArc_exists_kappaZero
  obtain ⟨hγd, hd2, hc2, hreg⟩ := cubic_geometry_group
  obtain ⟨hWd, hWc, hW0, hWL⟩ := cubic_amplitude_group witB
  obtain ⟨hr₁, hr₂, hr₃⟩ := cubicArc_region_bounds (b₁ := π / 3) (b₂ := 2 * π / 3)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hsupply⟩ :=
    exists_uniform_ftBranchSupply (Q := cubicQ) (r := 1) (z := cubicArcZ) (τ := cubicArcTau)
      (dS := cubicCofactorDeriv) (dγ := cubicGammaDeriv) (d2γ := cubicGammaDeriv2)
      (c₀ := π / 2) (κ₀ := κ₀) (Kγ := 8 / 9 * π)
      (by rw [h1]; exact hpi)
      (by rw [h1]; exact hγd) (by rw [h1]; exact hd2) (by rw [h1]; exact hc2)
      (by rw [h1]; exact hreg) (by positivity)
      (by rw [h1]; exact cubic_hKvar)
      (by rw [h1]; exact fun s hs => hasDerivAt_cubicArcCofactorAlong hs)
      (by rw [h1]; exact continuousOn_cubicCofactorDeriv)
      (by rw [h1]; exact fun s hs => ftCofactorAlong_cubicArc_ne_zero hs)
      (by rw [h1]; exact ⟨by linarith, by linarith⟩) hκ₀ (by rw [h1]; exact h0)
  refine ⟨κ₀', κ₁', hκ₀', hκ₁', ?_⟩
  have hres := hsupply witB witB_ne_zero (Ioo (0 : ℝ) π) (cubicArcAmpDeriv witB)
    (π / 3) (2 * π / 3) (3 / 2) (3 / 2) (3 / 2) isOpen_Ioo (by rw [h1])
    (fun s hs => hasDerivAt_cubicArcAmp witB hs) hWc
    (fun s hs => hr₁ s ⟨hs.1.le, hs.2⟩) hr₂
    (by rw [h1]; exact fun s hs => hr₃ s ⟨hs.1, hs.2.le⟩)
    (by rw [h1]; exact fun a' b' hab hsub k Lb Rb hL hR _ hne =>
      cubicArc_rootStates hab hsub hL hR hne)
  rw [h1] at hres
  -- at this pencil the endpoint values are genuine, so the interiority binder is met by
  -- the cheap route rather than by a fact about the blocks
  obtain ⟨Mb, hMb⟩ := hres
  refine ⟨Mb, fun M hM k Lb Rb hL hR hord hne => ?_⟩
  exact hMb M hM k Lb Rb hL hR hord
    (interior_of_endpoint_vanishing hL hR hW0 hWL hne) hne

/-! ### Why the composition with `CubicPhaseSupplyComposition` does not close -/

/-- **`cubic_ftPhaseSupply_of_branchSupply` names the superseded extension.**  It asks for
`hbranch` at `ftTauArc ![1,1,1] 1 2 1`, whose value past `π/r` is `0` — the convention that
is correct only when the branch runs into the origin.  `BranchSupplyCubicWitness` builds
its groups at `cubicArcTau = ftTauArcAt ![1,1,1] 1 2 1 (1/2)`, which carries the finite
value an `r = 1` arc actually ends at.

The two agree everywhere below `π` and disagree **at `π`**, by `1/2`.  So the mismatch is
not a spelling to be bridged: `ftPrincipal` of the first is `0` there and of the second is
`-1/2`, and `hbranch`'s blocks range over `Icc 0 π`, which contains that point.

Stated rather than described, because it is the one thing between `cubic_branchSupply` and
an unconditional `FTPhaseSupply` at this pencil. -/
theorem ftTauArc_pi_ne_cubicArcTau_pi :
    ftTauArc ![1, 1, 1] 1 2 1 π ≠ cubicArcTau π := by
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  have h1 : ftTauArc ![1, 1, 1] 1 2 1 π = 0 := by
    rw [ftTauArc, if_neg (by rw [hcast]; exact lt_irrefl π)]
  have h2 : cubicArcTau π = 1 / 2 := by
    rw [cubicArcTau, ftTauArcAt, if_neg (by rw [hcast]; exact lt_irrefl π)]
  rw [h1, h2]
  norm_num

end ForgacsTran
