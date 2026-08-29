/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CubicCollisionWitness
import ForgacsTran.CubicClockSpacing
import ForgacsTran.CubicWitnessComposition
import ForgacsTran.CubicInteriorRemainder
import ForgacsTran.TauArcAt
import ForgacsTran.PencilIndex
import ForgacsTran.ComplexPart

/-!
# `BranchSupply`'s collar, at a double collision

`BranchSupply.exists_bound_im_logDeriv_ftCofactorAlong_lower` is proved at arbitrary
multiplicity, deliberately: the order is `rootMultiplicity` and the reduced factor is
nonzero by construction, so no simplicity of the collision is assumed.  Every witness in
the tree before this one has `ν = 1`, which is exactly the case a simplicity lemma would
have covered, so the generality was proved and untested.

The cubic pencil tests it.  `Q = (1-t)³` at `r = 1` has `E = XQ' - rQ = -(1-t)²(2t+1)`,
a **double** zero at `t = 1`, and the branch reaches `1` as `θ → 0`
(`CubicCollisionWitness.ftCollisionOrder_cubic_zero`).  So the collar is instantiated here
at `m = 2`, and `E` does not vanish on the open arc, which is the arc state.

One further degeneracy of the earlier witness goes with it: `τ` is not constant here
(`cubicTau_not_constant`), so the branch is not a circle and the cofactor's argument is
not pinned to a ray — whether it actually moves, and so whether `κ₀` is positive, is not
settled below.

**The binders are one-sided.**  `θ` is an angular distance from the collision, so the
branch is asked for a `HasDerivWithinAt` on `Ici 0` there and a two-sided derivative off
it; `cubicTau` matches its closed form only on `[0, π]`, which is what makes that the
right form rather than a technicality.

Sorry-free.

## Main statements

* `ftCritical_cubicQ_endpoint_factor` — `hEfac` at `m = 2`.
* `hasDerivWithinAt_ftPrincipal_cubicTau_zero`, `hasDerivWithinAt_cubicGammaDeriv_zero` —
  the branch and its derivative, one-sidedly at the collision.
* `exists_cubicLip` — the Lipschitz collar on `γ'`, by compactness against `γ''`.
* `cubicCofactorDeriv`, `hasDerivAt_cubicCofactorAlong` — `∂_t D` along the arc.
* `cubicPencil_collar_witness` — every binder discharged.
* `cubicArcTau`, `cubicArcPencil_collar_witness` — the same at `ftTauArcAt`, the
  parametrization the branch supply actually consumes.
* `ftCritical_cubicQ_upper_factor`, `cubicUpperGammaDeriv`,
  `cubicArcPencil_upper_collar_witness` — the collar at the far collision, through the
  reflected branch.
* `cubicArc_exists_kappaZero` — `κ₀` at this pencil: a collar at each collision and
  compactness in between.
* `cubic_geometry_group`, `cubic_amplitude_group` — the branch and amplitude hypotheses of
  `exists_uniform_ftBranchSupply` at this pencil, the second at an arbitrary weight.
* `cubicTauDeriv2_zero`, `cubic_collar_reduced_requirements` — `τ''` at the collision is
  `7/9` here, and the general collar's two remaining needs both hold.
* `not_differentiableAt_ftTauArcAt_cubic_zero`,
  `not_exists_hasDerivAt_ftPrincipal_ftTauArcAt_cubic_zero` — and the closed-arc binder of
  `exists_uniform_ftBranchSupply` that is not, at the lower endpoint, for any `r`.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
and the principal amplitude» (`sec:geometry`, `eq:Dprime-identity`,
`eq:phase-derivative-bound`) at the worked cubic pencil.

## Tags

collar, collision, multiplicity, witness
-/

namespace ForgacsTran

open Polynomial Set Real Complex

/-- The spectral parameter along the cubic branch. -/
noncomputable def cubicZarc : ℝ → ℝ := fun θ => cubicZ (cubicTau θ) θ

/-- **`hEfac` at the cubic's lower collision, with `m = 2`.** -/
theorem ftCritical_cubicQ_endpoint_factor :
    ftCritical cubicQ 1
      = (X - C (ftPrincipal cubicTau 0)) ^ 2 * (-(2 * X + 1)) := by
  rw [ftPrincipal_cubicTau_zero', ftCritical_cubicQ]
  simp only [map_one]
  ring

theorem eval_cubic_endpoint_H_ne_zero :
    (-(2 * X + 1) : Polynomial ℂ).eval (ftPrincipal cubicTau 0) ≠ 0 := by
  rw [ftPrincipal_cubicTau_zero']
  simp only [eval_neg, eval_add, eval_mul, eval_one, eval_X, eval_ofNat]
  norm_num

theorem continuousOn_cubicTau : ContinuousOn cubicTau (Icc 0 π) := by
  refine ContinuousOn.congr (f := fun t : ℝ => 1 / (2 * Real.cos ((π - t) / 3))) ?_ ?_
  · refine ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => ?_)
    have := cos_third_pos ht
    positivity
  · intro t ht
    exact cubicTau_closed_form ht

theorem continuousOn_cubicTauDeriv : ContinuousOn cubicTauDeriv (Icc 0 π) := by
  refine ContinuousOn.congr (f := fun t : ℝ =>
    -Real.sin ((π - t) / 3) / (6 * Real.cos ((π - t) / 3) ^ 2)) ?_ (fun t _ => rfl)
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => ?_)
  have := cos_third_pos ht
  positivity

theorem continuousOn_cubicTauDeriv2 : ContinuousOn cubicTauDeriv2 (Icc 0 π) := by
  refine ContinuousOn.congr (f := fun t : ℝ =>
    (Real.cos ((π - t) / 3) ^ 2 + 2 * Real.sin ((π - t) / 3) ^ 2)
      / (18 * Real.cos ((π - t) / 3) ^ 3)) ?_ (fun t _ => rfl)
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => ?_)
  have := cos_third_pos ht
  positivity

theorem continuousOn_cubicGammaDeriv2 : ContinuousOn cubicGammaDeriv2 (Icc 0 π) := by
  refine ContinuousOn.congr (f := fun t : ℝ =>
    Complex.exp ((t : ℂ) * Complex.I)
      * (((cubicTauDeriv2 t : ℝ) : ℂ)
          + 2 * ((cubicTauDeriv t : ℝ) : ℂ) * Complex.I - ((cubicTau t : ℝ) : ℂ)))
    ?_ (fun t _ => rfl)
  refine ContinuousOn.mul (by fun_prop) ?_
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · exact Complex.continuous_ofReal.comp_continuousOn continuousOn_cubicTauDeriv2
  · exact ContinuousOn.mul (ContinuousOn.mul continuousOn_const
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_cubicTauDeriv))
      continuousOn_const
  · exact Complex.continuous_ofReal.comp_continuousOn continuousOn_cubicTau

theorem hasDerivWithinAt_cubicTau_zero' :
    HasDerivWithinAt cubicTau (cubicTauDeriv 0) (Ici 0) 0 := by
  have hpi := Real.pi_pos
  have hcos : Real.cos ((Real.pi - 0) / 3) ≠ 0 := by rw [sub_zero]; simp
  exact (hasDerivAt_cubicTauCF hcos).hasDerivWithinAt.congr_of_eventuallyEq
    cubicTau_eventuallyEq_cf (cubicTau_closed_form ⟨le_rfl, hpi.le⟩)

private theorem hasDerivWithinAt_expI (θ : ℝ) {s : Set ℝ} :
    HasDerivWithinAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I)) s θ :=
  ((((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).cexp).hasDerivWithinAt

/-- **`hd0` at the cubic's lower collision.**  The branch is one-sidedly
differentiable there, with the closed form's derivative. -/
theorem hasDerivWithinAt_ftPrincipal_cubicTau_zero :
    HasDerivWithinAt (ftPrincipal cubicTau) (cubicGammaDeriv 0) (Ici 0) 0 := by
  have hτ : HasDerivWithinAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ))
      ((cubicTauDeriv 0 : ℝ) : ℂ) (Ici 0) 0 := by
    exact hasDerivWithinAt_cubicTau_zero'.ofReal_comp
  have h := hτ.mul (hasDerivWithinAt_expI (s := Ici (0:ℝ)) 0)
  refine h.congr_deriv ?_
  rw [cubicGammaDeriv]
  push_cast
  simp

/-- **`γ'` is one-sidedly differentiable at the collision too**, which is what the
Lipschitz collar needs at the endpoint of `Icc 0 b`. -/
theorem hasDerivWithinAt_cubicGammaDeriv_zero :
    HasDerivWithinAt cubicGammaDeriv (cubicGammaDeriv2 0) (Ici 0) 0 := by
  have hpi := Real.pi_pos
  have hτ' : HasDerivWithinAt (fun t : ℝ => ((cubicTauDeriv t : ℝ) : ℂ))
      ((cubicTauDeriv2 0 : ℝ) : ℂ) (Ici 0) 0 := by
    exact (hasDerivAt_cubicTauDeriv (θ := 0) ⟨le_rfl, hpi.le⟩).hasDerivWithinAt.ofReal_comp
  have hτ : HasDerivWithinAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ))
      ((cubicTauDeriv 0 : ℝ) : ℂ) (Ici 0) 0 := by
    exact hasDerivWithinAt_cubicTau_zero'.ofReal_comp
  have hinner := hτ'.add (hτ.mul_const Complex.I)
  have h := (hasDerivWithinAt_expI (s := Ici (0:ℝ)) 0).mul hinner
  refine h.congr_deriv ?_
  rw [cubicGammaDeriv2]
  push_cast
  simp
  linear_combination ((cubicTau 0 : ℝ) : ℂ) * Complex.I_sq

/-- **The Lipschitz collar on `γ'`.**  `γ''` is continuous on the closed arc and the
collar is compact, so a constant exists; no closed form is needed. -/
theorem exists_cubicLip {b : ℝ} (hb0 : 0 < b) (hbπ : b < π) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ ∈ Icc (0 : ℝ) b,
      ‖cubicGammaDeriv θ - cubicGammaDeriv 0‖ ≤ L * θ :=
  exists_lipschitz_of_continuousOn_deriv2 (f := cubicGammaDeriv) (f' := cubicGammaDeriv2)
    hb0 hasDerivWithinAt_cubicGammaDeriv_zero
    (fun _ hx => hasDerivAt_cubicGammaDeriv ⟨hx.1, lt_of_le_of_lt hx.2 hbπ⟩)
    (continuousOn_cubicGammaDeriv2.mono (Icc_subset_Icc le_rfl hbπ.le))

/-- The cofactor's derivative along the cubic branch.  On the open arc
`ftCofactorAlong cubicQ 1 cubicZarc cubicTau` is `ftCriticalAlong cubicQ 1 cubicTau`
over `ftPrincipal cubicTau`, and this is the quotient rule applied to that, with
`cubicGammaDeriv` supplying `γ'`. -/
noncomputable def cubicCofactorDeriv (θ : ℝ) : ℂ :=
  (cubicGammaDeriv θ * (derivative (ftCritical cubicQ 1)).eval (ftPrincipal cubicTau θ)
      * ftPrincipal cubicTau θ
    - ftCriticalAlong cubicQ 1 cubicTau θ * cubicGammaDeriv θ)
    / ftPrincipal cubicTau θ ^ 2

theorem hasDerivAt_cubicCofactorAlong {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (ftCofactorAlong cubicQ 1 cubicZarc cubicTau) (cubicCofactorDeriv θ) θ := by
  have hγ0 : ftPrincipal cubicTau θ ≠ 0 := ftPrincipal_cubicTau_ne_zero θ
  have hγ := hasDerivAt_ftPrincipal_cubicTau hθ
  have hE := hasDerivAt_ftCriticalAlong (Q := cubicQ) (r := 1) (τ := cubicTau) hγ
  have hfeq : ftCofactorAlong cubicQ 1 cubicZarc cubicTau =ᶠ[nhds θ]
      fun s : ℝ => ftCriticalAlong cubicQ 1 cubicTau s / ftPrincipal cubicTau s := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
    exact ftCofactorAlong_eq_ftCritical_div le_rfl (ftPrincipal_cubicTau_ne_zero s)
      (cubic_pole_data hs).1
  refine ((hE.div hγ hγ0).congr_of_eventuallyEq hfeq).congr_deriv ?_
  rw [cubicCofactorDeriv]

/-- **The collar's binders are met at a DOUBLE collision.**  `m = 2` here, which is the
case no earlier witness reaches: `ftCollisionOrder_cubic_zero` puts the multiplicity at
`2`, and the factorization below carries that exponent. -/
theorem cubicPencil_collar_witness :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ π / 2 ∧ 0 ≤ C ∧
      ∀ θ ∈ Ioo (0 : ℝ) b',
        |(cubicCofactorDeriv θ
            / ftCofactorAlong cubicQ 1 cubicZarc cubicTau θ).im| ≤ C := by
  have hpi := Real.pi_pos
  have hb0 : (0 : ℝ) < π / 2 := by linarith
  have hbπ : π / 2 < π := by linarith
  obtain ⟨L, hL0, hLip⟩ := exists_cubicLip hb0 hbπ
  refine exists_bound_im_logDeriv_ftCofactorAlong_lower (Q := cubicQ) (r := 1)
    (z := cubicZarc) (τ := cubicTau) (dγ := cubicGammaDeriv) (dS := cubicCofactorDeriv)
    (H := -(2 * X + 1)) (m := 2) (b := π / 2) (L := L) le_rfl hb0 hL0
    ftCritical_cubicQ_endpoint_factor eval_cubic_endpoint_H_ne_zero
    (by rw [ftPrincipal_cubicTau_zero']; exact one_ne_zero)
    hasDerivWithinAt_ftPrincipal_cubicTau_zero
    (fun θ hθ => hasDerivAt_ftPrincipal_cubicTau ⟨hθ.1, lt_of_le_of_lt hθ.2 hbπ⟩)
    hLip (cubicGammaDeriv_ne_zero 0)
    (fun δ hδ => (cubic_pole_data ⟨hδ.1, lt_of_le_of_lt hδ.2 hbπ⟩).1)
    (fun δ hδ => hasDerivAt_cubicCofactorAlong ⟨hδ.1, lt_of_le_of_lt hδ.2 hbπ⟩)

/-! ### The far end of the arc

The upper endpoint is a collision too — `E`'s other zero, `-1/2`, and a **simple** one —
so it needs the collar as well, and `ftPrincipal` does not reflect, so the branch data is
taken at the reflected path.  Everything below mirrors the lower end with `Iic π` in place
of `Ici 0`.
-/

theorem cubicTau_eventuallyEq_cf_pi :
    cubicTau =ᶠ[nhdsWithin π (Iic π)] fun t : ℝ => 1 / (2 * Real.cos ((π - t) / 3)) := by
  have hpi := Real.pi_pos
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hpi).filter_mono nhdsWithin_le_nhds] with t h1 h2
  exact cubicTau_closed_form ⟨h2.le, h1⟩

/-- **One-sided differentiability of the branch at the far collision.** -/
theorem hasDerivWithinAt_cubicTau_pi :
    HasDerivWithinAt cubicTau (cubicTauDeriv π) (Iic π) π := by
  have hcos : Real.cos ((π - π) / 3) ≠ 0 := by rw [sub_self]; simp
  exact (hasDerivAt_cubicTauCF hcos).hasDerivWithinAt.congr_of_eventuallyEq
    cubicTau_eventuallyEq_cf_pi (cubicTau_closed_form ⟨Real.pi_pos.le, le_rfl⟩)

private theorem hasDerivWithinAt_expI' (θ : ℝ) {s : Set ℝ} :
    HasDerivWithinAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I)) s θ :=
  ((((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).cexp).hasDerivWithinAt

theorem hasDerivWithinAt_ftPrincipal_cubicTau_pi :
    HasDerivWithinAt (ftPrincipal cubicTau) (cubicGammaDeriv π) (Iic π) π := by
  have hτ : HasDerivWithinAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ))
      ((cubicTauDeriv π : ℝ) : ℂ) (Iic π) π := hasDerivWithinAt_cubicTau_pi.ofReal_comp
  have h := hτ.mul (hasDerivWithinAt_expI' (s := Iic π) π)
  refine h.congr_deriv ?_
  rw [cubicGammaDeriv]
  simp
  ring

/-- **`γ'` is one-sidedly differentiable at the far collision too.** -/
theorem hasDerivWithinAt_cubicGammaDeriv_pi :
    HasDerivWithinAt cubicGammaDeriv (cubicGammaDeriv2 π) (Iic π) π := by
  have hpi := Real.pi_pos
  have hτ' : HasDerivWithinAt (fun t : ℝ => ((cubicTauDeriv t : ℝ) : ℂ))
      ((cubicTauDeriv2 π : ℝ) : ℂ) (Iic π) π :=
    (hasDerivAt_cubicTauDeriv (θ := π) ⟨hpi.le, le_rfl⟩).hasDerivWithinAt.ofReal_comp
  have hτ : HasDerivWithinAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ))
      ((cubicTauDeriv π : ℝ) : ℂ) (Iic π) π := hasDerivWithinAt_cubicTau_pi.ofReal_comp
  have hinner := hτ'.add (hτ.mul_const Complex.I)
  have h := (hasDerivWithinAt_expI' (s := Iic π) π).mul hinner
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, cubicGammaDeriv2]
  linear_combination
    (Complex.exp ((π : ℂ) * Complex.I) * ((cubicTau π : ℝ) : ℂ)) * Complex.I_sq

/-! ### The same, at the arc's own parametrization

The collar above is stated at `cubicTau`, the closed-form radius.  What the branch supply
actually consumes is `ftTauArcAt`, the arc's own extension, and the two are not the same
function — they agree on the closed arc and nowhere is that automatic.  Below the collar is
transferred, which is what makes it a statement about the object the supply uses.

`ftTauArcAt` is **not** differentiable at `0` (`not_differentiableAt_ftTauArcAt_cubic_zero`),
and the transfer goes through anyway: the collar asks for a derivative there only within
`Ici 0`, which is all an arc endpoint has.
-/

/-- The cubic pencil's radius in the **arc's own** parametrization, with the upper
endpoint value supplied. -/
noncomputable def cubicArcTau : ℝ → ℝ := ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2)

/-- Its spectral parameter. -/
noncomputable def cubicArcZ : ℝ → ℝ := fun θ => cubicZ (cubicArcTau θ) θ

theorem cubicArcTau_eq {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) : cubicArcTau θ = cubicTau θ :=
  ftTauArcAt_eq_cubicTau hθ

theorem ftPrincipal_cubicArcTau_eq {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    ftPrincipal cubicArcTau θ = ftPrincipal cubicTau θ := by
  rw [ftPrincipal, ftPrincipal, cubicArcTau_eq hθ]

theorem ftCofactorAlong_cubicArc_eq {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) π) :
    ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ
      = ftCofactorAlong cubicQ 1 cubicZarc cubicTau θ := by
  rw [ftCofactorAlong, ftCofactorAlong, ftPrincipal_cubicArcTau_eq hθ]
  congr 2
  rw [cubicArcZ, cubicZarc, cubicArcTau_eq hθ]

/-- **The collar's binders are met at the arc's own parametrization**, not only at the
closed-form radius: `ftTauArcAt` agrees with `cubicTau` on the closed arc, so the whole
collar transfers, and the derivative at the collision is the one-sided one the collar
asks for — which is all that exists there. -/
theorem cubicArcPencil_collar_witness :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ π / 2 ∧ 0 ≤ C ∧
      ∀ θ ∈ Ioo (0 : ℝ) b',
        |(cubicCofactorDeriv θ
            / ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ).im| ≤ C := by
  have hpi := Real.pi_pos
  have hb0 : (0 : ℝ) < π / 2 := by linarith
  have hbπ : π / 2 < π := by linarith
  obtain ⟨L, hL0, hLip⟩ := exists_cubicLip hb0 hbπ
  have hzero : ftPrincipal cubicArcTau 0 = ftPrincipal cubicTau 0 :=
    ftPrincipal_cubicArcTau_eq ⟨le_rfl, hpi.le⟩
  have hnb : ∀ x ∈ Ioo (0 : ℝ) π,
      ftPrincipal cubicArcTau =ᶠ[nhds x] ftPrincipal cubicTau := by
    intro x hx
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    exact ftPrincipal_cubicArcTau_eq ⟨hs.1.le, hs.2.le⟩
  refine exists_bound_im_logDeriv_ftCofactorAlong_lower (Q := cubicQ) (r := 1)
    (z := cubicArcZ) (τ := cubicArcTau) (dγ := cubicGammaDeriv) (dS := cubicCofactorDeriv)
    (H := -(2 * X + 1)) (m := 2) (b := π / 2) (L := L) le_rfl hb0 hL0 ?_ ?_ ?_ ?_ ?_
    hLip (cubicGammaDeriv_ne_zero 0) ?_ ?_
  · rw [hzero]; exact ftCritical_cubicQ_endpoint_factor
  · rw [hzero]; exact eval_cubic_endpoint_H_ne_zero
  · rw [hzero, ftPrincipal_cubicTau_zero']; exact one_ne_zero
  · refine hasDerivWithinAt_ftPrincipal_cubicTau_zero.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with t h1 h2
      exact ftPrincipal_cubicArcTau_eq ⟨h1, h2.le⟩
    · exact hzero
  · intro θ hθ
    exact (hasDerivAt_ftPrincipal_cubicTau ⟨hθ.1, lt_of_le_of_lt hθ.2 hbπ⟩).congr_of_eventuallyEq
      (hnb θ ⟨hθ.1, lt_of_le_of_lt hθ.2 hbπ⟩)
  · intro δ hδ
    have hδπ : δ ∈ Ioo (0 : ℝ) π := ⟨hδ.1, lt_of_le_of_lt hδ.2 hbπ⟩
    have h := (cubic_pole_data hδπ).1
    rw [show ((cubicArcZ δ : ℝ) : ℂ) = ((cubicZ (cubicTau δ) δ : ℝ) : ℂ) by
      rw [cubicArcZ, cubicArcTau_eq ⟨hδπ.1.le, hδπ.2.le⟩],
      ftPrincipal_cubicArcTau_eq ⟨hδπ.1.le, hδπ.2.le⟩]
    exact h
  · intro δ hδ
    have hδπ : δ ∈ Ioo (0 : ℝ) π := ⟨hδ.1, lt_of_le_of_lt hδ.2 hbπ⟩
    refine (hasDerivAt_cubicCofactorAlong hδπ).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hδπ] with s hs
    exact ftCofactorAlong_cubicArc_eq ⟨hs.1.le, hs.2.le⟩

theorem ftPrincipal_cubicTau_pi : ftPrincipal cubicTau π = -(1 / 2) := by
  rw [ftPrincipal, cubicTau_pi, Complex.exp_pi_mul_I]
  push_cast
  ring

theorem ftCritical_cubicQ_upper_factor :
    ftCritical cubicQ 1
      = (X - C (ftPrincipal cubicTau π)) ^ 1 * (-(2 * (1 - X) ^ 2)) := by
  rw [ftPrincipal_cubicTau_pi]
  refine Polynomial.funext fun t => ?_
  rw [ftCritical_cubicQ]
  simp only [eval_neg, eval_mul, eval_pow, eval_sub, eval_add, eval_one, eval_X, eval_C,
    eval_ofNat]
  ring

theorem eval_cubic_upper_H_ne_zero :
    (-(2 * (1 - X) ^ 2) : Polynomial ℂ).eval (ftPrincipal cubicTau π) ≠ 0 := by
  rw [ftPrincipal_cubicTau_pi]
  simp only [eval_neg, eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_ofNat]
  norm_num

/-- `γ'` read from the **upper** endpoint, in the reflected coordinate `δ = π - θ`.
The sign is the chain rule factor of the reflection, so this is the derivative of
`δ ↦ γ(π - δ)` rather than `γ'` transported. -/
noncomputable def cubicUpperGammaDeriv : ℝ → ℂ := fun δ => -cubicGammaDeriv (π - δ)

private theorem hasDerivWithinAt_reflect (s : Set ℝ) (x : ℝ) :
    HasDerivWithinAt (fun u : ℝ => π - u) (-1 : ℝ) s x := by
  simpa using ((hasDerivAt_id x).const_sub π).hasDerivWithinAt

theorem hasDerivWithinAt_cubicUpperGammaDeriv_zero :
    HasDerivWithinAt cubicUpperGammaDeriv (cubicGammaDeriv2 (π - 0)) (Ici 0) 0 := by
  have hmap : MapsTo (fun u : ℝ => π - u) (Ici (0 : ℝ)) (Iic π) := by
    intro u hu; simp only [mem_Ici] at hu; simp only [mem_Iic]; linarith
  have h := HasDerivWithinAt.scomp (x := (0 : ℝ)) (t' := Iic π)
    (by simpa using hasDerivWithinAt_cubicGammaDeriv_pi)
    (hasDerivWithinAt_reflect (Ici (0 : ℝ)) 0) hmap
  refine h.neg.congr_deriv ?_
  simp

theorem hasDerivAt_cubicUpperGammaDeriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) π) :
    HasDerivAt cubicUpperGammaDeriv (cubicGammaDeriv2 (π - x)) x := by
  have hrefl : HasDerivAt (fun u : ℝ => π - u) (-1 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_sub π
  have hmem : π - x ∈ Ioo (0 : ℝ) π := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  refine ((hasDerivAt_cubicGammaDeriv hmem).scomp x hrefl).neg.congr_deriv ?_
  simp

theorem exists_cubicUpperLip {b : ℝ} (hb0 : 0 < b) (hbπ : b < π) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ δ ∈ Icc (0 : ℝ) b,
      ‖cubicUpperGammaDeriv δ - cubicUpperGammaDeriv 0‖ ≤ L * δ := by
  refine exists_lipschitz_of_continuousOn_deriv2 (f := cubicUpperGammaDeriv)
    (f' := fun δ : ℝ => cubicGammaDeriv2 (π - δ)) hb0
    hasDerivWithinAt_cubicUpperGammaDeriv_zero
    (fun x hx => hasDerivAt_cubicUpperGammaDeriv ⟨hx.1, lt_of_le_of_lt hx.2 hbπ⟩) ?_
  refine ContinuousOn.comp continuousOn_cubicGammaDeriv2 (by fun_prop) ?_
  intro u hu
  simp only [mem_Icc] at hu ⊢
  constructor <;> linarith [hbπ.le, hu.1, hu.2]

theorem hasDerivAt_cubicArcCofactorAlong {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    HasDerivAt (ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau)
      (cubicCofactorDeriv θ) θ := by
  refine (hasDerivAt_cubicCofactorAlong hθ).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
  exact ftCofactorAlong_cubicArc_eq ⟨hs.1.le, hs.2.le⟩

theorem ftCofactorAlong_cubicArc_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ ≠ 0 := by
  rw [ftCofactorAlong_cubicArc_eq ⟨hθ.1.le, hθ.2.le⟩]
  exact ftCofactorAlong_ne_zero le_rfl (ftPrincipal_cubicTau_ne_zero θ)
    (cubic_pole_data hθ).1 (ftCriticalAlong_cubic_ne_zero hθ)

theorem continuousOn_cubicCofactorDeriv :
    ContinuousOn cubicCofactorDeriv (Ioo (0 : ℝ) π) := by
  have hγ : ContinuousOn (ftPrincipal cubicTau) (Ioo (0 : ℝ) π) :=
    fun s hs => (hasDerivAt_ftPrincipal_cubicTau hs).continuousAt.continuousWithinAt
  have hdγ : ContinuousOn cubicGammaDeriv (Ioo (0 : ℝ) π) :=
    fun s hs => (hasDerivAt_cubicGammaDeriv hs).continuousAt.continuousWithinAt
  have hp : ∀ P : Polynomial ℂ,
      ContinuousOn (fun s : ℝ => P.eval (ftPrincipal cubicTau s)) (Ioo (0 : ℝ) π) :=
    fun P => (Polynomial.continuous P).comp_continuousOn hγ
  have hne : ∀ s ∈ Ioo (0 : ℝ) π, ftPrincipal cubicTau s ^ 2 ≠ 0 :=
    fun s _ => pow_ne_zero 2 (ftPrincipal_cubicTau_ne_zero s)
  refine ContinuousOn.congr (f := fun θ : ℝ =>
    (cubicGammaDeriv θ * (derivative (ftCritical cubicQ 1)).eval (ftPrincipal cubicTau θ)
        * ftPrincipal cubicTau θ
      - ftCriticalAlong cubicQ 1 cubicTau θ * cubicGammaDeriv θ)
      / ftPrincipal cubicTau θ ^ 2) ?_ (fun t _ => rfl)
  exact ContinuousOn.div
    (((hdγ.mul (hp _)).mul hγ).sub ((hp _).mul hdγ)) (hγ.pow 2) hne

/-- **The collar at the far collision**, at the arc's own parametrization. -/
theorem cubicArcPencil_upper_collar_witness :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ π / 2 ∧ 0 ≤ C ∧
      ∀ θ ∈ Ioo (π - b') π,
        |(cubicCofactorDeriv θ
            / ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ).im| ≤ C := by
  have hpi := Real.pi_pos
  have hb0 : (0 : ℝ) < π / 2 := by linarith
  have hbπ : π / 2 < π := by linarith
  obtain ⟨L, hL0, hLip⟩ := exists_cubicUpperLip hb0 hbπ
  have hπeq : ftPrincipal cubicArcTau π = ftPrincipal cubicTau π :=
    ftPrincipal_cubicArcTau_eq ⟨hpi.le, le_rfl⟩
  refine exists_bound_im_logDeriv_ftCofactorAlong_upper (Q := cubicQ) (r := 1)
    (z := cubicArcZ) (τ := cubicArcTau) (dγ := cubicUpperGammaDeriv)
    (dS := cubicCofactorDeriv) (H := -(2 * (1 - X) ^ 2)) (m := 1) (c := π)
    (b := π / 2) (L := L) le_rfl hb0 hL0 ?_ ?_ ?_ ?_ ?_ hLip ?_ ?_ ?_
  · rw [hπeq]; exact ftCritical_cubicQ_upper_factor
  · rw [hπeq]; exact eval_cubic_upper_H_ne_zero
  · rw [hπeq, ftPrincipal_cubicTau_pi]; norm_num
  · have hmap : MapsTo (fun u : ℝ => π - u) (Ici (0 : ℝ)) (Iic π) := by
      intro u hu; simp only [mem_Ici] at hu; simp only [mem_Iic]; linarith
    have hrefl : HasDerivWithinAt (fun u : ℝ => π - u) (-1 : ℝ) (Ici (0 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_sub π).hasDerivWithinAt
    have h := HasDerivWithinAt.scomp_of_eq (x := (0 : ℝ)) (t' := Iic π)
      hasDerivWithinAt_ftPrincipal_cubicTau_pi hrefl hmap (by ring)
    simp only [Function.comp_def] at h
    have h1 : HasDerivWithinAt (fun s : ℝ => ftPrincipal cubicTau (π - s))
        (cubicUpperGammaDeriv 0) (Ici 0) 0 := by
      refine h.congr_deriv ?_
      simp [cubicUpperGammaDeriv]
    refine h1.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with t h1' h2'
      simp only [mem_Ici] at h1'
      exact ftPrincipal_cubicArcTau_eq ⟨by linarith, by linarith⟩
    · exact ftPrincipal_cubicArcTau_eq ⟨by linarith, by linarith⟩
  · intro δ hδ
    have hmem : π - δ ∈ Ioo (0 : ℝ) π := ⟨by linarith [hδ.2, hbπ], by linarith [hδ.1]⟩
    have hrefl : HasDerivAt (fun u : ℝ => π - u) (-1 : ℝ) δ := by
      simpa using (hasDerivAt_id δ).const_sub π
    have h := (hasDerivAt_ftPrincipal_cubicTau hmem).scomp δ hrefl
    simp only [Function.comp_def] at h
    have h1 : HasDerivAt (fun s : ℝ => ftPrincipal cubicTau (π - s))
        (cubicUpperGammaDeriv δ) δ := by
      refine h.congr_deriv ?_
      simp [cubicUpperGammaDeriv]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds
      (show δ ∈ Ioo (0:ℝ) π from ⟨hδ.1, by linarith [hδ.2, hbπ]⟩)] with s hs
    exact ftPrincipal_cubicArcTau_eq ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · simpa [cubicUpperGammaDeriv] using cubicGammaDeriv_ne_zero π
  · intro δ hδ
    have hmem : π - δ ∈ Ioo (0 : ℝ) π := ⟨by linarith [hδ.2, hbπ], by linarith [hδ.1]⟩
    have h := (cubic_pole_data hmem).1
    rw [show ((cubicArcZ (π - δ) : ℝ) : ℂ) = ((cubicZ (cubicTau (π - δ)) (π - δ) : ℝ) : ℂ) by
      rw [cubicArcZ, cubicArcTau_eq ⟨hmem.1.le, hmem.2.le⟩],
      ftPrincipal_cubicArcTau_eq ⟨hmem.1.le, hmem.2.le⟩]
    exact h
  · intro δ hδ
    have hmem : π - δ ∈ Ioo (0 : ℝ) π := ⟨by linarith [hδ.2, hbπ], by linarith [hδ.1]⟩
    exact hasDerivAt_cubicArcCofactorAlong hmem

/-- **`κ₀` at the cubic pencil.**  The collar at each collision and compactness in
between, assembled by `exists_kappaZero_of_cover`. -/
theorem cubicArc_exists_kappaZero :
    ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧
      eVariationOn (ftFixedAngle cubicQ 1 cubicArcZ cubicArcTau cubicCofactorDeriv (π / 2))
        (Ioo (0 : ℝ) π) ≤ ENNReal.ofReal κ₀ := by
  have hpi := Real.pi_pos
  have h1 : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  obtain ⟨b₁, C₁, hb₁0, hb₁, hC₁, hlo⟩ := cubicArcPencil_collar_witness
  obtain ⟨b₂, C₃, hb₂0, hb₂, hC₃, hhi⟩ := cubicArcPencil_upper_collar_witness
  have hsubmid : Icc b₁ (π - b₂) ⊆ Ioo (0 : ℝ) π := fun x hx =>
    ⟨lt_of_lt_of_le hb₁0 hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩
  obtain ⟨C₂, hmid⟩ := exists_bound_im_logDeriv_ftCofactorAlong_mid
    (Q := cubicQ) (r := 1) (z := cubicArcZ) (τ := cubicArcTau) (dS := cubicCofactorDeriv)
    (b₁ := b₁) (b₂ := π - b₂)
    (by rw [h1]; exact fun s hs => hasDerivAt_cubicArcCofactorAlong hs)
    (by rw [h1]; exact continuousOn_cubicCofactorDeriv)
    (by rw [h1]; exact fun s hs => ftCofactorAlong_cubicArc_ne_zero hs)
    (by rw [h1]; exact hsubmid)
  obtain ⟨κ₀, hκ0, hvar⟩ := exists_kappaZero_of_cover
    (Q := cubicQ) (r := 1) (z := cubicArcZ) (τ := cubicArcTau) (dS := cubicCofactorDeriv)
    (c₀ := π / 2) (b₁ := b₁) (b₂ := π - b₂) (C₁ := C₁) (C₂ := C₂) (C₃ := C₃)
    (by rw [h1]; exact hpi.le)
    (by rw [h1]; exact fun s hs => hasDerivAt_cubicArcCofactorAlong hs)
    (by rw [h1]; exact continuousOn_cubicCofactorDeriv)
    (by rw [h1]; exact fun s hs => ftCofactorAlong_cubicArc_ne_zero hs)
    (by rw [h1]; exact ⟨by linarith, by linarith⟩)
    hlo hmid (by rw [h1]; exact hhi)
  refine ⟨κ₀, hκ0, ?_⟩
  rw [h1] at hvar
  exact hvar

/-! ### The geometry group, and the amplitude, at this pencil

What `exists_uniform_ftBranchSupply` still wants of the branch — `hγd`, `hd2`, `hc2`,
`hreg` — and of the amplitude — `hWd`, `hWc`, `hW0`, `hWL`.  All of it on the **open** arc
now, which is where the supply asks for it since the branch pins moved off the endpoints.

`hW0` and `hWL` are the division convention rather than a vanishing amplitude: `∂_t D`
vanishes at each collision, so the formalized `ftAmp` is `0` there whatever the weight
does.  `hWd` holds on the whole open arc including `π/2`, where the tree's own
`hasDerivAt_cubicAmp` stops — its route divides by the amplitude and this one does not.
-/

theorem hasDerivAt_ftPrincipal_cubicArcTau {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    HasDerivAt (ftPrincipal cubicArcTau) (cubicGammaDeriv θ) θ := by
  refine (hasDerivAt_ftPrincipal_cubicTau hθ).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
  exact ftPrincipal_cubicArcTau_eq ⟨hs.1.le, hs.2.le⟩

/-- The pencil's residue amplitude in the **arc's own** parametrization, built
from `cubicArcTau` and `cubicArcZ` rather than from `cubicTau`.  It is therefore
defined off `[0, π]` too, and agrees with `cubicAmp` on the closed arc
(`CubicRootStates.cubicArcAmp_eq_cubicAmp`). -/
noncomputable def cubicArcAmp (B : Polynomial ℂ) (θ : ℝ) : ℂ :=
  ftAmp cubicQ B 1 ((cubicArcZ θ : ℝ) : ℂ) (ftPrincipal cubicArcTau θ)

theorem cubicArcZ_zero : cubicArcZ 0 = 0 := by
  have h : cubicArcTau 0 = 1 := by
    rw [cubicArcTau_eq ⟨le_rfl, Real.pi_pos.le⟩, cubicTau_zero]
  rw [cubicArcZ, h, cubicZ]
  norm_num

theorem cubicArcZ_pi : cubicArcZ π = 27 / 4 := by
  have h : cubicArcTau π = 1 / 2 := by
    rw [cubicArcTau_eq ⟨Real.pi_pos.le, le_rfl⟩, cubicTau_pi]
  rw [cubicArcZ, h, cubicZ]
  norm_num

/-- **`hW0`.**  At the collision `∂_t D` vanishes, so the formalized amplitude is `0` by
the division convention — which is what the arc assembly asks for at the ends. -/
theorem cubicArcAmp_zero (B : Polynomial ℂ) : cubicArcAmp B 0 = 0 := by
  have hprin : ftPrincipal cubicArcTau 0 = 1 := by
    rw [ftPrincipal_cubicArcTau_eq ⟨le_rfl, Real.pi_pos.le⟩, ftPrincipal_cubicTau_zero']
  have hden : ftDen cubicQ 1 ((cubicArcZ 0 : ℝ) : ℂ) = cubicQ := by
    rw [cubicArcZ_zero, ftDen]
    push_cast
    simp
  have hroot : (ftDen cubicQ 1 ((cubicArcZ 0 : ℝ) : ℂ)).eval (ftPrincipal cubicArcTau 0) = 0 := by
    rw [hden, hprin, cubicQ_eval]
    norm_num
  have hcof : (ftCofactor cubicQ 1 ((cubicArcZ 0 : ℝ) : ℂ) (ftPrincipal cubicArcTau 0)).eval
      (ftPrincipal cubicArcTau 0) = 0 := by
    rw [← eval_derivative_ftDen hroot, hden, hprin, cubicQ]
    simp [derivative_pow]
  rw [cubicArcAmp, ftAmp, hcof, div_zero, neg_zero]

/-- **`hWL`.**  The same at the far collision. -/
theorem cubicArcAmp_pi (B : Polynomial ℂ) : cubicArcAmp B π = 0 := by
  have hprin : ftPrincipal cubicArcTau π = -(1 / 2) := by
    rw [ftPrincipal_cubicArcTau_eq ⟨Real.pi_pos.le, le_rfl⟩, ftPrincipal_cubicTau_pi]
  have hroot : (ftDen cubicQ 1 ((cubicArcZ π : ℝ) : ℂ)).eval (ftPrincipal cubicArcTau π) = 0 := by
    rw [hprin, cubicArcZ_pi, ftDen_eval, cubicQ_eval]
    push_cast
    norm_num
  have hcof : (ftCofactor cubicQ 1 ((cubicArcZ π : ℝ) : ℂ) (ftPrincipal cubicArcTau π)).eval
      (ftPrincipal cubicArcTau π) = 0 := by
    rw [← eval_derivative_ftDen hroot, hprin, cubicArcZ_pi, ftDen, cubicQ]
    simp [derivative_pow]
    norm_num
  rw [cubicArcAmp, ftAmp, hcof, div_zero, neg_zero]

/-- The amplitude's derivative along the arc, by the quotient rule on `-B(γ)/∂_t D`. -/
noncomputable def cubicArcAmpDeriv (B : Polynomial ℂ) (θ : ℝ) : ℂ :=
  -((cubicGammaDeriv θ * (derivative B).eval (ftPrincipal cubicArcTau θ)
      * ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ
    - B.eval (ftPrincipal cubicArcTau θ) * cubicCofactorDeriv θ)
    / ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ ^ 2)

/-- **`hWd` at the cubic**, on the whole open arc — the zero of the weight at `π/2` does
not obstruct it, because the quotient rule does not divide by the amplitude. -/
theorem hasDerivAt_cubicArcAmp (B : Polynomial ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    HasDerivAt (cubicArcAmp B) (cubicArcAmpDeriv B θ) θ := by
  have hS0 : ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ ≠ 0 :=
    ftCofactorAlong_cubicArc_ne_zero hθ
  have hB := hasDerivAt_eval_comp (γ := ftPrincipal cubicArcTau)
    (dγ := fun _ => cubicGammaDeriv θ) B (hasDerivAt_ftPrincipal_cubicArcTau hθ)
  have hS := hasDerivAt_cubicArcCofactorAlong hθ
  have h := (hB.div hS hS0).neg
  refine h.congr_deriv ?_
  rw [cubicArcAmpDeriv]

theorem continuousOn_cubicArcAmpDeriv (B : Polynomial ℂ) :
    ContinuousOn (cubicArcAmpDeriv B) (Ioo (0 : ℝ) π) := by
  have hγ : ContinuousOn (ftPrincipal cubicArcTau) (Ioo (0 : ℝ) π) :=
    fun s hs => (hasDerivAt_ftPrincipal_cubicArcTau hs).continuousAt.continuousWithinAt
  have hdγ : ContinuousOn cubicGammaDeriv (Ioo (0 : ℝ) π) :=
    fun s hs => (hasDerivAt_cubicGammaDeriv hs).continuousAt.continuousWithinAt
  have hS : ContinuousOn (ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau) (Ioo (0 : ℝ) π) :=
    fun s hs => (hasDerivAt_cubicArcCofactorAlong hs).continuousAt.continuousWithinAt
  have hp : ∀ P : Polynomial ℂ,
      ContinuousOn (fun s : ℝ => P.eval (ftPrincipal cubicArcTau s)) (Ioo (0 : ℝ) π) :=
    fun P => (Polynomial.continuous P).comp_continuousOn hγ
  have hne : ∀ s ∈ Ioo (0 : ℝ) π,
      ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau s ^ 2 ≠ 0 := fun s hs =>
    pow_ne_zero 2 (ftCofactorAlong_cubicArc_ne_zero hs)
  refine ContinuousOn.congr (f := fun θ : ℝ =>
    -((cubicGammaDeriv θ * (derivative B).eval (ftPrincipal cubicArcTau θ)
        * ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ
      - B.eval (ftPrincipal cubicArcTau θ) * cubicCofactorDeriv θ)
      / ftCofactorAlong cubicQ 1 cubicArcZ cubicArcTau θ ^ 2)) ?_ (fun t _ => rfl)
  exact (ContinuousOn.div (((hdγ.mul (hp _)).mul hS).sub
    ((hp _).mul continuousOn_cubicCofactorDeriv)) (hS.pow 2) hne).neg

/-- **The weight-free branch-geometry group of `exists_uniform_ftBranchSupply`, at the
cubic.**  Every clause on the open arc, which is where the supply now asks for them. -/
theorem cubic_geometry_group :
    (∀ s ∈ Ioo (0 : ℝ) π, HasDerivAt (ftPrincipal cubicArcTau) (cubicGammaDeriv s) s)
    ∧ (∀ s ∈ Ioo (0 : ℝ) π, HasDerivAt cubicGammaDeriv (cubicGammaDeriv2 s) s)
    ∧ ContinuousOn cubicGammaDeriv2 (Ioo (0 : ℝ) π)
    ∧ (∀ s ∈ Ioo (0 : ℝ) π, cubicGammaDeriv s ≠ 0) :=
  ⟨fun _ hs => hasDerivAt_ftPrincipal_cubicArcTau hs,
    fun _ hs => hasDerivAt_cubicGammaDeriv hs,
    continuousOn_cubicGammaDeriv2.mono Ioo_subset_Icc_self,
    fun s _ => cubicGammaDeriv_ne_zero s⟩

/-- **The amplitude group, at an arbitrary weight.**  `hWd`, `hWc`, `hW0` and `hWL` of
`exists_uniform_ftBranchSupply`, with `U = Ioo 0 π`. -/
theorem cubic_amplitude_group (B : Polynomial ℂ) :
    (∀ s ∈ Ioo (0 : ℝ) π, HasDerivAt (cubicArcAmp B) (cubicArcAmpDeriv B s) s)
    ∧ ContinuousOn (cubicArcAmpDeriv B) (Ioo (0 : ℝ) π)
    ∧ cubicArcAmp B 0 = 0 ∧ cubicArcAmp B π = 0 :=
  ⟨fun _ hs => hasDerivAt_cubicArcAmp B hs, continuousOn_cubicArcAmpDeriv B,
    cubicArcAmp_zero B, cubicArcAmp_pi B⟩

/-! ### Is `τ''` bounded at a collision, or merely unproved so?

The general collar's two remaining needs are a limit and a bound, and the bound is the one
to be suspicious of: `τ''` near a collision is where the geometry is worst.  At this pencil
it is **finite**, and computed rather than argued — `cubicTauDeriv2 0 = 7/9`, against
`ftTauDeriv2 … 0 = 0`, which is the division convention's junk.  Both reduced requirements
hold here.  So the general statement is **unproved rather than false**, which are different
findings and only the second would be about the mathematics.
-/

/-- **The branch's second derivative at the collision is `7/9` at the cubic — finite.**
`ftTauDeriv2 … 0` is `0` by the division convention (`ftTauDeriv2_zero`); the closed form's
own value there is `7/9`, and `hasDerivAt_cubicTauDeriv` holds at `0`, so that is the true
one.  The two numbers together are the `x/0` family at second order, with both sides
computed rather than argued. -/
theorem cubicTauDeriv2_zero : cubicTauDeriv2 0 = 7 / 9 := by
  have hc : Real.cos ((π - 0) / 3) = 1 / 2 := by
    rw [sub_zero]; exact Real.cos_pi_div_three
  have hs : Real.sin ((π - 0) / 3) = Real.sqrt 3 / 2 := by
    rw [sub_zero]; exact Real.sin_pi_div_three
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [cubicTauDeriv2, hc, hs]
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  nlinarith [h3]

/-- **The two statements the general collar still needs, both HOLDING at the cubic.**  The
limit — `γ'` reaches the collision's value — and the bound — `γ''` merely bounded on a
punctured collar.  Neither is vacuous, and `τ''` is *finite* at the collision rather than
merely bounded near it: `cubicTauDeriv2 0 = 7/9`. -/
theorem cubic_collar_reduced_requirements {b : ℝ} (hbπ : b < π) :
    ContinuousWithinAt cubicGammaDeriv (Ici 0) 0
      ∧ ∃ C : ℝ, ∀ θ ∈ Ioo (0 : ℝ) b, ‖cubicGammaDeriv2 θ‖ ≤ C := by
  refine ⟨hasDerivWithinAt_cubicGammaDeriv_zero.continuousWithinAt, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (continuousOn_cubicGammaDeriv2.mono (Icc_subset_Icc le_rfl hbπ.le))
  exact ⟨C, fun θ hθ => hC θ ⟨hθ.1.le, hθ.2.le⟩⟩

/-! ### The closed-arc binder is unsatisfiable at the lower endpoint

`exists_uniform_ftBranchSupply` asks `hγd`, `hd2` and `hc2` on an **open** `Uγ` containing
the closed arc, because they are passed straight to `ViewingAngle.hasDerivAt_polarAngle_base`
and `PhaseVariationBlocks.sum_eVariationOn_branch_le`, whose branch lift is an integral
whose differentiability at a parameter comes from `intervalIntegral.integral_hasDerivAt_right`
on a two-sided neighbourhood.

At the arc's lower endpoint that is not available, and no endpoint value repairs it:
`ftTauLower` extends by the constant `x₁`, slope `0`, while the branch leaves `0` with
slope `cubicTauDeriv 0 ≠ 0`.  The **values** agree, so continuity holds — which is why a
continuity lemma here proves nothing about the binder that blocks.  This is `r`-independent:
`ftTauLower` does not mention `r`, so the binder is met at any `r` only if the branch
happens to arrive with slope exactly `0`.
-/

private theorem ftTauArcAt_cubic_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2) x = 1 := by
  have hpi : x < π / ((1 : ℕ) : ℝ) := by
    rw [pi_div_natCast_one]; linarith [Real.pi_pos]
  rw [ftTauArcAt, if_pos hpi, ftTauLower, if_neg (not_lt.2 hx)]

/-- **The lower endpoint binder is unsatisfiable, not merely unproved.**  Even with the
upper endpoint repaired, `ftTauArcAt` is constant below `0` — slope `0` — while the branch
leaves `0` with slope `cubicTauDeriv 0 ≠ 0`.  The two one-sided derivatives disagree, so no
two-sided one exists. -/
theorem not_differentiableAt_ftTauArcAt_cubic_zero :
    ¬ DifferentiableAt ℝ (ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2)) 0 := by
  intro hdiff
  have hpi := Real.pi_pos
  have hleft : HasDerivWithinAt (ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2)) 0 (Iic 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (1 : ℝ)).congr
      (fun x hx => ftTauArcAt_cubic_of_nonpos hx) (ftTauArcAt_cubic_of_nonpos le_rfl)
  have hright : HasDerivWithinAt (ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2))
      (cubicTauDeriv 0) (Ici 0) 0 := by
    refine hasDerivWithinAt_cubicTau_zero'.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hpi).filter_mono nhdsWithin_le_nhds] with t h1 h2
      exact ftTauArcAt_eq_cubicTau ⟨h1, h2.le⟩
    · exact ftTauArcAt_eq_cubicTau ⟨le_rfl, hpi.le⟩
  have hL : deriv (ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2)) 0 = 0 :=
    (uniqueDiffOn_Iic (0 : ℝ) 0 (by simp)).eq_deriv _
      hdiff.hasDerivAt.hasDerivWithinAt hleft
  have hR : deriv (ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2)) 0 = cubicTauDeriv 0 :=
    (uniqueDiffOn_Ici (0 : ℝ) 0 (by simp)).eq_deriv _
      hdiff.hasDerivAt.hasDerivWithinAt hright
  exact cubicTauDeriv_zero_ne_zero (by rw [← hR, hL])

/-- **And so `hγd` itself is unsatisfiable at the lower endpoint.**  `hγd` asks for a
two-sided derivative of `ftPrincipal τ`, not of `τ`; but `τ` is recovered from it by
multiplying back by `e^{-iθ}` and taking the real part, so a derivative for one gives a
derivative for the other. -/
theorem not_exists_hasDerivAt_ftPrincipal_ftTauArcAt_cubic_zero :
    ¬ ∃ d : ℂ, HasDerivAt (ftPrincipal (ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2))) d 0 := by
  rintro ⟨d, hd⟩
  refine not_differentiableAt_ftTauArcAt_cubic_zero ?_
  have hE : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * Complex.I))
      (Complex.exp (-((0 : ℝ) : ℂ) * Complex.I) * (-1 * Complex.I)) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).neg).mul_const Complex.I).cexp
  have hmul := hd.mul hE
  have hre := hmul.re
  refine (hre.differentiableAt).congr_of_eventuallyEq ?_
  filter_upwards with s
  change ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2) s
    = (ftPrincipal (ftTauArcAt ![1, 1, 1] 1 2 1 (1 / 2)) s
        * Complex.exp (-(s : ℂ) * Complex.I)).re
  rw [ftPrincipal, mul_assoc, ← Complex.exp_add,
    show (s : ℂ) * Complex.I + -(s : ℂ) * Complex.I = 0 by ring, Complex.exp_zero, mul_one,
    Complex.ofReal_re]

end ForgacsTran
