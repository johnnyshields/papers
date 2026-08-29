/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.AngleChartForm
import ForgacsTran.EndpointBranch
import ForgacsTran.BranchSupplyGeometry

/-!
# `τ''` converges at a repeated smallest zero

`BranchSupplyGeometry.exists_lipschitz_ftGammaDerivAt_of_tendsto_ftTauDeriv2` reduces
the whole general collar to one hypothesis: that `τ''` has a limit as `θ ↓ 0`.
This module discharges it whenever the smallest zero `x_1` is repeated.

**The route is elementary.**  No Puiseux parameter, no implicit function theorem,
no analyticity at the endpoint.  Write `ρ ≥ 2` for the multiplicity of `x_1`, `C`
for the indices carrying it and `F` for the rest, and `β` for the branch angle at
a `C` index — one angle, since the `ρ` of them share their zero.  Two identities
hold across the whole arc:

  (A)  `x_1\sin β = τ\sin(β - θ)`                                (`ftAngle_spec`)
  (B)  `ρb + στ' + A_F = r`,  `b = β'`                (the branch equation, with
                                                     the `C` terms collected)

with `σ = \sum_F ∂_ττθ_j` and `A_F = \sum_F ∂_θθ_j`.  Differentiating (A) once and
taking (B) as it stands gives a linear system for `(τ', b)`; differentiating each
once more gives a system for `(τ'', β'')` with the **same** matrix

  `M = [[\sin(β-θ), Δ], [σ, ρ]]`,   `Δ = τ\cos(β-θ) - x_1\cos β`.

`AngleChartForm` makes every entry and every right-hand side a continuous
function of `(τ, θ)` at a zero the branch circle does not reach, `Δ → 0`, and
`\det M → ρ\sin(π/ρ) ≠ 0`.  Cramer's rule then closes both orders.

**Why (A) is carried separately.**  Folded into the angle sum, the `C` terms
diverge: `∂θ_k/∂τ` runs like `-ρ/θ` at a zero the branch runs into, which is why
`EndpointCofactorBound` records that `τ''` does not come from the angle sums by
algebra of limits.  What does converge is the combination `b = β'`, and (A) is
the relation that exhibits it.

## Main statements

* `tendsto_ftTau_endpoint` — `τ → x_1`, from `EndpointBranch.tendsto_ftTau_blowup`.
* `tendsto_ftClusterAngle` — `β → π - π/ρ`.
* `ftBranchSplit` — (B), the branch equation with the cluster terms collected.
* `ftClusterEqOne`, `ftClusterEqTwo` — (A) differentiated once and twice.
* `ftBranchEqTwo` — (B) differentiated.
* `exists_tendsto_ftFarSumTau`, `exists_tendsto_ftFarSumAngle`,
  `exists_tendsto_ftFarSumTauDeriv`, `exists_tendsto_ftFarSumAngleDeriv` — the far
  entries converge, through `AngleChartForm`.
* `tendsto_ftEndpointDet`, `ftEndpointDet_limit_ne` — `\det M → ρ\sin(π/ρ) ≠ 0`.
* `exists_tendsto_ftTauDeriv2` — **`τ''` converges.**
* `exists_lipschitz_ftGammaDerivAt_of_repeated_min` — the collar's Lipschitz input
  at a repeated smallest zero, with nothing left assumed.
* `exists_tendsto_ftTauDeriv2_witness` — the hypotheses instantiated, so the
  statement is not vacuous.

## Implementation notes

Sorry-free.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `sec:dominance`,
  `thm:weighted-dominance`.
* `../../scripts/check_endpoint_tau2_limit.py`.

## Tags

branch radius, second derivative, endpoint, collision, Cramer
-/

namespace ForgacsTran

open Real Set Filter Topology

variable {n r ρ : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}

/-- **The branch radius runs into the repeated zero.**  The blow-up
`(x_1 - τ)/θ` converges, so `x_1 - τ = θ·((x_1 - τ)/θ)` runs to zero. -/
theorem tendsto_ftTau_endpoint (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 x₁) := by
  have hb := tendsto_ftTau_blowup hn ha hr hnr hx₁ hmin hcard hρ
  have hθ : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmul := hθ.mul hb
  rw [zero_mul] at hmul
  have hsub : Tendsto (fun θ : ℝ => x₁ - ftTau a r (n - 1) θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ0
    have hne : θ ≠ 0 := ne_of_gt hθ0
    field_simp
  have := (tendsto_const_nhds (x := x₁) (f := 𝓝[>] (0 : ℝ))).sub hsub
  simpa using this

/-- **The cluster angle converges to `π - π/ρ`.**  The `ρ` indices carrying `x_1`
share one branch angle, and it is the argument of the chord from `x_1`, which the
blow-up sends to `\arg(-x_1\cot(π/ρ) + ix_1)`. -/
theorem tendsto_ftClusterAngle (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    Tendsto (fun θ : ℝ => ftAngle x₁ (ftTau a r (n - 1) θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi - Real.pi / ρ)) := by
  have hπ := Real.pi_pos
  set s₀ : ℝ := x₁ * (Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ)) with hs₀
  set L : ℂ := ((-s₀ : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I with hL
  have hb := tendsto_ftTau_blowup hn ha hr hnr hx₁ hmin hcard hρ
  have hτ := tendsto_ftTau_endpoint hn ha hr hnr hx₁ hmin hcard hρ
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  -- the chord, divided by `θ`, converges
  have hchord : Tendsto (fun θ : ℝ =>
      (((ftTau a r (n - 1) θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        - ((x₁ : ℝ) : ℂ)) / (θ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have h1 : Tendsto (fun θ : ℝ => (((ftTau a r (n - 1) θ - x₁ : ℝ) : ℂ)) / (θ : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((-s₀ : ℝ) : ℂ)) := by
      have hre : Tendsto (fun θ : ℝ => ((ftTau a r (n - 1) θ - x₁) / θ : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (-s₀)) := by
        refine (hb.neg).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with θ hθ0
        ring
      have := (Complex.continuous_ofReal.tendsto (-s₀)).comp hre
      refine this.congr fun θ => ?_
      simp [Function.comp_apply]
    have h2 : Tendsto (fun θ : ℝ => ((ftTau a r (n - 1) θ : ℝ) : ℂ)
        * ((Complex.exp ((θ : ℂ) * Complex.I) - 1) / (θ : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (((x₁ : ℝ) : ℂ) * Complex.I)) :=
      ((Complex.continuous_ofReal.tendsto x₁).comp hτ).mul
        (tendsto_expI_slope.mono_left hsub)
    have hsum := h1.add h2
    rw [← hL] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ0
    have hθC : ((θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hθ0
    push_cast
    field
  -- and `arg` is continuous there
  have him : L.im = x₁ := by simp [hL]
  have hslit : L ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (by rw [him]; exact ne_of_gt hx₁))
  have hcont : ContinuousAt Complex.arg L := Complex.continuousAt_arg hslit
  have hcomp := hcont.tendsto.comp hchord
  rw [hL, arg_blowup_root hx₁ hρ] at hcomp
  refine hcomp.congr' ?_
  have hτpos : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < ftTau a r (n - 1) θ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi / r by positivity)] with θ hθ
    exact ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  filter_upwards [self_mem_nhdsWithin, hτpos, Ioo_mem_nhdsGT hπ] with θ hθ0 hτθ hθπ
  have hθ0' : (0 : ℝ) < θ := hθ0
  set X : ℂ := ((ftTau a r (n - 1) θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    - ((x₁ : ℝ) : ℂ) with hXdef
  have hsplit : X = ((θ : ℝ) : ℂ) * (X / ((θ : ℝ) : ℂ)) := by
    have hθC : ((θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hθ0'
    field_simp
  rw [Function.comp_apply, ftAngle_eq_arg hτθ ⟨hθ0', hθπ.2⟩, ← hXdef]
  conv_rhs => rw [hsplit]
  exact (Complex.arg_real_mul _ hθ0').symm

/-! ### The cluster angle and the far sums -/

/-- The **far** indices: those carrying a zero strictly outside the branch's
endpoint radius.  Their partials stay bounded; the others do not. -/
noncomputable def ftFar {n : ℕ} (a : Fin n → ℝ) (x₁ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun k => ¬ (a k = x₁)

/-- `b = β'`, the derivative of the branch angle shared by the repeated zero. -/
noncomputable def ftClusterAngleDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ θ : ℝ) : ℝ :=
  -(Real.sin (ftAngle x₁ (ftTau a r l θ) θ) ^ 2 * x₁
      / (ftTau a r l θ ^ 2 * Real.sin θ)) * ftTauDeriv a r l θ
    + Real.sin (ftAngle x₁ (ftTau a r l θ) θ)
        * Real.cos (ftAngle x₁ (ftTau a r l θ) θ - θ) / Real.sin θ

/-- `β''`. -/
noncomputable def ftClusterAngleDeriv2 {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ θ : ℝ) : ℝ :=
  (ftAngleDeriv2Tau x₁ (ftTau a r l θ) θ * ftTauDeriv a r l θ
      + ftAngleDeriv2TauAngle x₁ (ftTau a r l θ) θ) * ftTauDeriv a r l θ
    + -(Real.sin (ftAngle x₁ (ftTau a r l θ) θ) ^ 2 * x₁
        / (ftTau a r l θ ^ 2 * Real.sin θ)) * ftTauDeriv2 a r l θ
    + (ftAngleDeriv2AngleTau x₁ (ftTau a r l θ) θ * ftTauDeriv a r l θ
      + ftAngleDeriv2Angle x₁ (ftTau a r l θ) θ)

/-- `σ = \sum_F ∂θ_j/∂τ`. -/
noncomputable def ftFarSumTau {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ θ : ℝ) : ℝ :=
  ∑ k ∈ ftFar a x₁, -(Real.sin (ftAngle (a k) (ftTau a r l θ) θ) ^ 2 * a k
    / (ftTau a r l θ ^ 2 * Real.sin θ))

/-- `A_F = \sum_F ∂θ_j/∂θ`. -/
noncomputable def ftFarSumAngle {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ θ : ℝ) : ℝ :=
  ∑ k ∈ ftFar a x₁, Real.sin (ftAngle (a k) (ftTau a r l θ) θ)
    * Real.cos (ftAngle (a k) (ftTau a r l θ) θ - θ) / Real.sin θ

/-- `σ'`, along the branch. -/
noncomputable def ftFarSumTauDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ θ : ℝ) : ℝ :=
  ∑ k ∈ ftFar a x₁, (ftAngleDeriv2Tau (a k) (ftTau a r l θ) θ * ftTauDeriv a r l θ
    + ftAngleDeriv2TauAngle (a k) (ftTau a r l θ) θ)

/-- `A_F'`, along the branch. -/
noncomputable def ftFarSumAngleDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ θ : ℝ) : ℝ :=
  ∑ k ∈ ftFar a x₁, (ftAngleDeriv2AngleTau (a k) (ftTau a r l θ) θ * ftTauDeriv a r l θ
    + ftAngleDeriv2Angle (a k) (ftTau a r l θ) θ)

/-! ### The derivatives that exist on the arc -/

theorem hasDerivAt_ftClusterAngle (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    HasDerivAt (fun t => ftAngle x₁ (ftTau a r (n - 1) t) t)
      (ftClusterAngleDeriv a r (n - 1) x₁ θ) θ := by
  have hb : ∀ t ∈ Ioo (0:ℝ) (π / r), FTBranchAt a r (n - 1) t := fun _ ht =>
    ftBranchAt_of_arc_principal hn ha hr hnr ht
  exact hasDerivAt_ftAngle_comp hx₁ (hasDerivAt_ftTau hn ha hr hθ hb)
    (ftTau_pos (hb θ hθ)) (ftArc_subset hr hθ)

theorem hasDerivAt_ftClusterAngleDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftClusterAngleDeriv a r (n - 1) x₁)
      (ftClusterAngleDeriv2 a r (n - 1) x₁ θ) θ := by
  have hb : ∀ t ∈ Ioo (0:ℝ) (π / r), FTBranchAt a r (n - 1) t := fun _ ht =>
    ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hT := hasDerivAt_ftTau hn ha hr hθ hb
  have hpos := ftTau_pos (hb θ hθ)
  have hθπ := ftArc_subset hr hθ
  have hP := hasDerivAt_ftAngleDerivTau_comp hx₁ hT hpos hθπ
  have hA := hasDerivAt_ftAngleDerivAngle_comp hx₁ hT hpos hθπ
  have hD := hasDerivAt_ftTauDeriv hn ha hr hθ hb
  exact ((hP.mul hD).add hA)

theorem hasDerivAt_ftFarSumTau (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftFarSumTau a r (n - 1) x₁) (ftFarSumTauDeriv a r (n - 1) x₁ θ) θ := by
  have hb : ∀ t ∈ Ioo (0:ℝ) (π / r), FTBranchAt a r (n - 1) t := fun _ ht =>
    ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hT := hasDerivAt_ftTau hn ha hr hθ hb
  exact HasDerivAt.fun_sum fun k _ =>
    hasDerivAt_ftAngleDerivTau_comp (ha k) hT (ftTau_pos (hb θ hθ)) (ftArc_subset hr hθ)

theorem hasDerivAt_ftFarSumAngle (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftFarSumAngle a r (n - 1) x₁) (ftFarSumAngleDeriv a r (n - 1) x₁ θ) θ := by
  have hb : ∀ t ∈ Ioo (0:ℝ) (π / r), FTBranchAt a r (n - 1) t := fun _ ht =>
    ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hT := hasDerivAt_ftTau hn ha hr hθ hb
  exact HasDerivAt.fun_sum fun k _ =>
    hasDerivAt_ftAngleDerivAngle_comp (ha k) hT (ftTau_pos (hb θ hθ)) (ftArc_subset hr hθ)

/-! ### The two identities -/

/-- **(B).**  The branch equation with the `ρ` cluster terms collected: their
individual partials diverge at the endpoint, their combination `b` does not. -/
theorem ftBranchSplit (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) :
    (ρ : ℝ) * ftClusterAngleDeriv a r (n - 1) x₁ θ
        + ftFarSumTau a r (n - 1) x₁ θ * ftTauDeriv a r (n - 1) θ
        + ftFarSumAngle a r (n - 1) x₁ θ
      = r := by
  classical
  have hb := ftBranchAt_of_arc_principal hn ha hr hnr hθ
  have hpos := ftTau_pos hb
  have hθπ := ftArc_subset hr hθ
  have hne : ftAngleSumDerivTau a (ftTau a r (n - 1) θ) θ ≠ 0 :=
    (ftAngleSumDerivTau_neg hn ha hpos hθπ).ne
  have hquot : ftTauDeriv a r (n - 1) θ
      * ftAngleSumDerivTau a (ftTau a r (n - 1) θ) θ
      = r - ftAngleSumDerivAngle a (ftTau a r (n - 1) θ) θ := by
    rw [ftTauDeriv, div_mul_cancel₀ _ hne]; ring
  -- split each partial sum at the cluster
  have hsplitT : ftAngleSumDerivTau a (ftTau a r (n - 1) θ) θ
      = (ρ : ℝ) * -(Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ) ^ 2 * x₁
            / (ftTau a r (n - 1) θ ^ 2 * Real.sin θ))
        + ftFarSumTau a r (n - 1) x₁ θ := by
    rw [ftAngleSumDerivTau, ftFarSumTau, ftFar,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => a k = x₁)]
    congr 1
    rw [Finset.sum_congr rfl (fun k hk => by
        rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const, hcard, nsmul_eq_mul]
  have hsplitA : ftAngleSumDerivAngle a (ftTau a r (n - 1) θ) θ
      = (ρ : ℝ) * (Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ)
            * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ) / Real.sin θ)
        + ftFarSumAngle a r (n - 1) x₁ θ := by
    rw [ftAngleSumDerivAngle, ftFarSumAngle, ftFar,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => a k = x₁)]
    congr 1
    rw [Finset.sum_congr rfl (fun k hk => by
        rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const, hcard, nsmul_eq_mul]
  rw [hsplitT, hsplitA] at hquot
  rw [ftClusterAngleDeriv]
  linarith [hquot]

/-- (A) differentiated once, as a `HasDerivAt` in general shape. -/
private theorem hasDerivAt_clusterRel {T B : ℝ → ℝ} {T' B' t x : ℝ}
    (hT : HasDerivAt T T' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun u => x * Real.sin (B u) - T u * Real.sin (B u - u))
      (x * (Real.cos (B t) * B')
        - (T' * Real.sin (B t - t) + T t * (Real.cos (B t - t) * (B' - 1)))) t := by
  refine (((hB.sin).const_mul x).sub (hT.mul ((hB.sub (hasDerivAt_id t)).sin))).congr_deriv ?_
  simp only [Pi.sub_apply, id_eq]

/-- **(A').**  `τ'\sin(β-θ) + b·Δ = τ\cos(β-θ)`, with `Δ = τ\cos(β-θ) - x_1\cos β`.
At the endpoint `Δ` vanishes and this alone pins `τ'`. -/
theorem ftClusterEqOne (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ftTauDeriv a r (n - 1) θ * Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
        + ftClusterAngleDeriv a r (n - 1) x₁ θ
          * (ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
            - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
      = ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ) := by
  have hb : ∀ t ∈ Ioo (0:ℝ) (π / r), FTBranchAt a r (n - 1) t := fun _ ht =>
    ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hzero : HasDerivAt (fun u => x₁ * Real.sin (ftAngle x₁ (ftTau a r (n - 1) u) u)
      - ftTau a r (n - 1) u * Real.sin (ftAngle x₁ (ftTau a r (n - 1) u) u - u)) 0 θ := by
    refine (hasDerivAt_const θ (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    have h := ftAngle_spec (a := x₁) (ftTau_pos (hb t ht)).ne' (ftArc_subset hr ht)
    linarith [h]
  have hexp := hasDerivAt_clusterRel (x := x₁) (hasDerivAt_ftTau hn ha hr hθ hb)
    (hasDerivAt_ftClusterAngle hn ha hr hnr hx₁ hθ)
  have hu := hexp.unique hzero
  linear_combination -hu

/-- **(B'').**  (B) differentiated: the same matrix, acting on `(τ'', β'')`. -/
theorem ftBranchEqTwo (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) :
    ftTauDeriv2 a r (n - 1) θ * ftFarSumTau a r (n - 1) x₁ θ
        + (ρ : ℝ) * ftClusterAngleDeriv2 a r (n - 1) x₁ θ
      = -(ftFarSumTauDeriv a r (n - 1) x₁ θ * ftTauDeriv a r (n - 1) θ
          + ftFarSumAngleDeriv a r (n - 1) x₁ θ) := by
  have hb : ∀ t ∈ Ioo (0:ℝ) (π / r), FTBranchAt a r (n - 1) t := fun _ ht =>
    ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hzero : HasDerivAt (fun t => (ρ : ℝ) * ftClusterAngleDeriv a r (n - 1) x₁ t
      + ftFarSumTau a r (n - 1) x₁ t * ftTauDeriv a r (n - 1) t
      + ftFarSumAngle a r (n - 1) x₁ t) 0 θ := by
    refine (hasDerivAt_const θ ((r : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact ftBranchSplit hn ha hr hnr hcard ht
  have hexp := (((hasDerivAt_ftClusterAngleDeriv hn ha hr hnr hx₁ hθ).const_mul (ρ : ℝ)).add
    ((hasDerivAt_ftFarSumTau (x₁ := x₁) hn ha hr hnr hθ).mul
      (hasDerivAt_ftTauDeriv hn ha hr hθ hb))).add
    (hasDerivAt_ftFarSumAngle (x₁ := x₁) hn ha hr hnr hθ)
  have hu := hexp.unique hzero
  linear_combination hu

/-- (A') differentiated once more, in general shape. -/
private theorem hasDerivAt_clusterRel2 {T Td B Bd : ℝ → ℝ} {Td' Bd' t x : ℝ}
    (hT : HasDerivAt T (Td t) t) (hTd : HasDerivAt Td Td' t)
    (hB : HasDerivAt B (Bd t) t) (hBd : HasDerivAt Bd Bd' t) :
    HasDerivAt (fun u => x * (Real.cos (B u) * Bd u)
        - (Td u * Real.sin (B u - u) + T u * (Real.cos (B u - u) * (Bd u - 1))))
      (-(Td' * Real.sin (B t - t)
          + Bd' * (T t * Real.cos (B t - t) - x * Real.cos (B t))
          + x * Real.sin (B t) * Bd t ^ 2
          + 2 * Td t * Real.cos (B t - t) * (Bd t - 1)
          - T t * Real.sin (B t - t) * (Bd t - 1) ^ 2)) t := by
  have hBt := hB.sub (hasDerivAt_id t)
  refine ((((hB.cos).mul hBd).const_mul x).sub
    ((hTd.mul (hBt.sin)).add (hT.mul ((hBt.cos).mul (hBd.sub_const 1))))).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  ring

/-- **(A'').**  `τ''\sin(β-θ) + β''·Δ = R_1`, with every term of `R_1` built from
quantities that converge at the endpoint. -/
theorem ftClusterEqTwo (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ftTauDeriv2 a r (n - 1) θ * Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
        + ftClusterAngleDeriv2 a r (n - 1) x₁ θ
          * (ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
            - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
      = -(x₁ * Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ)
            * ftClusterAngleDeriv a r (n - 1) x₁ θ ^ 2)
        - 2 * ftTauDeriv a r (n - 1) θ
            * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
            * (ftClusterAngleDeriv a r (n - 1) x₁ θ - 1)
        + ftTau a r (n - 1) θ * Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
            * (ftClusterAngleDeriv a r (n - 1) x₁ θ - 1) ^ 2 := by
  have hb : ∀ t ∈ Ioo (0:ℝ) (π / r), FTBranchAt a r (n - 1) t := fun _ ht =>
    ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hzero : HasDerivAt (fun u => x₁ * (Real.cos (ftAngle x₁ (ftTau a r (n - 1) u) u)
        * ftClusterAngleDeriv a r (n - 1) x₁ u)
      - (ftTauDeriv a r (n - 1) u * Real.sin (ftAngle x₁ (ftTau a r (n - 1) u) u - u)
        + ftTau a r (n - 1) u * (Real.cos (ftAngle x₁ (ftTau a r (n - 1) u) u - u)
          * (ftClusterAngleDeriv a r (n - 1) x₁ u - 1)))) 0 θ := by
    refine (hasDerivAt_const θ (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    linear_combination -(ftClusterEqOne hn ha hr hnr hx₁ ht)
  have hexp := hasDerivAt_clusterRel2 (x := x₁) (T := ftTau a r (n - 1))
    (Td := ftTauDeriv a r (n - 1))
    (B := fun t => ftAngle x₁ (ftTau a r (n - 1) t) t)
    (Bd := ftClusterAngleDeriv a r (n - 1) x₁)
    (hasDerivAt_ftTau hn ha hr hθ hb) (hasDerivAt_ftTauDeriv hn ha hr hθ hb)
    (hasDerivAt_ftClusterAngle hn ha hr hnr hx₁ hθ)
    (hasDerivAt_ftClusterAngleDeriv hn ha hr hnr hx₁ hθ)
  have hu := hexp.unique hzero
  linear_combination -hu

/-! ### The entries converge

Every matrix entry and every right-hand side is a far-index chart form evaluated
along `(τ(θ), θ) → (x_1, 0)`, or a cluster quantity whose limit is known.  Only
`\det M` needs a value; the rest need only to converge, which is why they are
stated existentially. -/

/-- The pair `(τ(θ), θ)` runs into `(x_1, 0)`, which is where every chart form is
evaluated. -/
private theorem tendsto_ftTauPair {T : ℝ → ℝ} (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    Tendsto (fun θ : ℝ => (T θ, θ)) (𝓝[>] (0 : ℝ)) (𝓝 (x₁, 0)) :=
  hT.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- The chord to a zero the branch circle does not reach stays off zero. -/
private theorem ftChordSq_endpoint_ne {c : ℝ} (hcx : x₁ < c) : ftChordSq c x₁ 0 ≠ 0 := by
  have h : ftChordSq c x₁ 0 = (c - x₁) ^ 2 := by rw [ftChordSq, Real.cos_zero]; ring
  rw [h]
  positivity

/-- **`∂θ_k/∂τ` converges**, at a zero the branch circle does not reach.  The
chart form is `-a\sin θ/D` (`AngleChartForm.ftAngleDerivTau_chart`), and `D` stays
off zero there, so the whole quotient is continuous at `(x_1, 0)`. -/
private theorem tendsto_ftAngleDerivTau_chart {T : ℝ → ℝ} {c : ℝ} (hcx : x₁ < c)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    Tendsto (fun θ => -(c * Real.sin θ) / ftChordSq c (T θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (-(c * Real.sin 0) / ftChordSq c x₁ 0)) := by
  have hD : ContinuousAt (fun p : ℝ × ℝ => ftChordSq c p.1 p.2) (x₁, 0) := by
    simp only [ftChordSq]; fun_prop
  have h : ContinuousAt (fun p : ℝ × ℝ => -(c * Real.sin p.2) / ftChordSq c p.1 p.2) (x₁, 0) :=
    ContinuousAt.div (by fun_prop) hD (ftChordSq_endpoint_ne hcx)
  simpa [Function.comp_def] using h.tendsto.comp (tendsto_ftTauPair hT)

/-- **`∂θ_k/∂θ` converges**, by the same argument at the chart form
`τ(τ - a\cos θ)/D` (`AngleChartForm.ftAngleDerivAngle_chart`). -/
private theorem tendsto_ftAngleDerivAngle_chart {T : ℝ → ℝ} {c : ℝ} (hcx : x₁ < c)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    Tendsto (fun θ => T θ * (T θ - c * Real.cos θ) / ftChordSq c (T θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (x₁ * (x₁ - c * Real.cos 0) / ftChordSq c x₁ 0)) := by
  have hD : ContinuousAt (fun p : ℝ × ℝ => ftChordSq c p.1 p.2) (x₁, 0) := by
    simp only [ftChordSq]; fun_prop
  have h : ContinuousAt
      (fun p : ℝ × ℝ => p.1 * (p.1 - c * Real.cos p.2) / ftChordSq c p.1 p.2) (x₁, 0) :=
    ContinuousAt.div (by fun_prop) hD (ftChordSq_endpoint_ne hcx)
  simpa [Function.comp_def] using h.tendsto.comp (tendsto_ftTauPair hT)

/-- **`∂²θ_k/∂τ²` converges**, at the chart form
`2a\sin θ(τ - a\cos θ)/D²` (`AngleChartForm.ftAngleDeriv2Tau_chart`).  `D²` in the
denominator is why the nonvanishing is raised to a power rather than reused. -/
private theorem tendsto_ftAngleDeriv2Tau_chart {T : ℝ → ℝ} {c : ℝ} (hcx : x₁ < c)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    Tendsto (fun θ => 2 * c * Real.sin θ * (T θ - c * Real.cos θ)
        / ftChordSq c (T θ) θ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * c * Real.sin 0 * (x₁ - c * Real.cos 0) / ftChordSq c x₁ 0 ^ 2)) := by
  have hD : ContinuousAt (fun p : ℝ × ℝ => ftChordSq c p.1 p.2) (x₁, 0) := by
    simp only [ftChordSq]; fun_prop
  have h : ContinuousAt (fun p : ℝ × ℝ => 2 * c * Real.sin p.2 * (p.1 - c * Real.cos p.2)
      / ftChordSq c p.1 p.2 ^ 2) (x₁, 0) :=
    ContinuousAt.div (by fun_prop) (hD.pow 2) (pow_ne_zero _ (ftChordSq_endpoint_ne hcx))
  simpa [Function.comp_def] using h.tendsto.comp (tendsto_ftTauPair hT)

/-- **Both mixed second partials converge**, and this is one lemma rather than two:
`∂²θ_k/∂τ∂θ` and `∂²θ_k/∂θ∂τ` have the *same* chart form
`-a(\cos θ·D - 2aτ\sin²θ)/D²` (`AngleChartForm.ftAngleDeriv2AngleTau_chart` and
`ftAngleDeriv2TauAngle_chart` land on it identically), so `σ'` and `A_F'` consume
the same limit — `σ'` as its second term and `A_F'` as its first. -/
private theorem tendsto_ftAngleDeriv2Mixed_chart {T : ℝ → ℝ} {c : ℝ} (hcx : x₁ < c)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    Tendsto (fun θ => -(c * (Real.cos θ * ftChordSq c (T θ) θ
          - 2 * c * T θ * Real.sin θ ^ 2)) / ftChordSq c (T θ) θ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (-(c * (Real.cos 0 * ftChordSq c x₁ 0 - 2 * c * x₁ * Real.sin 0 ^ 2))
        / ftChordSq c x₁ 0 ^ 2)) := by
  have hD : ContinuousAt (fun p : ℝ × ℝ => ftChordSq c p.1 p.2) (x₁, 0) := by
    simp only [ftChordSq]; fun_prop
  have h : ContinuousAt (fun p : ℝ × ℝ => -(c * (Real.cos p.2 * ftChordSq c p.1 p.2
      - 2 * c * p.1 * Real.sin p.2 ^ 2)) / ftChordSq c p.1 p.2 ^ 2) (x₁, 0) := by
    refine ContinuousAt.div ?_ (hD.pow 2) (pow_ne_zero _ (ftChordSq_endpoint_ne hcx))
    simp only [ftChordSq]
    fun_prop
  simpa [Function.comp_def] using h.tendsto.comp (tendsto_ftTauPair hT)

/-- **`∂²θ_k/∂θ²` converges**, at the chart form
`aτ\sin θ(D - 2τ(τ - a\cos θ))/D²` (`AngleChartForm.ftAngleDeriv2Angle_chart`). -/
private theorem tendsto_ftAngleDeriv2Angle_chart {T : ℝ → ℝ} {c : ℝ} (hcx : x₁ < c)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    Tendsto (fun θ => c * T θ * Real.sin θ
          * (ftChordSq c (T θ) θ - 2 * T θ * (T θ - c * Real.cos θ))
        / ftChordSq c (T θ) θ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (c * x₁ * Real.sin 0 * (ftChordSq c x₁ 0 - 2 * x₁ * (x₁ - c * Real.cos 0))
        / ftChordSq c x₁ 0 ^ 2)) := by
  have hD : ContinuousAt (fun p : ℝ × ℝ => ftChordSq c p.1 p.2) (x₁, 0) := by
    simp only [ftChordSq]; fun_prop
  have h : ContinuousAt (fun p : ℝ × ℝ => c * p.1 * Real.sin p.2
      * (ftChordSq c p.1 p.2 - 2 * p.1 * (p.1 - c * Real.cos p.2))
      / ftChordSq c p.1 p.2 ^ 2) (x₁, 0) := by
    refine ContinuousAt.div ?_ (hD.pow 2) (pow_ne_zero _ (ftChordSq_endpoint_ne hcx))
    simp only [ftChordSq]
    fun_prop
  simpa [Function.comp_def] using h.tendsto.comp (tendsto_ftTauPair hT)

/-- The arc, as an eventual condition at its lower endpoint. -/
private theorem eventually_arc (hr : 1 ≤ r) :
    ∀ᶠ θ in 𝓝[>] (0:ℝ), θ ∈ Ioo (0:ℝ) (π / r) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  exact Ioo_mem_nhdsGT (by positivity)

private theorem far_lt (hmin : ∀ k, x₁ ≤ a k) {k : Fin n} (hk : k ∈ ftFar a x₁) :
    x₁ < a k :=
  lt_of_le_of_ne (hmin k) (Ne.symm (Finset.mem_filter.1 hk).2)

/-- `σ` converges. -/
theorem exists_tendsto_ftFarSumTau (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hmin : ∀ k, x₁ ≤ a k)
    (hT : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    ∃ L, Tendsto (ftFarSumTau a r (n - 1) x₁) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hchart : Tendsto (fun θ => ∑ k ∈ ftFar a x₁,
      -(a k * Real.sin θ) / ftChordSq (a k) (ftTau a r (n - 1) θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ ftFar a x₁, -(a k * Real.sin 0) / ftChordSq (a k) x₁ 0)) :=
    tendsto_finsetSum _ fun k hk => tendsto_ftAngleDerivTau_chart (far_lt hmin hk) hT
  refine ⟨_, hchart.congr' ?_⟩
  filter_upwards [eventually_arc (r := r) hr] with θ hθ
  have hpos := ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hθπ := ftArc_subset hr hθ
  simp only [ftFarSumTau]
  exact Finset.sum_congr rfl fun k _ => (ftAngleDerivTau_chart (ha k) hpos hθπ).symm

/-- `A_F` converges. -/
theorem exists_tendsto_ftFarSumAngle (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hmin : ∀ k, x₁ ≤ a k)
    (hT : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 x₁)) :
    ∃ L, Tendsto (ftFarSumAngle a r (n - 1) x₁) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hchart : Tendsto (fun θ => ∑ k ∈ ftFar a x₁,
      ftTau a r (n - 1) θ * (ftTau a r (n - 1) θ - a k * Real.cos θ)
        / ftChordSq (a k) (ftTau a r (n - 1) θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ ftFar a x₁, x₁ * (x₁ - a k * Real.cos 0) / ftChordSq (a k) x₁ 0)) :=
    tendsto_finsetSum _ fun k hk => tendsto_ftAngleDerivAngle_chart (far_lt hmin hk) hT
  refine ⟨_, hchart.congr' ?_⟩
  filter_upwards [eventually_arc (r := r) hr] with θ hθ
  have hpos := ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hθπ := ftArc_subset hr hθ
  simp only [ftFarSumAngle]
  exact Finset.sum_congr rfl fun k _ => (ftAngleDerivAngle_chart (ha k) hpos hθπ).symm

/-- `σ'` converges, once `τ'` does. -/
theorem exists_tendsto_ftFarSumTauDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hmin : ∀ k, x₁ ≤ a k)
    (hT : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 x₁))
    {D : ℝ} (hD : Tendsto (ftTauDeriv a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    ∃ L, Tendsto (ftFarSumTauDeriv a r (n - 1) x₁) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hchart : Tendsto (fun θ => ∑ k ∈ ftFar a x₁,
      (2 * a k * Real.sin θ * (ftTau a r (n - 1) θ - a k * Real.cos θ)
          / ftChordSq (a k) (ftTau a r (n - 1) θ) θ ^ 2 * ftTauDeriv a r (n - 1) θ
        + -(a k * (Real.cos θ * ftChordSq (a k) (ftTau a r (n - 1) θ) θ
            - 2 * a k * ftTau a r (n - 1) θ * Real.sin θ ^ 2))
          / ftChordSq (a k) (ftTau a r (n - 1) θ) θ ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ ftFar a x₁,
        (2 * a k * Real.sin 0 * (x₁ - a k * Real.cos 0) / ftChordSq (a k) x₁ 0 ^ 2 * D
          + -(a k * (Real.cos 0 * ftChordSq (a k) x₁ 0 - 2 * a k * x₁ * Real.sin 0 ^ 2))
            / ftChordSq (a k) x₁ 0 ^ 2))) :=
    tendsto_finsetSum _ fun k hk =>
      ((tendsto_ftAngleDeriv2Tau_chart (far_lt hmin hk) hT).mul hD).add
        (tendsto_ftAngleDeriv2Mixed_chart (far_lt hmin hk) hT)
  refine ⟨_, hchart.congr' ?_⟩
  filter_upwards [eventually_arc (r := r) hr] with θ hθ
  have hpos := ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hθπ := ftArc_subset hr hθ
  simp only [ftFarSumTauDeriv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ftAngleDeriv2Tau_chart (ha k) hpos hθπ, ftAngleDeriv2TauAngle_chart (ha k) hpos hθπ]

/-- `A_F'` converges, once `τ'` does. -/
theorem exists_tendsto_ftFarSumAngleDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hmin : ∀ k, x₁ ≤ a k)
    (hT : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 x₁))
    {D : ℝ} (hD : Tendsto (ftTauDeriv a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    ∃ L, Tendsto (ftFarSumAngleDeriv a r (n - 1) x₁) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hchart : Tendsto (fun θ => ∑ k ∈ ftFar a x₁,
      (-(a k * (Real.cos θ * ftChordSq (a k) (ftTau a r (n - 1) θ) θ
            - 2 * a k * ftTau a r (n - 1) θ * Real.sin θ ^ 2))
          / ftChordSq (a k) (ftTau a r (n - 1) θ) θ ^ 2 * ftTauDeriv a r (n - 1) θ
        + a k * ftTau a r (n - 1) θ * Real.sin θ
            * (ftChordSq (a k) (ftTau a r (n - 1) θ) θ
              - 2 * ftTau a r (n - 1) θ * (ftTau a r (n - 1) θ - a k * Real.cos θ))
          / ftChordSq (a k) (ftTau a r (n - 1) θ) θ ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ ftFar a x₁,
        (-(a k * (Real.cos 0 * ftChordSq (a k) x₁ 0 - 2 * a k * x₁ * Real.sin 0 ^ 2))
            / ftChordSq (a k) x₁ 0 ^ 2 * D
          + a k * x₁ * Real.sin 0 * (ftChordSq (a k) x₁ 0 - 2 * x₁ * (x₁ - a k * Real.cos 0))
            / ftChordSq (a k) x₁ 0 ^ 2))) :=
    tendsto_finsetSum _ fun k hk =>
      ((tendsto_ftAngleDeriv2Mixed_chart (far_lt hmin hk) hT).mul hD).add
        (tendsto_ftAngleDeriv2Angle_chart (far_lt hmin hk) hT)
  refine ⟨_, hchart.congr' ?_⟩
  filter_upwards [eventually_arc (r := r) hr] with θ hθ
  have hpos := ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hθπ := ftArc_subset hr hθ
  simp only [ftFarSumAngleDeriv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ftAngleDeriv2AngleTau_chart (ha k) hpos hθπ, ftAngleDeriv2Angle_chart (ha k) hpos hθπ]

/-! ### The determinant, and Cramer -/

/-- `\det M = \sin(β-θ)·ρ - Δσ`, the determinant both orders are solved by. -/
noncomputable def ftEndpointDet {n : ℕ} (a : Fin n → ℝ) (r l ρ : ℕ) (x₁ θ : ℝ) : ℝ :=
  Real.sin (ftAngle x₁ (ftTau a r l θ) θ - θ) * ρ
    - (ftTau a r l θ * Real.cos (ftAngle x₁ (ftTau a r l θ) θ - θ)
        - x₁ * Real.cos (ftAngle x₁ (ftTau a r l θ) θ)) * ftFarSumTau a r l x₁ θ

/-- **The determinant runs to `ρ\sin(π/ρ)`**, which is off zero: `Δ → 0` because
the cluster angle and the radius reach the endpoint together. -/
theorem tendsto_ftEndpointDet (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    Tendsto (ftEndpointDet a r (n - 1) ρ x₁) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sin (Real.pi / ρ) * ρ)) := by
  have hτ := tendsto_ftTau_endpoint hn ha hr hnr hx₁ hmin hcard hρ
  obtain ⟨Lσ, hσ⟩ := exists_tendsto_ftFarSumTau hn ha hr hnr hmin hτ
  have hβ := tendsto_ftClusterAngle hn ha hr hnr hx₁ hmin hcard hρ
  have hβθ : Tendsto (fun θ => ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi - Real.pi / ρ)) := by
    simpa using hβ.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hsin : Tendsto (fun θ => Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (Real.pi / ρ))) := by
    have h := (Real.continuous_sin.continuousAt
      (x := Real.pi - Real.pi / ρ)).tendsto.comp hβθ
    rw [Real.sin_pi_sub] at h
    simpa [Function.comp_def] using h
  have hcosβθ : Tendsto (fun θ => Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos (Real.pi - Real.pi / ρ))) := by
    simpa [Function.comp_def] using (Real.continuous_cos.continuousAt
      (x := Real.pi - Real.pi / ρ)).tendsto.comp hβθ
  have hcosβ : Tendsto (fun θ => Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos (Real.pi - Real.pi / ρ))) := by
    simpa [Function.comp_def] using (Real.continuous_cos.continuousAt
      (x := Real.pi - Real.pi / ρ)).tendsto.comp hβ
  have hΔ : Tendsto (fun θ => ftTau a r (n - 1) θ
      * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
      - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hτ.mul hcosβθ).sub ((tendsto_const_nhds (x := x₁)).mul hcosβ)
  have h := (hsin.mul (tendsto_const_nhds (x := (ρ : ℝ)))).sub (hΔ.mul hσ)
  rw [zero_mul, sub_zero] at h
  exact h.congr fun θ => by rw [ftEndpointDet]

/-- The determinant's limit is off zero. -/
theorem ftEndpointDet_limit_ne (hρ : 2 ≤ ρ) : Real.sin (Real.pi / ρ) * (ρ : ℝ) ≠ 0 := by
  have hπ := Real.pi_pos
  have hρR : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have h1 : 0 < Real.pi / ρ := by positivity
  have h2 : Real.pi / ρ < Real.pi := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  exact (mul_pos (Real.sin_pos_of_pos_of_lt_pi h1 h2) (by linarith)).ne'

/-- **`τ''` converges at the endpoint**, at every admissible pencil whose smallest
zero is repeated.  This is the single analytic input
`BranchSupplyGeometry.exists_lipschitz_ftGammaDerivAt_of_tendsto_ftTauDeriv2` asks
for, and the whole general collar follows from it.

**Differs from the paper's route.**  `lem:principal-endpoint-regularity` reaches
endpoint regularity through analyticity — a Puiseux parameter, an analytic `k`-th
root, a local inverse — and a second derivative at the endpoint comes with it.
Here `τ''` is shown to converge with none of that.  The branch angle at the
repeated zero is carried alongside `τ` as a second unknown, and the two relations
the pair satisfies differentiate into a linear system whose matrix stays
invertible at the endpoint.  Nothing is expanded and nothing is inverted; what is
used is that a determinant has a nonzero limit. -/
theorem exists_tendsto_ftTauDeriv2 (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ D2, Tendsto (ftTauDeriv2 a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 D2) := by
  have hτ := tendsto_ftTau_endpoint hn ha hr hnr hx₁ hmin hcard hρ
  have hβ := tendsto_ftClusterAngle hn ha hr hnr hx₁ hmin hcard hρ
  have hdet := tendsto_ftEndpointDet hn ha hr hnr hx₁ hmin hcard hρ
  have hdne : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftEndpointDet a r (n - 1) ρ x₁ θ ≠ 0 :=
    hdet.eventually_ne (ftEndpointDet_limit_ne hρ)
  obtain ⟨Lσ, hσ⟩ := exists_tendsto_ftFarSumTau hn ha hr hnr hmin hτ
  obtain ⟨LA, hA⟩ := exists_tendsto_ftFarSumAngle hn ha hr hnr hmin hτ
  have hβθ : Tendsto (fun θ => ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi - Real.pi / ρ)) := by
    simpa using hβ.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hsin : Tendsto (fun θ => Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (Real.pi - Real.pi / ρ))) := by
    simpa [Function.comp_def] using (Real.continuous_sin.continuousAt
      (x := Real.pi - Real.pi / ρ)).tendsto.comp hβθ
  have hcosβθ : Tendsto (fun θ => Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos (Real.pi - Real.pi / ρ))) := by
    simpa [Function.comp_def] using (Real.continuous_cos.continuousAt
      (x := Real.pi - Real.pi / ρ)).tendsto.comp hβθ
  have hsinβ : Tendsto (fun θ => Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (Real.pi - Real.pi / ρ))) := by
    simpa [Function.comp_def] using (Real.continuous_sin.continuousAt
      (x := Real.pi - Real.pi / ρ)).tendsto.comp hβ
  have hcosβ : Tendsto (fun θ => Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos (Real.pi - Real.pi / ρ))) := by
    simpa [Function.comp_def] using (Real.continuous_cos.continuousAt
      (x := Real.pi - Real.pi / ρ)).tendsto.comp hβ
  have hΔ : Tendsto (fun θ => ftTau a r (n - 1) θ
      * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
      - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hτ.mul hcosβθ).sub ((tendsto_const_nhds (x := x₁)).mul hcosβ)
  -- first order, by Cramer
  have hcram1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftTauDeriv a r (n - 1) θ
      = ((ρ : ℝ) * (ftTau a r (n - 1) θ
            * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ))
          - (ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
              - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
            * ((r : ℝ) - ftFarSumAngle a r (n - 1) x₁ θ))
        / ftEndpointDet a r (n - 1) ρ x₁ θ := by
    filter_upwards [eventually_arc (r := r) hr, hdne] with θ hθ hd
    rw [eq_div_iff hd, ftEndpointDet]
    linear_combination (ρ : ℝ) * ftClusterEqOne hn ha hr hnr hx₁ hθ
      - (ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
          - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
        * ftBranchSplit hn ha hr hnr hcard hθ
  have htau1 := (((((tendsto_const_nhds (x := (ρ : ℝ))).mul (hτ.mul hcosβθ)).sub
    (hΔ.mul ((tendsto_const_nhds (x := (r : ℝ))).sub hA))).div hdet
      (ftEndpointDet_limit_ne hρ)).congr' (hcram1.mono fun _ h => h.symm))
  -- the cluster angle's derivative, by the same system
  have hcram2 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftClusterAngleDeriv a r (n - 1) x₁ θ
      = (Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
            * ((r : ℝ) - ftFarSumAngle a r (n - 1) x₁ θ)
          - ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
            * ftFarSumTau a r (n - 1) x₁ θ)
        / ftEndpointDet a r (n - 1) ρ x₁ θ := by
    filter_upwards [eventually_arc (r := r) hr, hdne] with θ hθ hd
    rw [eq_div_iff hd, ftEndpointDet]
    linear_combination Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
        * ftBranchSplit hn ha hr hnr hcard hθ
      - ftFarSumTau a r (n - 1) x₁ θ * ftClusterEqOne hn ha hr hnr hx₁ hθ
  have hb := ((((hsin.mul ((tendsto_const_nhds (x := (r : ℝ))).sub hA)).sub
    ((hτ.mul hcosβθ).mul hσ)).div hdet (ftEndpointDet_limit_ne hρ)).congr'
      (hcram2.mono fun _ h => h.symm))
  -- second order, same matrix
  obtain ⟨Lσ', hσ'⟩ := exists_tendsto_ftFarSumTauDeriv hn ha hr hnr hmin hτ htau1
  obtain ⟨LA', hA'⟩ := exists_tendsto_ftFarSumAngleDeriv hn ha hr hnr hmin hτ htau1
  have hR1 := ((((tendsto_const_nhds (x := x₁)).mul hsinβ).mul (hb.pow 2)).neg.sub
    (((tendsto_const_nhds (x := (2 : ℝ))).mul htau1).mul hcosβθ
      |>.mul (hb.sub (tendsto_const_nhds (x := (1 : ℝ)))))).add
    ((hτ.mul hsin).mul ((hb.sub (tendsto_const_nhds (x := (1 : ℝ)))).pow 2))
  have hR2 := ((hσ'.mul htau1).add hA').neg
  have hcram3 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftTauDeriv2 a r (n - 1) θ
      = ((ρ : ℝ) * (-(x₁ * Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ)
              * ftClusterAngleDeriv a r (n - 1) x₁ θ ^ 2)
            - 2 * ftTauDeriv a r (n - 1) θ
              * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
              * (ftClusterAngleDeriv a r (n - 1) x₁ θ - 1)
            + ftTau a r (n - 1) θ * Real.sin (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
              * (ftClusterAngleDeriv a r (n - 1) x₁ θ - 1) ^ 2)
          - (ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
              - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
            * -(ftFarSumTauDeriv a r (n - 1) x₁ θ * ftTauDeriv a r (n - 1) θ
              + ftFarSumAngleDeriv a r (n - 1) x₁ θ))
        / ftEndpointDet a r (n - 1) ρ x₁ θ := by
    filter_upwards [eventually_arc (r := r) hr, hdne] with θ hθ hd
    rw [eq_div_iff hd, ftEndpointDet]
    linear_combination (ρ : ℝ) * ftClusterEqTwo hn ha hr hnr hx₁ hθ
      - (ftTau a r (n - 1) θ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ - θ)
          - x₁ * Real.cos (ftAngle x₁ (ftTau a r (n - 1) θ) θ))
        * ftBranchEqTwo hn ha hr hnr hx₁ hcard hθ
  exact ⟨_, ((((tendsto_const_nhds (x := (ρ : ℝ))).mul hR1).sub (hΔ.mul hR2)).div hdet
    (ftEndpointDet_limit_ne hρ)).congr' (hcram3.mono fun _ h => h.symm)⟩

/-- **The general collar's Lipschitz input, with nothing assumed.**
`BranchSupplyGeometry.exists_lipschitz_ftGammaDerivAt_of_tendsto_ftTauDeriv2` carries
the `τ''` limit as a hypothesis; at a repeated smallest zero it is now discharged. -/
theorem exists_lipschitz_ftGammaDerivAt_of_repeated_min (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (v : ℂ) (L b : ℝ), 0 < b ∧ 0 ≤ L ∧
      ∀ θ ∈ Icc (0 : ℝ) b,
        ‖ftGammaDerivAt a r (n - 1) v θ - ftGammaDerivAt a r (n - 1) v 0‖ ≤ L * θ := by
  obtain ⟨D2, hD2⟩ := exists_tendsto_ftTauDeriv2 hn ha hr hnr hx₁ hmin hcard hρ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  exact exists_lipschitz_ftGammaDerivAt_of_tendsto_ftTauDeriv2 hn ha hr (by positivity)
    (fun _ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ) hD2

/-- **The hypotheses are satisfiable**, at the paper's own witness cubic
`Q = (1 - t)^3` with `r = 1`, where the smallest zero carries multiplicity `3`.
`../../scripts/check_endpoint_tau2_limit.py` measures the limit there as `7/9`;
nothing is claimed about it here, and in particular nothing is claimed about
`ftTauDeriv2 ![1, 1, 1] 1 2 0`, which is junk from a vanishing denominator. -/
theorem exists_tendsto_ftTauDeriv2_witness :
    ∃ D2, Tendsto (ftTauDeriv2 ![1, 1, 1] 1 2) (𝓝[>] (0 : ℝ)) (𝓝 D2) := by
  have hcard : (Finset.univ.filter fun k => (![1, 1, 1] : Fin 3 → ℝ) k = 1).card = 3 := by
    rw [Finset.filter_true_of_mem fun k _ => by fin_cases k <;> norm_num]
    simp
  exact exists_tendsto_ftTauDeriv2 (n := 3) (r := 1) (ρ := 3) (x₁ := 1)
    (by norm_num) (fun k => by fin_cases k <;> norm_num) le_rfl (Or.inl (by norm_num))
    (by norm_num) (fun k => by fin_cases k <;> norm_num) hcard (by norm_num)

end ForgacsTran
