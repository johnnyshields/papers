/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.AttractorPole

/-!
# The contour-separated expansion at a cluster of simple poles

`ClusterContour` carries the invariance half of `lem:contour-separation` and
`ContourRemainder` the decay half for a contour enclosing **two** poles.  This
module carries the algebraic half for an arbitrary finite cluster of simple
poles, which is what the endpoint analysis of `subsec:weighted-dominance` needs:
there the retained contour holds the whole `ρ`-root lower cluster or the whole
`r`-root upper one, not just the principal pair.

## Main statements

* `poleProd`, `poleCofactor`, `poleProd_mul_cofactor` — the retained poles
  divided out, by monic division; the cluster members are distinct because they
  are a `Finset`.
* `eval_derivative_of_poleProd` — `D'(a)` factors through the cofactor, which is
  what identifies the residue at `a` with `B(a)/D'(a)`.
* `poleRes`, `poleNum`, `poleRem`, `div_eq_poleSum_add_rem` — **partial fractions
  over the cluster**, done by polynomial division rather than through removable
  singularities: `B - S·\mathrm{num}` vanishes at every retained pole, so the
  remainder is a quotient of polynomials with no retained pole left.
* `taylorCoeff_add`, `taylorCoeff_const_mul`, `taylorCoeff_finsetSum` — the
  coefficient calculus the extraction runs on.
* `taylorCoeff_div_poleExpansion` — `[t^M]B/D` is the sum of the retained residue
  contributions `-A_a a^{-M-1}` plus the coefficient of the analytic remainder.
* `poleCofactor_ne_zero`, `exists_poleRem_bound`,
  `norm_smul_taylorCoeff_poleRem_le` — the remainder is analytic and bounded on
  the separating disk, so its normalized coefficient is `O((τ/R)^M)`.
* `exists_cluster_expansion` — **`eq:contour-separated-expansion` for the pencil**:
  `τ^{M+1}F_M(z)` is the sum of the retained `W_aζ_a^{-M-1}`,
  `ζ_a = a/τ`, plus a remainder of size `τ C(τ/R)^M`, one `C`
  serving every `M`.
* `taylorCoeff_poleRem_eq_contour`, `norm_smul_taylorCoeff_poleRem_le_of_div`,
  `cluster_expansion_of_div_bound` — **the same expansion with the paper's own
  constant**.  The retained residues integrate to zero against `t^{-M-1}` over the
  circle, so the remainder's coefficient *is* `(2π i)^{-1}∮ B t^{-M-1}/D`
  and the estimate can be stated against `C_Γ = sup_Γ|B/D|`.  That
  constant is attached to the circle and the pencil rather than to the retained
  set, which is what lets one constant serve a parameter window across a
  collision — where no bound on `poleRem`/`poleCofactor` exists, because the
  retained `Finset` loses a member there and both jump.
* `ftContourRem`, `ftContourRemDeriv`, `ftContourRem_expand`,
  `hasDerivAt_ftContourRem`, `norm_ftContourRemDeriv_le`,
  `norm_smul_ftContourRemDeriv_le` — **`eq:C1-interior-remainder`'s derivative
  half**.  The parameter enters the pencil `D_w = Q + wX^r` linearly, so
  `D_{w+h}^{-1} = D_w^{-1} - hX^rD_w^{-2} + h^2X^{2r}D_{w+h}^{-1}D_w^{-2}` is an
  identity with an exact quadratic tail; integrating it over a circle on which
  the pencil stays bounded away from zero gives differentiability in the
  parameter, the derivative, and its bound in one step — no differentiation
  under the integral sign — where the paper reaches the same bound through
  holomorphy of `E_M` in `z` and Cauchy's estimate on a fixed disk.  The size is
  the point: differentiating in `w` touches only `D`, never the `t^{-M-1}`, so the
  derivative carries the same `R^{-M}` as the value and **no factor of `M`
  appears**.

## Implementation notes

Nothing here is assumed.  No `sorry`, and no hypothesis about which of the
retained zeros is principal.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Contour-separated
residues» (`sec:geometry`, `subsec:contour-residues`, `lem:contour-separation`,
`eq:contour-separated-expansion`, `eq:contour-remainder-bound`).

## Tags

pole expansion, contour separation, simple poles, residue
-/

namespace ForgacsTran

open Polynomial Metric Shields

/-! ### The displayed poles and the cofactor -/

/-- Paper `lem:contour-separation` — the product of the retained poles. -/
noncomputable def poleProd (s : Finset ℂ) : ℂ[X] := ∏ a ∈ s, (X - C a)

/-- Paper `lem:contour-separation` — the denominator with the retained poles
divided out. -/
noncomputable def poleCofactor (D : ℂ[X]) (s : Finset ℂ) : ℂ[X] := D /ₘ poleProd s

theorem poleProd_monic (s : Finset ℂ) : (poleProd s).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a

@[simp] theorem eval_poleProd (s : Finset ℂ) (t : ℂ) :
    (poleProd s).eval t = ∏ a ∈ s, (t - a) := by
  simp [poleProd, Polynomial.eval_prod]

theorem poleProd_dvd {D : ℂ[X]} {s : Finset ℂ} (hroot : ∀ a ∈ s, D.eval a = 0) :
    poleProd s ∣ D := by
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a ha b hb hab
    exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))
  · intro a ha
    exact dvd_iff_isRoot.mpr (hroot a ha)

theorem poleProd_mul_cofactor {D : ℂ[X]} {s : Finset ℂ} (hroot : ∀ a ∈ s, D.eval a = 0) :
    poleProd s * poleCofactor D s = D := by
  have hmod : D %ₘ poleProd s = 0 :=
    (modByMonic_eq_zero_iff_dvd (poleProd_monic s)).mpr (poleProd_dvd hroot)
  have h := modByMonic_add_div D (poleProd s)
  rw [hmod, zero_add] at h
  exact h

/-- The derivative of `D` at a displayed pole factors through the cofactor and
the other displayed poles.  This is what identifies the residue at `a` with
`B(a)/D'(a)`. -/
theorem eval_derivative_of_poleProd {D : ℂ[X]} {s : Finset ℂ} {a : ℂ} (ha : a ∈ s)
    (hroot : ∀ b ∈ s, D.eval b = 0) :
    (derivative D).eval a
      = (poleCofactor D s).eval a * ∏ b ∈ s.erase a, (a - b) := by
  have hsplit : poleProd s = (X - C a) * poleProd (s.erase a) := by
    rw [poleProd, poleProd, ← Finset.mul_prod_erase s _ ha]
  have hD : D = (X - C a) * (poleProd (s.erase a) * poleCofactor D s) := by
    conv_lhs => rw [← poleProd_mul_cofactor hroot]
    rw [hsplit]; ring
  conv_lhs => rw [hD]
  simp
  ring

/-! ### Partial fractions over the retained cluster -/

/-- Paper `eq:residue-amplitude` — the residue of `B/D` at a simple pole,
`B(a)/D'(a)`.  The paper's amplitude `𝒲` is its negative. -/
noncomputable def poleRes (B D : ℂ[X]) (a : ℂ) : ℂ := B.eval a / (derivative D).eval a

/-- The numerator of the partial-fraction sum over the retained poles. -/
noncomputable def poleNum (B D : ℂ[X]) (s : Finset ℂ) : ℂ[X] :=
  ∑ a ∈ s, C (poleRes B D a) * poleProd (s.erase a)

theorem eval_poleNum_of_mem {B D : ℂ[X]} {s : Finset ℂ} {a : ℂ} (ha : a ∈ s) :
    (poleNum B D s).eval a = poleRes B D a * ∏ b ∈ s.erase a, (a - b) := by
  classical
  have hkey : ∑ b ∈ s, (C (poleRes B D b) * poleProd (s.erase b)).eval a
      = (C (poleRes B D a) * poleProd (s.erase a)).eval a := by
    refine Finset.sum_eq_single_of_mem a ha ?_
    intro b hb hba
    have hmem : a ∈ s.erase b := Finset.mem_erase.mpr ⟨fun h => hba h.symm, ha⟩
    simp only [eval_mul, eval_C, eval_poleProd]
    rw [Finset.prod_eq_zero hmem (by ring), mul_zero]
  rw [poleNum, eval_finsetSum s (fun b => C (poleRes B D b) * poleProd (s.erase b)) a, hkey]
  simp

/-- The remainder numerator vanishes at every retained pole: that is what makes
the partial-fraction remainder a polynomial. -/
theorem isRoot_sub_cofactor_mul_poleNum {B D : ℂ[X]} {s : Finset ℂ}
    (hroot : ∀ b ∈ s, D.eval b = 0) (hsimple : ∀ b ∈ s, (derivative D).eval b ≠ 0)
    {a : ℂ} (ha : a ∈ s) :
    (B - poleCofactor D s * poleNum B D s).IsRoot a := by
  have hd := eval_derivative_of_poleProd ha hroot
  simp only [IsRoot, eval_sub, eval_mul, eval_poleNum_of_mem ha]
  rw [show (poleCofactor D s).eval a * (poleRes B D a * ∏ b ∈ s.erase a, (a - b))
      = poleRes B D a * ((poleCofactor D s).eval a * ∏ b ∈ s.erase a, (a - b)) by ring,
    ← hd, poleRes, div_mul_cancel₀ _ (hsimple a ha), sub_self]

/-- Paper `lem:contour-separation` — the analytic remainder numerator. -/
noncomputable def poleRem (B D : ℂ[X]) (s : Finset ℂ) : ℂ[X] :=
  (B - poleCofactor D s * poleNum B D s) /ₘ poleProd s

theorem poleProd_mul_poleRem {B D : ℂ[X]} {s : Finset ℂ}
    (hroot : ∀ b ∈ s, D.eval b = 0) (hsimple : ∀ b ∈ s, (derivative D).eval b ≠ 0) :
    poleProd s * poleRem B D s = B - poleCofactor D s * poleNum B D s := by
  have hdvd : poleProd s ∣ (B - poleCofactor D s * poleNum B D s) :=
    poleProd_dvd fun a ha => isRoot_sub_cofactor_mul_poleNum hroot hsimple ha
  have hmod : (B - poleCofactor D s * poleNum B D s) %ₘ poleProd s = 0 :=
    (modByMonic_eq_zero_iff_dvd (poleProd_monic s)).mpr hdvd
  have h := modByMonic_add_div (B - poleCofactor D s * poleNum B D s) (poleProd s)
  rw [hmod, zero_add] at h
  exact h

theorem eval_poleNum_div {B D : ℂ[X]} {s : Finset ℂ} {t : ℂ} (ht : ∀ a ∈ s, t ≠ a) :
    (poleNum B D s).eval t / (poleProd s).eval t
      = ∑ a ∈ s, poleRes B D a * (t - a)⁻¹ := by
  classical
  rw [poleNum, eval_finsetSum s (fun b => C (poleRes B D b) * poleProd (s.erase b)) t,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hsplit : ∏ b ∈ s, (t - b) = (t - a) * ∏ b ∈ s.erase a, (t - b) :=
    (Finset.mul_prod_erase s (fun b => t - b) ha).symm
  have hta : t - a ≠ 0 := sub_ne_zero.mpr (ht a ha)
  have hprod : ∏ b ∈ s.erase a, (t - b) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun b hb => ?_
    exact sub_ne_zero.mpr (ht b (Finset.mem_of_mem_erase hb))
  simp only [eval_mul, eval_C, eval_poleProd, hsplit]
  field_simp

/-- **Paper `lem:contour-separation`, `eq:contour-separated-expansion` — partial
fractions over the retained cluster.**  Off the poles and where the cofactor does
not vanish, `B/D` is the sum of the simple-pole terms at the retained poles plus
a remainder that is a quotient of polynomials with no retained pole left.

**Differs from the paper's route.**  `lem:contour-separation` is stated as a
contour integral, its remainder estimated by the length of the contour and the
sup of `B/D` on it.  Here the decomposition is partial fractions by polynomial
division — `B - S·num` vanishes at every retained pole, so the remainder is a
quotient of polynomials — and its coefficient is bounded by Cauchy's estimate on
the separating circle. -/
theorem div_eq_poleSum_add_rem {B D : ℂ[X]} {s : Finset ℂ}
    (hroot : ∀ b ∈ s, D.eval b = 0) (hsimple : ∀ b ∈ s, (derivative D).eval b ≠ 0)
    {t : ℂ} (ht : ∀ a ∈ s, t ≠ a) (hS : (poleCofactor D s).eval t ≠ 0) :
    B.eval t / D.eval t
      = (∑ a ∈ s, poleRes B D a * (t - a)⁻¹)
        + (poleRem B D s).eval t / (poleCofactor D s).eval t := by
  classical
  have hP : (poleProd s).eval t ≠ 0 := by
    rw [eval_poleProd]
    exact Finset.prod_ne_zero_iff.mpr fun a ha => sub_ne_zero.mpr (ht a ha)
  have hD : D.eval t = (poleProd s).eval t * (poleCofactor D s).eval t := by
    conv_lhs => rw [← poleProd_mul_cofactor hroot]
    simp
  have hrem := congrArg (Polynomial.eval t) (poleProd_mul_poleRem (B := B) hroot hsimple)
  simp only [eval_mul, eval_sub] at hrem
  rw [← eval_poleNum_div ht, hD, div_add_div _ _ hP hS, div_eq_div_iff (by exact mul_ne_zero hP hS)
    (by exact mul_ne_zero hP hS)]
  linear_combination (-((poleProd s).eval t * (poleCofactor D s).eval t)) * hrem

/-! ### Taylor coefficients of a finite sum -/

theorem taylorCoeff_add {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (m : ℕ) :
    taylorCoeff (fun t => F t + G t) m = taylorCoeff F m + taylorCoeff G m := by
  rw [taylorCoeff, iteratedDeriv_fun_add hF.contDiffAt hG.contDiffAt, mul_add, ← taylorCoeff,
    ← taylorCoeff]

theorem taylorCoeff_const_mul (c : ℂ) (F : ℂ → ℂ) (m : ℕ) :
    taylorCoeff (fun t => c * F t) m = c * taylorCoeff F m := by
  rw [taylorCoeff, iteratedDeriv_const_mul_field, taylorCoeff]
  ring

theorem taylorCoeff_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, AnalyticAt ℂ (F i) 0) (m : ℕ) :
    taylorCoeff (fun t => ∑ i ∈ s, F i t) m = ∑ i ∈ s, taylorCoeff (F i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [taylorCoeff]
  | insert a t hat ih =>
    have hFa : AnalyticAt ℂ (F a) 0 := hF a (Finset.mem_insert_self a t)
    have hFt : ∀ i ∈ t, AnalyticAt ℂ (F i) 0 :=
      fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hsum : AnalyticAt ℂ (fun w => ∑ i ∈ t, F i w) 0 := by
      have h := Finset.analyticAt_sum t fun i hi => hFt i hi
      have heq : (∑ n ∈ t, F n) = fun w => ∑ i ∈ t, F i w := by
        funext w; simp [Finset.sum_apply]
      rwa [heq] at h
    have hcongr : (fun w => ∑ i ∈ insert a t, F i w) = fun w => F a w + ∑ i ∈ t, F i w := by
      funext w; rw [Finset.sum_insert hat]
    rw [hcongr, taylorCoeff_add hFa hsum, ih hFt, Finset.sum_insert hat]

/-! ### The coefficient extraction -/

/-- The cofactor is zero-free on any disk whose only denominator zeros are the
retained ones. -/
theorem poleCofactor_ne_zero {D : ℂ[X]} {s : Finset ℂ} {R : ℝ}
    (hroot : ∀ a ∈ s, D.eval a = 0) (hsimple : ∀ a ∈ s, (derivative D).eval a ≠ 0)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R → D.eval t = 0 → t ∈ s) :
    ∀ t ∈ closedBall (0 : ℂ) R, (poleCofactor D s).eval t ≠ 0 := by
  intro t ht hzero
  have htR : ‖t‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using ht
  have hD : D.eval t = 0 := by
    conv_lhs => rw [← poleProd_mul_cofactor hroot]
    simp [hzero]
  have hts : t ∈ s := huniq t htR hD
  have hd := eval_derivative_of_poleProd hts hroot
  rw [hzero, zero_mul] at hd
  exact hsimple t hts hd

/-- **Paper `lem:contour-separation`, `eq:contour-separated-expansion` — the
coefficient extraction.**  `[t^M]B/D` is the sum of the retained residue
contributions `-A_a a^{-M-1}` plus the coefficient of the analytic remainder. -/
theorem taylorCoeff_div_poleExpansion {B D : ℂ[X]} {s : Finset ℂ}
    (hroot : ∀ a ∈ s, D.eval a = 0) (hsimple : ∀ a ∈ s, (derivative D).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (hS0 : (poleCofactor D s).eval 0 ≠ 0) (M : ℕ) :
    taylorCoeff (fun t => B.eval t / D.eval t) M
      = (∑ a ∈ s, -(poleRes B D a) * (a ^ (M + 1))⁻¹)
        + taylorCoeff
            (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M := by
  classical
  set E : ℂ → ℂ := fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t with hE
  set Fs : ℂ → ℂ := fun t => ∑ a ∈ s, poleRes B D a * (t - a)⁻¹ with hFs
  have hEan : AnalyticAt ℂ E 0 :=
    (analyticAt_eval _ 0).div (analyticAt_eval _ 0) hS0
  have hterm : ∀ a ∈ s, AnalyticAt ℂ (fun t : ℂ => poleRes B D a * (t - a)⁻¹) 0 := by
    intro a ha
    have hsub : (0 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (fun h => ha0 a ha h.symm)
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv hsub)
  have hFsan : AnalyticAt ℂ Fs 0 := by
    have h := Finset.analyticAt_sum s hterm
    have heq : (∑ n ∈ s, fun t : ℂ => poleRes B D n * (t - n)⁻¹) = Fs := by
      funext w; simp [hFs, Finset.sum_apply]
    rwa [heq] at h
  have hgerm : (fun t => B.eval t / D.eval t) =ᶠ[nhds 0] fun t => Fs t + E t := by
    have h1 : ∀ᶠ t in nhds (0 : ℂ), ∀ a ∈ s, t ≠ a := by
      rw [Filter.eventually_all_finset s]
      intro a ha
      exact (continuousAt_id (x := (0 : ℂ))).eventually_ne (fun h => ha0 a ha h.symm)
    have h2 : ∀ᶠ t in nhds (0 : ℂ), (poleCofactor D s).eval t ≠ 0 :=
      (analyticAt_eval (poleCofactor D s) 0).continuousAt.eventually_ne hS0
    filter_upwards [h1, h2] with t ht hSt
    exact div_eq_poleSum_add_rem hroot hsimple ht hSt
  rw [taylorCoeff_congr hgerm M, taylorCoeff_add hFsan hEan, hFs,
    taylorCoeff_finsetSum s (fun a t => poleRes B D a * (t - a)⁻¹) hterm M]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [taylorCoeff_const_mul, taylorCoeff_inv_sub (ha0 a ha)]
  ring

/-! ### The remainder is `O(σ^M)` -/

/-- The analytic remainder is bounded on the separating circle, by compactness. -/
theorem exists_poleRem_bound {B D : ℂ[X]} {s : Finset ℂ} {R : ℝ}
    (hS : ∀ t ∈ closedBall (0 : ℂ) R, (poleCofactor D s).eval t ≠ 0) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ sphere (0 : ℂ) R,
      ‖(poleRem B D s).eval t / (poleCofactor D s).eval t‖ ≤ C := by
  have hcont : ContinuousOn
      (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) (sphere (0 : ℂ) R) :=
    (continuous_eval _).continuousOn.div (continuous_eval _).continuousOn
      fun t ht => hS t (sphere_subset_closedBall ht)
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn (isCompact_sphere (0 : ℂ) R) hcont
  exact ⟨max C 0, le_max_right _ _, fun t ht => le_trans (hC t ht) (le_max_left _ _)⟩

/-- **Paper `eq:contour-remainder-bound`.**  Normalized by `τ^{M+1}` with
`τ ≤ R`, the analytic remainder's coefficient is `O((τ/R)^M)`. -/
theorem norm_smul_taylorCoeff_poleRem_le {B D : ℂ[X]} {s : Finset ℂ} {R C τ : ℝ}
    (hR : 0 < R) (hτ : 0 ≤ τ)
    (hS : ∀ t ∈ closedBall (0 : ℂ) R, (poleCofactor D s).eval t ≠ 0)
    (hC : ∀ t ∈ sphere (0 : ℂ) R,
      ‖(poleRem B D s).eval t / (poleCofactor D s).eval t‖ ≤ C) (M : ℕ) :
    ‖((τ : ℂ)) ^ (M + 1)
        * taylorCoeff (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M‖
      ≤ τ * C * (τ / R) ^ M := by
  have hEan : AnalyticOnNhd ℂ
      (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) (closedBall (0 : ℂ) R) :=
    AnalyticOnNhd.div (analyticOnNhd_eval _ _) (analyticOnNhd_eval _ _) hS
  have hEdcc : DiffContOnCl ℂ
      (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) (ball (0 : ℂ) R) := by
    refine ⟨(hEan.mono ball_subset_closedBall).differentiableOn, ?_⟩
    rw [closure_ball (0 : ℂ) hR.ne']
    exact hEan.continuousOn
  have hbound := norm_taylorCoeff_le hR hEdcc hC M
  have hRM : (0 : ℝ) < R ^ M := pow_pos hR M
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
  calc τ ^ (M + 1)
        * ‖taylorCoeff (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M‖
      ≤ τ ^ (M + 1) * (C / R ^ M) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = τ * C * (τ / R) ^ M := by rw [div_pow, pow_succ]; field_simp

/-! ### `eq:contour-separated-expansion` for the pencil -/

/-- **`eq:contour-separated-expansion` with the contour constant supplied.**  The
primitive form: `C` is a bound on the analytic remainder over the separating
circle, a statement about `B`, the denominator and the retained cluster alone.
Taking it as an input rather than producing it is what lets a *single* `C` serve
a whole parameter window, which is what `thm:weighted-dominance` needs. -/
theorem cluster_expansion_of_bound {Q B : ℂ[X]} {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {z : ℂ} {s : Finset ℂ} {R τ C : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    (hroot : ∀ a ∈ s, (ftDen Q r z).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r z)).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R → (ftDen Q r z).eval t = 0 → t ∈ s)
    (hCbd : ∀ t ∈ sphere (0 : ℂ) R,
      ‖(poleRem B (ftDen Q r z) s).eval t / (poleCofactor (ftDen Q r z) s).eval t‖ ≤ C) :
    ∀ M : ℕ,
      ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval z
          - ∑ a ∈ s, ftAmp Q B r z a * ((((a : ℂ) / (τ : ℂ))) ^ (M + 1))⁻¹‖
        ≤ τ * C * (τ / R) ^ M := by
  classical
  set D : ℂ[X] := ftDen Q r z with hD
  have hS := poleCofactor_ne_zero (D := D) (s := s) hroot hsimple huniq
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) R := by simp [hR.le]
  have hS0 := hS 0 h0mem
  intro M
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have hcoeff := taylorCoeff_div_poleExpansion (B := B) (D := D) hroot hsimple ha0 hS0 M
  rw [taylorCoeff_div_ftDen Q B hr hQ0 z M] at hcoeff
  have hterm : ∀ a ∈ s,
      ((τ : ℂ)) ^ (M + 1) * (-(poleRes B D a) * (a ^ (M + 1))⁻¹)
        = ftAmp Q B r z a * ((((a : ℂ) / (τ : ℂ))) ^ (M + 1))⁻¹ := by
    intro a ha
    have hane : (a : ℂ) ≠ 0 := ha0 a ha
    rw [ftAmp_eq_derivative (hroot a ha), poleRes, div_pow, ← hD]
    field_simp
  have hsplit : ((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval z
      - ∑ a ∈ s, ftAmp Q B r z a * ((((a : ℂ) / (τ : ℂ))) ^ (M + 1))⁻¹
      = ((τ : ℂ)) ^ (M + 1)
        * taylorCoeff (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M := by
    rw [hcoeff, mul_add, Finset.mul_sum, Finset.sum_congr rfl hterm]
    ring
  rw [hsplit]
  exact norm_smul_taylorCoeff_poleRem_le hR hτ.le hS hCbd M

/-- **Paper `lem:contour-separation`, `eq:contour-separated-expansion`.**  The
contour constant produced by compactness of the separating circle. -/
theorem exists_cluster_expansion {Q B : ℂ[X]} {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {z : ℂ} {s : Finset ℂ} {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    (hroot : ∀ a ∈ s, (ftDen Q r z).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r z)).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R → (ftDen Q r z).eval t = 0 → t ∈ s) :
    ∃ C ≥ (0 : ℝ), ∀ M : ℕ,
      ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval z
          - ∑ a ∈ s, ftAmp Q B r z a * ((((a : ℂ) / (τ : ℂ))) ^ (M + 1))⁻¹‖
        ≤ τ * C * (τ / R) ^ M := by
  obtain ⟨C, hC0, hCbd⟩ :=
    exists_poleRem_bound (B := B) (D := ftDen Q r z) (s := s)
      (poleCofactor_ne_zero hroot hsimple huniq)
  exact ⟨C, hC0, cluster_expansion_of_bound hr hQ0 hR hτ hroot hsimple ha0 huniq hCbd⟩



/-! ### The contour form of the remainder coefficient

`norm_smul_taylorCoeff_poleRem_le` states the estimate against a bound on the
analytic remainder itself.  Over a parameter window that is the wrong constant to
ask for: the retained set is indexed by the parameter and loses a member wherever
two zeros collide, so `poleRem` and `poleCofactor` jump there and no bound on them
survives a collision — while the grouped quantity does, which is the content of
`lem:contour-separation`.  `B/D` does not jump: the zeros collide inside the
circle and the circle is fixed.  What follows identifies the remainder's
coefficient with the paper's own contour integral, so the estimate can be stated
against `sup_Γ|B/D|` instead. -/

private theorem sphere_ne_zero' {R : ℝ} (hR : 0 < R) {t : ℂ}
    (ht : t ∈ sphere (0 : ℂ) R) : t ≠ 0 := by
  have hn : ‖t‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
  intro h
  rw [h, norm_zero] at hn
  exact hR.ne hn

private theorem sphere_sub_ne_zero' {R : ℝ} {a t : ℂ} (ha : ‖a‖ < R)
    (ht : t ∈ sphere (0 : ℂ) R) : t - a ≠ 0 := by
  have hn : ‖t‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
  intro h
  rw [sub_eq_zero] at h
  rw [h] at hn
  exact absurd hn ha.ne

private theorem circleIntegrable_inv_pow {R : ℝ} (hR : 0 < R) (k : ℕ) :
    CircleIntegrable (fun t : ℂ => (t ^ k)⁻¹) 0 R :=
  ContinuousOn.circleIntegrable hR.le
    (((continuous_id.pow k).continuousOn).inv₀ fun _t ht =>
      pow_ne_zero k (sphere_ne_zero' hR ht))

private theorem circleIntegrable_pole_weight {R : ℝ} (hR : 0 < R) {a : ℂ} (ha : ‖a‖ < R)
    (k : ℕ) : CircleIntegrable (fun t : ℂ => (t - a)⁻¹ * (t ^ k)⁻¹) 0 R :=
  ContinuousOn.circleIntegrable hR.le
    ((((continuous_id.sub continuous_const).continuousOn).inv₀ fun _t ht =>
        sphere_sub_ne_zero' ha ht).mul
      (((continuous_id.pow k).continuousOn).inv₀ fun _t ht =>
        pow_ne_zero k (sphere_ne_zero' hR ht)))

/-- On a circle about the origin only the `t^{-1}` weight has a nonzero integral. -/
private theorem circleIntegral_inv_pow_eq_zero {R : ℝ} (hR : 0 < R) {k : ℕ} (hk : k ≠ 1) :
    (∮ t in C(0, R), ((t : ℂ) ^ k)⁻¹) = 0 := by
  have hcong : (∮ t in C(0, R), ((t : ℂ) ^ k)⁻¹)
      = ∮ t in C(0, R), (t - 0) ^ (-(k : ℤ)) := by
    refine circleIntegral.integral_congr hR.le fun t _ => ?_
    rw [sub_zero, zpow_neg, zpow_natCast]
  have hne : (-(k : ℤ)) ≠ -1 := by
    intro h
    exact hk (by omega)
  rw [hcong, circleIntegral.integral_sub_zpow_of_ne hne 0 0 R]

/-- The recurrence that drives the retained weights to zero:
`(t-a)^{-1}t^{-k-1} = a^{-1}\bigl((t-a)^{-1}t^{-k} - t^{-k-1}\bigr)`. -/
private theorem circleIntegral_pole_weight_rec {R : ℝ} (hR : 0 < R) {a : ℂ}
    (ha : ‖a‖ < R) (ha0 : a ≠ 0) (k : ℕ) :
    (∮ t in C(0, R), (t - a)⁻¹ * (t ^ (k + 1))⁻¹)
      = a⁻¹ * ((∮ t in C(0, R), (t - a)⁻¹ * (t ^ k)⁻¹)
          - ∮ t in C(0, R), ((t : ℂ) ^ (k + 1))⁻¹) := by
  rw [← circleIntegral.integral_sub (circleIntegrable_pole_weight hR ha k)
      (circleIntegrable_inv_pow hR (k + 1)),
    ← circleIntegral.integral_const_mul]
  refine circleIntegral.integral_congr hR.le fun t ht => ?_
  have ht0 : t ≠ 0 := sphere_ne_zero' hR ht
  have hta : t - a ≠ 0 := sphere_sub_ne_zero' ha ht
  have hpk : (t : ℂ) ^ k ≠ 0 := pow_ne_zero k ht0
  field

/-- **The retained residues are invisible to the contour.**  For a pole strictly
inside the circle, `∮ t^{-M-1}(t-a)^{-1}\,dt = 0`: the residue at `a` and the
residue at the origin cancel. -/
private theorem circleIntegral_pole_weight_eq_zero {R : ℝ} (hR : 0 < R) {a : ℂ}
    (ha : ‖a‖ < R) (ha0 : a ≠ 0) (k : ℕ) :
    (∮ t in C(0, R), (t - a)⁻¹ * (t ^ (k + 1))⁻¹) = 0 := by
  have hball : a ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_zero_right] using ha
  induction k with
  | zero =>
      rw [circleIntegral_pole_weight_rec hR ha ha0 0]
      have h0 : (∮ t in C(0, R), (t - a)⁻¹ * ((t : ℂ) ^ 0)⁻¹)
          = ∮ t in C(0, R), (t - a)⁻¹ :=
        circleIntegral.integral_congr hR.le fun t _ => by rw [pow_zero, inv_one, mul_one]
      have h1 : (∮ t in C(0, R), ((t : ℂ) ^ 1)⁻¹) = ∮ t in C(0, R), (t - (0 : ℂ))⁻¹ :=
        circleIntegral.integral_congr hR.le fun t _ => by rw [pow_one, sub_zero]
      rw [h0, h1, circleIntegral.integral_sub_inv_of_mem_ball hball,
        circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hR), sub_self, mul_zero]
  | succ k ih =>
      rw [circleIntegral_pole_weight_rec hR ha ha0 (k + 1), ih,
        circleIntegral_inv_pow_eq_zero hR (k := k + 2) (by omega), sub_zero, mul_zero]

/-- **Paper `lem:contour-separation`, read in the direction that fixes the
constant.**  The analytic remainder's `M`-th coefficient *is* the contour
integral `(2π i)^{-1}∮_{|t|=R}B(t)t^{-M-1}/D(t)\,dt` of
`eq:contour-separated-expansion`: the retained residues contribute nothing to it.

**Differs from the paper's route.**  The paper writes the expansion in this
direction from the start, defining `E_M` by the contour integral and reading the
residues off it.  Here the expansion is built algebraically, by partial fractions
over the retained cluster, and the contour form is recovered afterwards — which
is what supplies a constant that does not move with the retained set. -/
theorem taylorCoeff_poleRem_eq_contour {B D : ℂ[X]} {s : Finset ℂ} {R : ℝ} (hR : 0 < R)
    (hroot : ∀ a ∈ s, D.eval a = 0) (hsimple : ∀ a ∈ s, (derivative D).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R)
    (hS : ∀ t ∈ closedBall (0 : ℂ) R, (poleCofactor D s).eval t ≠ 0) (M : ℕ) :
    taylorCoeff (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹
          * ∮ t in C(0, R), B.eval t / (t ^ (M + 1) * D.eval t) := by
  classical
  set G : ℂ → ℂ := fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t with hG
  have hGan : AnalyticOnNhd ℂ G (closedBall (0 : ℂ) R) :=
    AnalyticOnNhd.div (analyticOnNhd_eval _ _) (analyticOnNhd_eval _ _) hS
  have hGdiff : DifferentiableOn ℂ G (closedBall (0 : ℂ) R) := hGan.differentiableOn
  -- the Cauchy form of the coefficient
  have hcauchy := taylorCoeff_eq_circleIntegral (F := G) hR hGdiff M
  -- the two integrands agree on the circle up to the retained weights
  have hpoint : ∀ t ∈ sphere (0 : ℂ) R,
      B.eval t / (t ^ (M + 1) * D.eval t)
        = (∑ a ∈ s, poleRes B D a * ((t - a)⁻¹ * (t ^ (M + 1))⁻¹))
          + G t * (t ^ (M + 1))⁻¹ := by
    intro t ht
    have hts : ∀ a ∈ s, t ≠ a := by
      intro a haS h
      exact absurd (h ▸ (mem_sphere_iff_norm.1 ht)) (by simpa [sub_zero] using (haR a haS).ne)
    have hSt : (poleCofactor D s).eval t ≠ 0 :=
      hS t (sphere_subset_closedBall ht)
    have hbase := div_eq_poleSum_add_rem (B := B) hroot hsimple hts hSt
    have hlhs : B.eval t / (t ^ (M + 1) * D.eval t)
        = (B.eval t / D.eval t) * (t ^ (M + 1))⁻¹ := by
      rw [div_mul_eq_div_div_swap, div_eq_mul_inv]
    rw [hlhs, hbase, add_mul, Finset.sum_mul]
    simp only [mul_assoc, hG]
  -- integrability of the two pieces
  have hGint : CircleIntegrable (fun t : ℂ => G t * (t ^ (M + 1))⁻¹) 0 R := by
    refine ContinuousOn.circleIntegrable hR.le (ContinuousOn.mul ?_ ?_)
    · exact (hGan.continuousOn).mono sphere_subset_closedBall
    · exact ((continuous_id.pow (M + 1)).continuousOn).inv₀ fun t ht =>
        pow_ne_zero _ (sphere_ne_zero' hR ht)
  have hsint : ∀ a ∈ s,
      CircleIntegrable (fun t : ℂ => poleRes B D a * ((t - a)⁻¹ * (t ^ (M + 1))⁻¹)) 0 R :=
    fun a haS =>
      CircleIntegrable.const_fun_smul (a := poleRes B D a)
        (circleIntegrable_pole_weight hR (haR a haS) (M + 1))
  have hsumint : CircleIntegrable
      (fun t : ℂ => ∑ a ∈ s, poleRes B D a * ((t - a)⁻¹ * (t ^ (M + 1))⁻¹)) 0 R :=
    CircleIntegrable.fun_sum s hsint
  -- the retained weights integrate to zero
  have hzero : ∀ a ∈ s,
      (∮ t in C(0, R), poleRes B D a * ((t - a)⁻¹ * (t ^ (M + 1))⁻¹)) = 0 := by
    intro a haS
    rw [circleIntegral.integral_const_mul,
      circleIntegral_pole_weight_eq_zero hR (haR a haS) (ha0 a haS) M, mul_zero]
  have hmain : (∮ t in C(0, R), B.eval t / (t ^ (M + 1) * D.eval t))
      = ∮ t in C(0, R), G t * (t ^ (M + 1))⁻¹ := by
    rw [circleIntegral.integral_congr hR.le hpoint,
      circleIntegral.integral_add hsumint hGint,
      circleIntegral.integral_fun_sum hsint, Finset.sum_congr rfl hzero]
    simp
  have hweight : (∮ t in C(0, R), G t * (t : ℂ) ^ (-(M : ℤ) - 1))
      = ∮ t in C(0, R), G t * (t ^ (M + 1))⁻¹ := by
    refine circleIntegral.integral_congr hR.le fun t ht => ?_
    rw [show (-(M : ℤ) - 1) = -((M + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [hmain, ← hweight, hcauchy]

/-- **`eq:contour-remainder-bound` with the paper's own constant.**  The same
estimate as `norm_smul_taylorCoeff_poleRem_le`, but stated against
`C_Γ = sup_Γ|B/D|` — a quantity attached to the circle and the pencil
rather than to the retained set, hence one that a whole parameter window can
share. -/
theorem norm_smul_taylorCoeff_poleRem_le_of_div {B D : ℂ[X]} {s : Finset ℂ} {R C τ : ℝ}
    (hR : 0 < R) (hτ : 0 ≤ τ)
    (hroot : ∀ a ∈ s, D.eval a = 0) (hsimple : ∀ a ∈ s, (derivative D).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R)
    (hS : ∀ t ∈ closedBall (0 : ℂ) R, (poleCofactor D s).eval t ≠ 0)
    (hC : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t / D.eval t‖ ≤ C) (M : ℕ) :
    ‖((τ : ℂ)) ^ (M + 1)
        * taylorCoeff (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M‖
      ≤ τ * C * (τ / R) ^ M := by
  have hRM1 : (0 : ℝ) < R ^ (M + 1) := pow_pos hR (M + 1)
  have hbd : ∀ t ∈ sphere (0 : ℂ) R,
      ‖B.eval t / (t ^ (M + 1) * D.eval t)‖ ≤ C / R ^ (M + 1) := by
    intro t ht
    have hnt : ‖t‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
    have hsplit : B.eval t / (t ^ (M + 1) * D.eval t)
        = B.eval t / D.eval t / t ^ (M + 1) := by rw [div_div, mul_comm]
    rw [hsplit, norm_div, norm_pow, hnt]
    exact div_le_div_of_nonneg_right (hC t ht) hRM1.le
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hR.le hbd
  have hpre : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos Real.pi_pos]
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcoeff : ‖taylorCoeff
      (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M‖ ≤ C / R ^ M := by
    rw [taylorCoeff_poleRem_eq_contour hR hroot hsimple ha0 haR hS M, norm_mul, hpre]
    calc 1 / (2 * Real.pi) * ‖∮ t in C(0, R), B.eval t / (t ^ (M + 1) * D.eval t)‖
        ≤ 1 / (2 * Real.pi) * (2 * Real.pi * R * (C / R ^ (M + 1))) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = C / R ^ M := by rw [pow_succ]; field_simp
  have hRM : (0 : ℝ) < R ^ M := pow_pos hR M
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
  calc τ ^ (M + 1)
        * ‖taylorCoeff (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M‖
      ≤ τ ^ (M + 1) * (C / R ^ M) := mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = τ * C * (τ / R) ^ M := by rw [div_pow, pow_succ]; field_simp

/-- **`eq:contour-separated-expansion` with the contour constant.**  The form of
`cluster_expansion_of_bound` whose `C` is `sup_Γ|B/D|`, so one constant
serves every parameter value whose retained zeros stay strictly inside the
circle — including the parameter values at which two of them collide. -/
theorem cluster_expansion_of_div_bound {Q B : ℂ[X]} {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {z : ℂ} {s : Finset ℂ} {R τ C : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    (hroot : ∀ a ∈ s, (ftDen Q r z).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r z)).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R)
    (huniq : ∀ t : ℂ, ‖t‖ ≤ R → (ftDen Q r z).eval t = 0 → t ∈ s)
    (hCbd : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t / (ftDen Q r z).eval t‖ ≤ C) :
    ∀ M : ℕ,
      ‖((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval z
          - ∑ a ∈ s, ftAmp Q B r z a * ((((a : ℂ) / (τ : ℂ))) ^ (M + 1))⁻¹‖
        ≤ τ * C * (τ / R) ^ M := by
  classical
  set D : ℂ[X] := ftDen Q r z with hD
  have hS := poleCofactor_ne_zero (D := D) (s := s) hroot hsimple huniq
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) R := by simp [hR.le]
  have hS0 := hS 0 h0mem
  intro M
  have hτ0 : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ.ne'
  have hcoeff := taylorCoeff_div_poleExpansion (B := B) (D := D) hroot hsimple ha0 hS0 M
  rw [taylorCoeff_div_ftDen Q B hr hQ0 z M] at hcoeff
  have hterm : ∀ a ∈ s,
      ((τ : ℂ)) ^ (M + 1) * (-(poleRes B D a) * (a ^ (M + 1))⁻¹)
        = ftAmp Q B r z a * ((((a : ℂ) / (τ : ℂ))) ^ (M + 1))⁻¹ := by
    intro a ha
    have hane : (a : ℂ) ≠ 0 := ha0 a ha
    rw [ftAmp_eq_derivative (hroot a ha), poleRes, div_pow, ← hD]
    field_simp
  have hsplit : ((τ : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval z
      - ∑ a ∈ s, ftAmp Q B r z a * ((((a : ℂ) / (τ : ℂ))) ^ (M + 1))⁻¹
      = ((τ : ℂ)) ^ (M + 1)
        * taylorCoeff (fun t => (poleRem B D s).eval t / (poleCofactor D s).eval t) M := by
    rw [hcoeff, mul_add, Finset.mul_sum, Finset.sum_congr rfl hterm]
    ring
  rw [hsplit]
  exact norm_smul_taylorCoeff_poleRem_le_of_div hR hτ.le hroot hsimple ha0 haR hS hCbd M


/-! ### The contour remainder in the spectral parameter

`eq:C1-interior-remainder` needs the `θ`-derivative of the normalized
remainder, and `lem:contour-separation` is differentiated nowhere in the paper.
`taylorCoeff_poleRem_eq_contour` makes that derivative reachable without
differentiating under the integral at all: the parameter enters the pencil
`D_w = Q + wX^r` **linearly**, so

`D_{w+h}^{-1} = D_w^{-1} - hX^rD_w^{-2} + h^2X^{2r}D_{w+h}^{-1}D_w^{-2}`

is an identity between rational functions, exact with a quadratic tail.
Integrating it term by term over a circle on which every denominator is bounded
away from zero gives the derivative and its bound in one step, and the tail is
`O(h^2)` — which *is* differentiability.

The point of the exercise is the size: the parameter derivative carries the same
`R^{-M}` as the value, because differentiating in `w` touches only `D`, never the
`t^{-M-1}`.  No factor of `M` appears. -/

/-- The contour form of the analytic remainder's coefficient, as a function of
the spectral parameter. -/
noncomputable def ftContourRem (Q B : ℂ[X]) (r : ℕ) (R : ℝ) (M : ℕ) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹
    * ∮ t in C(0, R), B.eval t / (t ^ (M + 1) * (ftDen Q r w).eval t)

/-- Its parameter derivative, `-\,(2π i)^{-1}∮ Bt^{r-M-1}D_w^{-2}`. -/
noncomputable def ftContourRemDeriv (Q B : ℂ[X]) (r : ℕ) (R : ℝ) (M : ℕ) (w : ℂ) : ℂ :=
  -((2 * (Real.pi : ℂ) * Complex.I)⁻¹
      * ∮ t in C(0, R), B.eval t * t ^ r / (t ^ (M + 1) * (ftDen Q r w).eval t ^ 2))

/-- The same identity on the integrand of `eq:contour-separated-expansion`. -/
private theorem ftContour_integrand_expand {Q B : ℂ[X]} {r M : ℕ} {w h t : ℂ}
    (ht : t ≠ 0) (h0 : (ftDen Q r w).eval t ≠ 0) (h1 : (ftDen Q r (w + h)).eval t ≠ 0) :
    B.eval t / (t ^ (M + 1) * (ftDen Q r (w + h)).eval t)
      = B.eval t / (t ^ (M + 1) * (ftDen Q r w).eval t)
        - h * (B.eval t * t ^ r / (t ^ (M + 1) * (ftDen Q r w).eval t ^ 2))
        + h ^ 2 * (B.eval t * t ^ (2 * r)
            / (t ^ (M + 1) * ((ftDen Q r (w + h)).eval t * (ftDen Q r w).eval t ^ 2))) := by
  have htp : (t : ℂ) ^ (M + 1) ≠ 0 := pow_ne_zero _ ht
  have hexp : (ftDen Q r (w + h)).eval t = (ftDen Q r w).eval t + h * t ^ r := by
    simp only [ftDen_eval]; ring
  rw [hexp] at h1 ⊢
  field

private theorem continuousOn_quot {R : ℝ} {N Dn : ℂ → ℂ}
    (hN : Continuous N) (hDc : Continuous Dn)
    (hD : ∀ t ∈ sphere (0 : ℂ) R, Dn t ≠ 0) :
    ContinuousOn (fun t => N t / Dn t) (sphere (0 : ℂ) R) :=
  hN.continuousOn.div hDc.continuousOn hD

/-- **The expansion, integrated.**  Term by term over the circle, with the tail
kept exact.  Every denominator is continuous and zero-free there, so the three
pieces are separately circle-integrable and the sum splits. -/
theorem ftContourRem_expand {Q B : ℂ[X]} {r M : ℕ} {w h : ℂ} {R : ℝ} (hR : 0 < R)
    (h0 : ∀ t ∈ sphere (0 : ℂ) R, (ftDen Q r w).eval t ≠ 0)
    (h1 : ∀ t ∈ sphere (0 : ℂ) R, (ftDen Q r (w + h)).eval t ≠ 0) :
    ftContourRem Q B r R M (w + h)
      = ftContourRem Q B r R M w + h * ftContourRemDeriv Q B r R M w
        + h ^ 2 * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹
            * ∮ t in C(0, R), B.eval t * t ^ (2 * r)
                / (t ^ (M + 1) * ((ftDen Q r (w + h)).eval t
                    * (ftDen Q r w).eval t ^ 2))) := by
  have htne : ∀ t ∈ sphere (0 : ℂ) R, t ≠ 0 := fun t ht => sphere_ne_zero' hR ht
  have hpow : ∀ t ∈ sphere (0 : ℂ) R, (t : ℂ) ^ (M + 1) ≠ 0 :=
    fun t ht => pow_ne_zero _ (htne t ht)
  have hcA : ContinuousOn (fun t : ℂ => B.eval t / (t ^ (M + 1) * (ftDen Q r w).eval t))
      (sphere (0 : ℂ) R) :=
    continuousOn_quot (continuous_eval B)
      ((continuous_id.pow _).mul (continuous_eval _))
      fun t ht => mul_ne_zero (hpow t ht) (h0 t ht)
  have hcX : ContinuousOn
      (fun t : ℂ => B.eval t * t ^ r / (t ^ (M + 1) * (ftDen Q r w).eval t ^ 2))
      (sphere (0 : ℂ) R) :=
    continuousOn_quot ((continuous_eval B).mul (continuous_id.pow _))
      ((continuous_id.pow _).mul ((continuous_eval _).pow 2))
      fun t ht => mul_ne_zero (hpow t ht) (pow_ne_zero _ (h0 t ht))
  have hcY : ContinuousOn
      (fun t : ℂ => B.eval t * t ^ (2 * r)
        / (t ^ (M + 1) * ((ftDen Q r (w + h)).eval t * (ftDen Q r w).eval t ^ 2)))
      (sphere (0 : ℂ) R) :=
    continuousOn_quot ((continuous_eval B).mul (continuous_id.pow _))
      ((continuous_id.pow _).mul ((continuous_eval _).mul ((continuous_eval _).pow 2)))
      fun t ht => mul_ne_zero (hpow t ht)
        (mul_ne_zero (h1 t ht) (pow_ne_zero _ (h0 t ht)))
  have hintA : CircleIntegrable
      (fun t : ℂ => B.eval t / (t ^ (M + 1) * (ftDen Q r w).eval t)) 0 R :=
    ContinuousOn.circleIntegrable hR.le hcA
  have hinthX : CircleIntegrable
      (fun t : ℂ => -h * (B.eval t * t ^ r / (t ^ (M + 1) * (ftDen Q r w).eval t ^ 2))) 0 R :=
    ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul hcX)
  have hinthY : CircleIntegrable
      (fun t : ℂ => h ^ 2 * (B.eval t * t ^ (2 * r)
        / (t ^ (M + 1) * ((ftDen Q r (w + h)).eval t * (ftDen Q r w).eval t ^ 2)))) 0 R :=
    ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul hcY)
  have hintsum : CircleIntegrable
      (fun t : ℂ => B.eval t / (t ^ (M + 1) * (ftDen Q r w).eval t)
        + -h * (B.eval t * t ^ r / (t ^ (M + 1) * (ftDen Q r w).eval t ^ 2))) 0 R :=
    ContinuousOn.circleIntegrable hR.le (hcA.add (continuousOn_const.mul hcX))
  have hcong : (∮ t in C(0, R), B.eval t / (t ^ (M + 1) * (ftDen Q r (w + h)).eval t))
      = ∮ t in C(0, R),
          ((B.eval t / (t ^ (M + 1) * (ftDen Q r w).eval t)
            + -h * (B.eval t * t ^ r / (t ^ (M + 1) * (ftDen Q r w).eval t ^ 2)))
            + h ^ 2 * (B.eval t * t ^ (2 * r)
                / (t ^ (M + 1) * ((ftDen Q r (w + h)).eval t
                    * (ftDen Q r w).eval t ^ 2)))) := by
    refine circleIntegral.integral_congr hR.le fun t ht => ?_
    have := ftContour_integrand_expand (B := B) (M := M) (htne t ht) (h0 t ht) (h1 t ht)
    rw [this]; ring
  rw [ftContourRem, ftContourRemDeriv, ftContourRem, hcong,
    circleIntegral.integral_add hintsum hinthY,
    circleIntegral.integral_add hintA hinthX,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul]
  ring

/-- `L_Γ C_Γ/(2π) = RC` for the circle of radius `R`. -/
private theorem norm_contour_factor_le {R C : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : ∀ t ∈ sphere (0 : ℂ) R, ‖f t‖ ≤ C) :
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ t in C(0, R), f t‖ ≤ R * C := by
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hR.le hf
  have hpre : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos Real.pi_pos]
  rw [norm_mul, hpre]
  calc 1 / (2 * Real.pi) * ‖∮ t in C(0, R), f t‖
      ≤ 1 / (2 * Real.pi) * (2 * Real.pi * R * C) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = R * C := by field_simp

/-- **The parameter derivative carries the same `R^{-M}` as the value.**
Differentiating in `w` touches only the pencil, never the `t^{-M-1}`, so the
bound is `C_Γ R^r/(m^2R^M)` — the `C^0` bound times `R^r/m`, with **no**
factor of `M`.  That is the whole point of taking the derivative on the contour
rather than on the coefficient. -/
theorem norm_ftContourRemDeriv_le {Q B : ℂ[X]} {r M : ℕ} {w : ℂ} {R CB m : ℝ}
    (hR : 0 < R) (hm : 0 < m)
    (hCB : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t‖ ≤ CB)
    (hD : ∀ t ∈ sphere (0 : ℂ) R, m ≤ ‖(ftDen Q r w).eval t‖) :
    ‖ftContourRemDeriv Q B r R M w‖ ≤ CB * R ^ r / (m ^ 2 * R ^ M) := by
  have hbd : ∀ t ∈ sphere (0 : ℂ) R,
      ‖B.eval t * t ^ r / (t ^ (M + 1) * (ftDen Q r w).eval t ^ 2)‖
        ≤ CB * R ^ r / (R ^ (M + 1) * m ^ 2) := by
    intro t ht
    have hnt : ‖t‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
    have hDm := hD t ht
    have hDpos : (0 : ℝ) < ‖(ftDen Q r w).eval t‖ := lt_of_lt_of_le hm hDm
    have hsq : m ^ 2 ≤ ‖(ftDen Q r w).eval t‖ ^ 2 := by nlinarith
    have hBt : ‖B.eval t‖ ≤ CB := hCB t ht
    have hCB0 : (0 : ℝ) ≤ CB := le_trans (norm_nonneg _) hBt
    have hnum : ‖B.eval t‖ * R ^ r ≤ CB * R ^ r :=
      mul_le_mul_of_nonneg_right hBt (by positivity)
    have hden : R ^ (M + 1) * m ^ 2 ≤ R ^ (M + 1) * ‖(ftDen Q r w).eval t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hnt]
    calc ‖B.eval t‖ * R ^ r / (R ^ (M + 1) * ‖(ftDen Q r w).eval t‖ ^ 2)
        ≤ CB * R ^ r / (R ^ (M + 1) * ‖(ftDen Q r w).eval t‖ ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ CB * R ^ r / (R ^ (M + 1) * m ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_left hden (by positivity)
  have heq : R * (CB * R ^ r / (R ^ (M + 1) * m ^ 2)) = CB * R ^ r / (m ^ 2 * R ^ M) := by
    rw [pow_succ]
    field_simp
  rw [ftContourRemDeriv, norm_neg, ← heq]
  exact norm_contour_factor_le hR hbd

/-- The tail of the expansion, bounded.  One more power of `R^r/m` than the
derivative, and still no `M`. -/
private theorem norm_ftContourRem_tail_le {Q B : ℂ[X]} {r M : ℕ} {w h : ℂ} {R CB m : ℝ}
    (hR : 0 < R) (hm : 0 < m)
    (hCB : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t‖ ≤ CB)
    (h0 : ∀ t ∈ sphere (0 : ℂ) R, m ≤ ‖(ftDen Q r w).eval t‖)
    (h1 : ∀ t ∈ sphere (0 : ℂ) R, m ≤ ‖(ftDen Q r (w + h)).eval t‖) :
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹
        * ∮ t in C(0, R), B.eval t * t ^ (2 * r)
            / (t ^ (M + 1) * ((ftDen Q r (w + h)).eval t
                * (ftDen Q r w).eval t ^ 2))‖
      ≤ CB * R ^ (2 * r) / (m ^ 3 * R ^ M) := by
  have hbd : ∀ t ∈ sphere (0 : ℂ) R,
      ‖B.eval t * t ^ (2 * r)
          / (t ^ (M + 1) * ((ftDen Q r (w + h)).eval t * (ftDen Q r w).eval t ^ 2))‖
        ≤ CB * R ^ (2 * r) / (R ^ (M + 1) * (m * m ^ 2)) := by
    intro t ht
    have hnt : ‖t‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
    have hD0 := h0 t ht
    have hD1 := h1 t ht
    have hBt : ‖B.eval t‖ ≤ CB := hCB t ht
    have hCB0 : (0 : ℝ) ≤ CB := le_trans (norm_nonneg _) hBt
    have hsq : m ^ 2 ≤ ‖(ftDen Q r w).eval t‖ ^ 2 := by nlinarith
    have hprod : m * m ^ 2 ≤ ‖(ftDen Q r (w + h)).eval t‖ * ‖(ftDen Q r w).eval t‖ ^ 2 :=
      mul_le_mul hD1 hsq (by positivity) (le_trans hm.le hD1)
    have hden : R ^ (M + 1) * (m * m ^ 2)
        ≤ R ^ (M + 1) * (‖(ftDen Q r (w + h)).eval t‖ * ‖(ftDen Q r w).eval t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    have hnum : ‖B.eval t‖ * R ^ (2 * r) ≤ CB * R ^ (2 * r) :=
      mul_le_mul_of_nonneg_right hBt (by positivity)
    have hpos : (0 : ℝ) < ‖(ftDen Q r (w + h)).eval t‖ * ‖(ftDen Q r w).eval t‖ ^ 2 :=
      lt_of_lt_of_le (by positivity) hprod
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hnt]
    calc ‖B.eval t‖ * R ^ (2 * r)
          / (R ^ (M + 1) * (‖(ftDen Q r (w + h)).eval t‖ * ‖(ftDen Q r w).eval t‖ ^ 2))
        ≤ CB * R ^ (2 * r)
          / (R ^ (M + 1) * (‖(ftDen Q r (w + h)).eval t‖ * ‖(ftDen Q r w).eval t‖ ^ 2)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ CB * R ^ (2 * r) / (R ^ (M + 1) * (m * m ^ 2)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_left hden (by positivity)
  have heq : R * (CB * R ^ (2 * r) / (R ^ (M + 1) * (m * m ^ 2)))
      = CB * R ^ (2 * r) / (m ^ 3 * R ^ M) := by
    rw [pow_succ]
    field_simp
  rw [← heq]
  exact norm_contour_factor_le hR hbd

/-- **The contour remainder is differentiable in the spectral parameter, with the
derivative `eq:C1-interior-remainder` needs.**  Along the real axis — which is
where the Forgács--Tran parameter `z(θ)` lives — the expansion's exact
quadratic tail *is* differentiability: no dominated convergence, no
differentiation under the integral sign, and no hypothesis beyond a circle on
which the pencil stays bounded away from zero throughout a neighborhood of the
parameter.

**Differs from the paper's route.**  The paper proves the same bound through
holomorphy: `lem:contour-separation` makes `E_M` holomorphic in `z` over a
complex neighborhood of the parameter piece, and Cauchy's estimate on a fixed
disk bounds `∂_zE_M` by the same exponential.  Here the parameter is real
and the expansion is exact, so neither holomorphy nor a disk is formed — which is
why the hypotheses are a real interval of parameters and a zero-free circle, and
nothing about a complex neighborhood. -/
theorem hasDerivAt_ftContourRem {Q B : ℂ[X]} {r M : ℕ} {R CB m ε : ℝ} {x₀ : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hε : 0 < ε)
    (hCB : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t‖ ≤ CB)
    (hDb : ∀ x : ℝ, |x - x₀| ≤ ε → ∀ t ∈ sphere (0 : ℂ) R,
      m ≤ ‖(ftDen Q r ((x : ℝ) : ℂ)).eval t‖) :
    HasDerivAt (fun x : ℝ => ftContourRem Q B r R M ((x : ℝ) : ℂ))
      (ftContourRemDeriv Q B r R M ((x₀ : ℝ) : ℂ)) x₀ := by
  obtain ⟨t₀, ht₀⟩ : (sphere (0 : ℂ) R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  have hCB0 : (0 : ℝ) ≤ CB := le_trans (norm_nonneg _) (hCB t₀ ht₀)
  have hK0 : (0 : ℝ) ≤ CB * R ^ (2 * r) / (m ^ 3 * R ^ M) := by positivity
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min ε (c / (CB * R ^ (2 * r) / (m ^ 3 * R ^ M) + 1)), by positivity, fun x hx => ?_⟩
  have hdist : |x - x₀| < min ε (c / (CB * R ^ (2 * r) / (m ^ 3 * R ^ M) + 1)) := by
    rwa [Real.dist_eq] at hx
  have hxε : |x - x₀| ≤ ε := le_of_lt (lt_of_lt_of_le hdist (min_le_left _ _))
  have hxc : |x - x₀| ≤ c / (CB * R ^ (2 * r) / (m ^ 3 * R ^ M) + 1) :=
    le_of_lt (lt_of_lt_of_le hdist (min_le_right _ _))
  have hxx : ((x : ℝ) : ℂ) = ((x₀ : ℝ) : ℂ) + ((x - x₀ : ℝ) : ℂ) := by push_cast; ring
  have hne : ∀ y : ℝ, |y - x₀| ≤ ε → ∀ t ∈ sphere (0 : ℂ) R,
      (ftDen Q r ((y : ℝ) : ℂ)).eval t ≠ 0 := by
    intro y hy t ht hz
    have := hDb y hy t ht
    rw [hz, norm_zero] at this
    linarith
  have hD0 : ∀ t ∈ sphere (0 : ℂ) R, (ftDen Q r ((x₀ : ℝ) : ℂ)).eval t ≠ 0 :=
    hne x₀ (by simpa using hε.le)
  have hD1 : ∀ t ∈ sphere (0 : ℂ) R,
      (ftDen Q r (((x₀ : ℝ) : ℂ) + ((x - x₀ : ℝ) : ℂ))).eval t ≠ 0 := by
    intro t ht
    rw [← hxx]
    exact hne x hxε t ht
  have hm1 : ∀ t ∈ sphere (0 : ℂ) R,
      m ≤ ‖(ftDen Q r (((x₀ : ℝ) : ℂ) + ((x - x₀ : ℝ) : ℂ))).eval t‖ := by
    intro t ht
    rw [← hxx]
    exact hDb x hxε t ht
  have hexp := ftContourRem_expand (Q := Q) (B := B) (M := M) hR hD0 hD1
  have htail := norm_ftContourRem_tail_le (Q := Q) (B := B) (M := M) hR hm hCB
    (hDb x₀ (by simpa using hε.le)) hm1
  have hrw : ftContourRem Q B r R M ((x : ℝ) : ℂ)
      - ftContourRem Q B r R M ((x₀ : ℝ) : ℂ)
      - (x - x₀) • ftContourRemDeriv Q B r R M ((x₀ : ℝ) : ℂ)
      = ((x - x₀ : ℝ) : ℂ) ^ 2 * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹
          * ∮ t in C(0, R), B.eval t * t ^ (2 * r)
              / (t ^ (M + 1) * ((ftDen Q r (((x₀ : ℝ) : ℂ) + ((x - x₀ : ℝ) : ℂ))).eval t
                  * (ftDen Q r ((x₀ : ℝ) : ℂ)).eval t ^ 2))) := by
    rw [hxx, hexp, Complex.real_smul]
    ring
  rw [hrw, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have habs : (0 : ℝ) ≤ |x - x₀| := abs_nonneg _
  calc |x - x₀| ^ 2 * ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹
          * ∮ t in C(0, R), B.eval t * t ^ (2 * r)
              / (t ^ (M + 1) * ((ftDen Q r (((x₀ : ℝ) : ℂ) + ((x - x₀ : ℝ) : ℂ))).eval t
                  * (ftDen Q r ((x₀ : ℝ) : ℂ)).eval t ^ 2))‖
      ≤ |x - x₀| ^ 2 * (CB * R ^ (2 * r) / (m ^ 3 * R ^ M)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ c * |x - x₀| := by
        have hstep : |x - x₀| * (CB * R ^ (2 * r) / (m ^ 3 * R ^ M)) ≤ c := by
          have h1 : |x - x₀| * (CB * R ^ (2 * r) / (m ^ 3 * R ^ M) + 1) ≤ c := by
            rw [← le_div_iff₀ (by positivity)]
            exact hxc
          nlinarith [habs, hK0]
        nlinarith [habs, hK0, hstep]

/-- `ftContourRem` is the analytic remainder's coefficient — `taylorCoeff_poleRem_eq_contour`
in the notation the derivative is taken in. -/
theorem taylorCoeff_poleRem_eq_ftContourRem {Q B : ℂ[X]} {r M : ℕ} {w : ℂ} {s : Finset ℂ}
    {R : ℝ} (hR : 0 < R)
    (hroot : ∀ a ∈ s, (ftDen Q r w).eval a = 0)
    (hsimple : ∀ a ∈ s, (derivative (ftDen Q r w)).eval a ≠ 0)
    (ha0 : ∀ a ∈ s, a ≠ 0) (haR : ∀ a ∈ s, ‖a‖ < R)
    (hS : ∀ t ∈ closedBall (0 : ℂ) R, (poleCofactor (ftDen Q r w) s).eval t ≠ 0) :
    taylorCoeff (fun t => (poleRem B (ftDen Q r w) s).eval t
        / (poleCofactor (ftDen Q r w) s).eval t) M
      = ftContourRem Q B r R M w :=
  taylorCoeff_poleRem_eq_contour hR hroot hsimple ha0 haR hS M

/-- **The chain rule to the Forgács--Tran parameter.**  `θ ↦ F_M(z(θ))`'s
remainder differentiates through `z`, so the derivative is `z'(θ)` times the
parameter derivative on the contour. -/
theorem hasDerivAt_ftContourRem_comp {Q B : ℂ[X]} {r M : ℕ} {R CB m ε : ℝ}
    {z : ℝ → ℝ} {z' θ : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hε : 0 < ε)
    (hCB : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t‖ ≤ CB)
    (hDb : ∀ x : ℝ, |x - z θ| ≤ ε → ∀ t ∈ sphere (0 : ℂ) R,
      m ≤ ‖(ftDen Q r ((x : ℝ) : ℂ)).eval t‖)
    (hz : HasDerivAt z z' θ) :
    HasDerivAt (fun s : ℝ => ftContourRem Q B r R M ((z s : ℝ) : ℂ))
      (z' • ftContourRemDeriv Q B r R M ((z θ : ℝ) : ℂ)) θ :=
  HasDerivAt.scomp θ (hasDerivAt_ftContourRem hR hm hε hCB hDb) hz

/-- **`eq:C1-interior-remainder`, the derivative half, in the shape
`Consequences.c1_interior_remainder_bound` consumes.**  Normalized by
`τ^{M+1}`, the `θ`-derivative of the remainder is `O(σ^M)` with a
constant `τ_{max}Z C_Γ R^r/m^2` in which **`M` does not appear** — which
is the whole content of the claim, since a constant carrying one more factor of
`M` would leave `norm_le_of_mul_eq` nothing to cancel.

The `(M+1)` that `eq:C1-interior-remainder` does carry comes from the
`τ^{M+1}` prefactor alone, and `Consequences.norm_deriv_scaled_remainder_le`
is where it enters. -/
theorem norm_smul_ftContourRemDeriv_le {Q B : ℂ[X]} {r M : ℕ} {w : ℂ}
    {R CB m τ τmax Z z' : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hτ : 0 ≤ τ) (hτmax : τ ≤ τmax) (hZ : |z'| ≤ Z)
    (hCB : ∀ t ∈ sphere (0 : ℂ) R, ‖B.eval t‖ ≤ CB)
    (hD : ∀ t ∈ sphere (0 : ℂ) R, m ≤ ‖(ftDen Q r w).eval t‖) :
    ‖((τ : ℝ) : ℂ) ^ (M + 1) * (z' • ftContourRemDeriv Q B r R M w)‖
      ≤ (τmax * Z * CB * R ^ r / m ^ 2) * (τ / R) ^ M := by
  obtain ⟨t₀, ht₀⟩ : (sphere (0 : ℂ) R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  have hCB0 : (0 : ℝ) ≤ CB := le_trans (norm_nonneg _) (hCB t₀ ht₀)
  have hZ0 : (0 : ℝ) ≤ Z := le_trans (abs_nonneg _) hZ
  have hbase := norm_ftContourRemDeriv_le (Q := Q) (B := B) (M := M) hR hm hCB hD
  have hRM : (0 : ℝ) < R ^ M := pow_pos hR M
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ,
    Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hstep : |z'| * ‖ftContourRemDeriv Q B r R M w‖
      ≤ Z * (CB * R ^ r / (m ^ 2 * R ^ M)) :=
    mul_le_mul hZ hbase (norm_nonneg _) hZ0
  calc τ ^ (M + 1) * (|z'| * ‖ftContourRemDeriv Q B r R M w‖)
      ≤ τ ^ (M + 1) * (Z * (CB * R ^ r / (m ^ 2 * R ^ M))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (τ * Z * CB * R ^ r / m ^ 2) * (τ / R) ^ M := by
        rw [div_pow, pow_succ]
        field_simp
    _ ≤ (τmax * Z * CB * R ^ r / m ^ 2) * (τ / R) ^ M := by
        have hcoef : τ * Z * CB * R ^ r / m ^ 2 ≤ τmax * Z * CB * R ^ r / m ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have : (0 : ℝ) ≤ Z * CB * R ^ r := by positivity
          nlinarith [pow_pos hR r]
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)

end ForgacsTran
