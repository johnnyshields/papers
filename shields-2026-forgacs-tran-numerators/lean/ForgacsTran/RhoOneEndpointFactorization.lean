/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointLowerRhoOne
import ForgacsTran.PencilArcSymmetry
import ForgacsTran.EndpointCollision
import ForgacsTran.EndpointPackage

/-!
# The lower endpoint's factorization group at `ρ = 1`

`EndpointPackage.endpoint_package_of_two_le_rho` supplies
`thm:weighted-dominance`'s lower endpoint group — `te₀`, `γe₀`, `hγ0₀`, `hγd₀`,
`hk₀` — at `2 ≤ ρ`, where the branch radius runs into the repeated smallest zero
`x₁` and the spectral parameter into `g(x₁) = 0`.

At `ρ = 1` neither value is that, and the difference is not a degeneracy of the
same formula.  The radius runs into the critical point `t_a` of `eq:ab-def`, which
lies strictly inside `(x₁, x₂)` and is **not** a zero of `Q`; the parameter runs
into `g(t_a) = -Q(t_a)/t_a^r ≠ 0`.  `EndpointLowerRhoOne` supplies the extension
that can carry that value, and this module assembles the group over it.

**Three of the `2 ≤ ρ` group's binders are not obstructions here, and one is.**
`hcB₀`, `hcQ₀`, `hBp₀`, `hEp₀` and `hρ` are all conditioned on `0 < n₀`, and
`ρ = 1` gives `n₀ = ρ - 2 = 0` in `ℕ`, so every one of them is vacuous — the
`clusterAlpha` degeneracy `SimpleEndpoint.clusterAlpha_one_eq_zero` records, and
the contradiction `SimpleEndpoint.hEp_false_of_rho_one` derives, are both about
the **unconditioned** forms and cannot be reached from a composition at `n₀ = 0`.
What does not dissolve is `hk₀`, which names `z 0` and is false against the
hardcoded `0`.

**`hγd₀` is proved, and what it rests on is one inequality about the endpoint.**
At `2 ≤ ρ` the radius approaches `x₁` linearly and
`EndpointPackage.tendsto_ftTau_blowup` supplies the nonzero slope.  At `ρ = 1` the
approach is quadratic, so the slope is `0` and `γ'(0⁺) = i·t_a` is purely
imaginary.  `PencilArcSymmetry.tendsto_slope_of_ftPencilIm_eq_zero` supplies that
vanishing from `E'(t_a) ≠ 0` alone, so
`hasDerivWithinAt_ftPrincipal_ftTauLower_of_simple_endpoint` carries no analytic
hypothesis at all — only the admissible class, `E(t_a) = 0` and `E'(t_a) ≠ 0`.

The two-step form is kept beside it.  `..._rho_one` takes the slope as a
hypothesis and is the part of the argument that has nothing to do with the pencil;
keeping them separate is what makes it visible that the pencil enters only through
that one limit.

## Main statements

* `exists_endpoint_factorization_rho_one` — `te₀`, `hte₀`, `hγ0₀` and `hk₀` at the
  `ρ = 1` lower endpoint, over `ftBranchZLowerAt` at the branch's own endpoint
  value.  The multiplicity is `2`, not merely `1`: the endpoint is a collision of
  the principal pair.
* `hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one` — `hγd₀` from the vanishing
  radial slope, with `γe₀ = i·t_a ≠ 0`.
* `hasDerivWithinAt_ftPrincipal_ftTauLower_of_simple_endpoint` — the same with the
  slope discharged, so the inputs are the admissible class and the two facts about
  the endpoint.  `E'(t_a) ≠ 0` is the whole dichotomy: it holds at `ρ = 1` and at
  `ρ = 2`, and fails from `ρ = 3`, where the approach really is linear.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:ab-def`, `eq:principal-pair`, `subsec:proof`.

## Tags

lower endpoint, rho = 1, endpoint factorization, collision, false binder
-/

namespace ForgacsTran

open Complex Filter Topology Polynomial
open scoped Topology

/-- **The `ρ = 1` lower endpoint's factorization data.**  The critical point `t_a`
is produced with the branch limit that reaches it, and `hk₀` holds over
`ftBranchZLowerAt` at that point's own spectral value.

The multiplicity is `2`.  At `2 ≤ ρ` the corresponding statement is `1 ≤`, and the
difference is the geometry: here the principal pair collides at `t_a`, which is
also why `∂_tD` vanishes there and the closed-window forms of the simplicity
binders are false.

**It carries no `ρ` hypothesis, and that is not an oversight.**  The critical
point, the limit and the multiplicity all come off the admissible class alone, so
this is the uniform statement rather than the `ρ = 1` half of a dichotomy; the
`2 ≤ ρ` group is what it becomes wherever the endpoint value is `0`, by
`EndpointLowerRhoOne.ftBranchZLower_eq_ftBranchZLowerAt`.  The dichotomy lives one
level up, in which value that is. -/
theorem exists_endpoint_factorization_rho_one {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) :
    ∃ ta : ℝ, 0 < ta
      ∧ (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0
      ∧ Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta)
      ∧ ((ta : ℝ) : ℂ) ≠ 0
      ∧ ftPrincipal (ftTauLower a r (n - 1) ta) 0 = ((ta : ℝ) : ℂ)
      ∧ 2 ≤ (ftDen (ftRootPoly c a) r
          ((ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r) 0 : ℝ) : ℂ)).rootMultiplicity
        ((ta : ℝ) : ℂ) := by
  obtain ⟨ta, hta, hlim, hE⟩ := exists_tendsto_ftTau_nhdsGT_zero_of_two_le hn2 ha hr hc
  refine ⟨ta, hta, hE, hlim, by exact_mod_cast hta.ne', ?_, ?_⟩
  · rw [ftPrincipal_ftTauLower_zero]
  · rw [ftBranchZLowerAt_zero]
    exact two_le_rootMultiplicity_ftDen_at_critical ha hc.ne' hr hta.ne' hE

/-- **`hγd₀` at `ρ = 1`, from the vanishing radial slope.**  `γ = τe^{iθ}`, so the
derivative at the endpoint is `τ'(0⁺) + i·τ(0)`; at `ρ = 1` the radius approaches
`t_a` quadratically, the first term is `0`, and what is left is purely imaginary
and nonzero.

The slope is the hypothesis.  Everything else here is the `2 ≤ ρ` argument of
`EndpointPackage.hasDerivWithinAt_ftPrincipal_ftTauLower` with its nonzero slope
replaced by `0`, which is why this is stated as a reduction: the pencil, the
admissible class and the exponent `r` do not appear, so nothing about them can be
hiding in it. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one {n r : ℕ} {a : Fin n → ℝ}
    {ta : ℝ}
    (hslope : Tendsto (fun δ : ℝ => (ftTau a r (n - 1) δ - ta) / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauLower a r (n - 1) ta) δ)
      (((ta : ℝ) : ℂ) * Complex.I) (Set.Ici 0) 0 := by
  have hrealC : Tendsto (fun δ : ℝ => (((ftTau a r (n - 1) δ - ta) / δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((0 : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.tendsto _).comp hslope
  have hexpc : Tendsto (fun δ : ℝ => Complex.exp (((δ : ℝ) : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous fun δ : ℝ => Complex.exp (((δ : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    have h : Tendsto (fun δ : ℝ => Complex.exp (((δ : ℝ) : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((((0 : ℝ)) : ℂ) * Complex.I))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  have hcomb := (hrealC.mul hexpc).add
    ((tendsto_expI_slope.mono_left hsub).const_mul ((ta : ℝ) : ℂ))
  have hval : (((0 : ℝ) : ℂ)) * 1 + ((ta : ℝ) : ℂ) * Complex.I
      = ((ta : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hval] at hcomb
  have hdiff : (Set.Ici (0 : ℝ)) \ {(0 : ℝ)} = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hx, hne⟩
      exact lt_of_le_of_ne hx (Ne.symm hne)
    · intro hx
      exact ⟨le_of_lt hx, ne_of_gt hx⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff]
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  have hδC : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ0
  simp only [slope, vsub_eq_sub, sub_zero, Complex.real_smul, Complex.ofReal_inv]
  rw [ftPrincipal_ftTauLower_zero, ftPrincipal, ftTauLower_agree a r (n - 1) ta hδ0]
  push_cast
  field_simp
  ring

/-- **`hγd₀` at the branch, with the slope discharged.**  The only inputs left are
the admissible class and the two facts about the endpoint itself: `E(t_a) = 0` and
`E'(t_a) ≠ 0`.  No analytic hypothesis is carried.

The branch equation comes from `FTBranchEndpoint.ftPencilIm_eq_zero` on the open
arc, the vanishing slope from
`PencilArcSymmetry.tendsto_slope_of_ftPencilIm_eq_zero`, and the rest is the
`2 ≤ ρ` argument with its nonzero slope replaced by `0`.

**`E'(t_a) ≠ 0` is the whole dichotomy.**  It holds at `ρ = 1`, where `t_a` is a
simple zero of `E` strictly inside `(x_1, x_2)`, and also at `ρ = 2`, where
`E'(x_1) = x_1Q''(x_1) ≠ 0`; it fails from `ρ = 3`, where the approach is genuinely
linear.  So this is not the `ρ = 1` statement — it is the statement, and `ρ` enters
only through whether its hypothesis holds. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauLower_of_simple_endpoint {n r : ℕ}
    {a : Fin n → ℝ} {c ta : ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta))
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0)
    (hE' : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval ta ≠ 0) :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauLower a r (n - 1) ta) δ)
      (((ta : ℝ) : ℂ) * Complex.I) (Set.Ici 0) 0 := by
  have hn : 0 < n := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hbπ : Real.pi / r ≤ Real.pi := by
    rw [div_le_iff₀ hrR]
    nlinarith [Real.pi_pos]
  have hzero : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      ftPencilIm (ftRootPolyReal c a) r (ftTau a r (n - 1) θ) θ = 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with θ hθ
    exact ftPencilIm_eq_zero c ha ⟨hθ.1, lt_of_lt_of_le hθ.2 hbπ⟩
      (ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ)
  exact hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one
    (tendsto_slope_of_ftPencilIm_eq_zero hzero hlim hE hE')

/-! ### The nondegeneracy, from the admissible class alone

`E'(t_a) ≠ 0` is the one hypothesis `hγd₀` still names, and it is not an extra
analytic assumption: off the zeros of `Q` it holds for **every** positive pencil,
at every `n` and every `r`, by a sign argument with no case analysis. -/

/-- **`E'` cannot vanish at a zero of `E` that is not a zero of `Q`.**  `E = -Σ·Q`,
so `E(t) = 0` away from the zeros of `Q` forces `Σ(t) = 0`; then
`E'(t) = -Σ'(t)Q(t)`, and `Σ'(t) = ∑_k a_k/(a_k - t)^2` is a sum of positive terms
and cannot vanish for a positive pencil.

There is no multiplicity anywhere in this, and no bound on `n`.  What decides the
dichotomy is entirely the hypothesis `∀ k, a_k ≠ t`: at `2 ≤ ρ` the endpoint *is*
the repeated zero and this does not apply; at `ρ = 1` it lies strictly between the
two smallest zeros and it does. -/
theorem eval_derivative_ftCriticalReal_ne_zero_of_not_root {n r : ℕ} {a : Fin n → ℝ}
    {c t : ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hne : ∀ k, a k - t ≠ 0)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval t = 0) :
    (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval t ≠ 0 := by
  classical
  have hQ : (ftRootPolyReal c a).eval t ≠ 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun k _ => hne k)
  have hSig : ftSigmaReal a r t = 0 := by
    have hfac := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := r) hne
    rw [hE] at hfac
    rcases mul_eq_zero.1 hfac.symm with h | h
    · exact neg_eq_zero.1 h
    · exact absurd h hQ
  rw [eval_derivative_ftCriticalReal_of_ftSigmaReal_eq_zero hne hSig]
  exact mul_ne_zero (neg_ne_zero.2 (ne_of_gt (sum_div_sq_pos hn ha hne))) hQ

/-- **`hγd₀` at the branch whenever the endpoint is not a zero of `Q`.**  This is
the statement the dichotomy actually turns on, and it names neither `ρ` nor a bound
on `n`: the derivative binder holds, with `γe₀ = i·t_a`, exactly when the branch
radius runs into a point that is not a zero of the pencil's numerator.

At `2 ≤ ρ` the hypothesis fails — the endpoint is the repeated zero — and the
linear approach of `EndpointPackage.hasDerivWithinAt_ftPrincipal_ftTauLower` is
what applies instead.  `ρ = 2` is the one place both are available, and they agree:
`cot(π/2) = 0`. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauLower_of_not_root {n r : ℕ} {a : Fin n → ℝ}
    {c ta : ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta))
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0)
    (hne : ∀ k, a k - ta ≠ 0) :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauLower a r (n - 1) ta) δ)
      (((ta : ℝ) : ℂ) * Complex.I) (Set.Ici 0) 0 :=
  hasDerivWithinAt_ftPrincipal_ftTauLower_of_simple_endpoint hn2 ha hr hlim hE
    (eval_derivative_ftCriticalReal_ne_zero_of_not_root (by omega) ha hc.ne' hne hE)

/-- **`hγd₀` at the `ρ = 1` lower endpoint.**  The branch radius runs into a point
strictly between the two smallest zeros, so it is no zero of `Q`, and
`hasDerivWithinAt_ftPrincipal_ftTauLower_of_not_root` applies with `γe₀ = i·t_a`.

Both halves of the bracket are derived rather than assumed — see `rho_one_hgd`
below, which supplies them.  This form takes them as hypotheses because it is the
composition step and nothing in it depends on how they were obtained. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one_of_bracket {n r : ℕ}
    {a : Fin n → ℝ} {c ta : ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta)) (hta : 0 < ta)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0)
    (hupper : ∀ k, k ≠ i → ta < a k) :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauLower a r (n - 1) ta) δ)
      (((ta : ℝ) : ℂ) * Complex.I) (Set.Ici 0) 0 := by
  have hlow : a i < ta :=
    lt_of_eval_ftCriticalReal_eq_zero hc ha hr hmin hsimple hta hE
  refine hasDerivWithinAt_ftPrincipal_ftTauLower_of_not_root hn2 ha hc hr hlim hE ?_
  intro k
  rcases eq_or_ne k i with rfl | hk
  · exact sub_ne_zero.2 (by linarith)
  · exact sub_ne_zero.2 (by linarith [hupper k hk])

/-- **`hγd₀` at the `ρ = 1` lower endpoint, from the admissible class alone.**  The
only hypothesis on the zeros is that the smallest one is simple, which is what
`ρ = 1` means.  The endpoint's location is produced, not assumed: it lies strictly
inside the first gap, so it is no zero of `Q`, and `γe₀ = i·t_a` follows.

**No hypothesis is placed on `a j` for `j ≠ i`,** so a repeated *second* zero is
covered.  That is why the bracket comes from the branch — `FTBranchGap`'s
`lt_of_tendsto_ftTau` bounds the limit below every other zero using the branch
radius itself — rather than from an intermediate-value argument on `Σ` between the
two smallest zeros, which would need the second zero to be a distinct value. -/
theorem rho_one_hgd {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) {i : Fin n}
    (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, a i < ta ∧ (∀ k, k ≠ i → ta < a k)
      ∧ Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta)
      ∧ (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0
      ∧ HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauLower a r (n - 1) ta) δ)
          (((ta : ℝ) : ℂ) * Complex.I) (Set.Ici 0) 0 := by
  obtain ⟨ta, hta0, hlim, hE⟩ := exists_tendsto_ftTau_nhdsGT_zero_of_two_le hn2 ha hr hc
  have hlow : a i < ta := lt_of_eval_ftCriticalReal_eq_zero hc ha hr hmin hsimple hta0 hE
  have hupper : ∀ k, k ≠ i → ta < a k := fun k hk =>
    lt_of_tendsto_ftTau hn2 ha hr (Ne.symm hk) hlim hlow
  exact ⟨ta, hlow, hupper, hlim, hE,
    hasDerivWithinAt_ftPrincipal_ftTauLower_rho_one_of_bracket hn2 ha hc hr hmin hsimple
      hlim hta0 hE hupper⟩

/-! ### The retained lower set at `ρ = 1`

`n₀ = ρ - 2 = 0`: the principal pair is the whole retained cluster, exactly as
`n₁ = 0` at the `r = 1` upper endpoint.  What the group consumes is a separating
radius, and what produces one is the strict inequality `t_a < ‖w‖` for every root
of the endpoint pencil other than the collision — no constant, and no rate.

The separation is the hypothesis here.  `LowerSeparationNormalized` reduces it to a
statement with no pencil in it, and that statement is not yet proved; taking it as
a binder is what lets the rest of the block be checked against the consumer
meanwhile, which is the only way to find out whether it is the right shape. -/

/-- **The retained lower set at `ρ = 1`, from a separating radius.**  The pair
`{t_+, t_-}` is exactly the zero set of the branch pencil in the closed disk of
radius `R₀`, and both members are simple.

The window is punctured and must stay so: the pair collides at `t_a`, where the
limiting pencil has a double root, so `∂_tD(t_+)` vanishes in the limit and the
closed-window form of the simplicity clause is false.  Same geometry as the upper
endpoint at `r = 1`, at the other end of the arc. -/
theorem eventually_lower_retained_rho_one {n r : ℕ} {a : Fin n → ℝ} {c ta R₀ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hta : 0 < ta) (hne : ∀ k, a k - ta ≠ 0)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta))
    (hR : ta < R₀)
    (hsep : ∀ w : ℂ, (ftDen (ftRootPoly c a) r
        ((-((ftRootPolyReal c a).eval ta) / ta ^ r : ℝ) : ℂ)).eval w = 0 →
      w ≠ ((ta : ℝ) : ℂ) → R₀ < ‖w‖) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 < ftTauArc a r (n - 1) ta δ ∧
      ftTauArc a r (n - 1) ta δ ≤ (ta + R₀) / 2 ∧
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a r (n - 1) ta) δ) = 0 ∧
      ftPrincipal (ftTauArc a r (n - 1) ta) δ ≠
        ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I) ∧
      (∀ w ∈ ({ftPrincipal (ftTauArc a r (n - 1) ta) δ,
          ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)}
            : Finset ℂ),
        (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval w = 0 ∧
          ‖w‖ < R₀ ∧
          (derivative (ftDen (ftRootPoly c a) r
            ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ))).eval w ≠ 0) ∧
      (∀ t : ℂ, ‖t‖ ≤ R₀ →
        (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval t = 0 →
        t ∈ ({ftPrincipal (ftTauArc a r (n - 1) ta) δ,
          ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)}
            : Finset ℂ)) := by
  classical
  have hn : 0 < n := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb : (0 : ℝ) < Real.pi / r := by positivity
  have hR0 : (0 : ℝ) < R₀ := lt_trans hta hR
  have hQta : (ftRootPolyReal c a).eval ta ≠ 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc.ne' (Finset.prod_ne_zero_iff.2 fun k _ => hne k)
  set zb : ℝ := -((ftRootPolyReal c a).eval ta) / ta ^ r with hzb
  -- the circle `R₀` is zero-free for the LIMITING pencil: the collision is inside,
  -- everything else is outside, and `hsep` is what says there is nothing between
  have hlimsphere : ∀ t : ℂ, ‖t‖ = R₀ →
      (ftDen (ftRootPoly c a) r ((zb : ℝ) : ℂ)).eval t ≠ 0 := by
    intro t ht hzero
    by_cases hteq : t = ((ta : ℝ) : ℂ)
    · rw [hteq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hta] at ht
      exact absurd ht (by linarith)
    · exact absurd ht (by have := hsep t hzero hteq; linarith)
  -- the branch facts on the open arc
  obtain ⟨hrootA, hposA⟩ :=
    ft_branch_root_and_pos (a := a) (r := r) c hn ha hr (Or.inl hn2)
  have harc : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo (0 : ℝ) (Real.pi / r) :=
    Ioo_mem_nhdsGT hb
  have hagree : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ftTauArc a r (n - 1) ta δ = ftTau a r (n - 1) δ := by
    filter_upwards [harc] with δ hδ
    exact ftTauArc_agree a r (n - 1) ta hδ.1 hδ.2
  have hTsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ftTau a r (n - 1) δ < (ta + R₀) / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hlim ((R₀ - ta) / 2) (by linarith)]
      with δ hδ
    rw [Real.dist_eq, abs_lt] at hδ
    linarith [hδ.2]
  -- the branch's spectral parameter runs into the endpoint value
  have hmem : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      δ ∈ Set.Ioo 0 Real.pi ∧ FTBranchAt a r (n - 1) δ := by
    filter_upwards [harc] with δ hδ
    refine ⟨⟨hδ.1, lt_of_lt_of_le hδ.2 ?_⟩,
      ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hδ⟩
    rw [div_le_iff₀ hrR]
    nlinarith [Real.pi_pos, (by exact_mod_cast hr : (1 : ℝ) ≤ r)]
  have hz : Tendsto (ftBranchZ a c r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 zb) :=
    tendsto_ftBranchZ_lower (c := c) ha hta hmem hlim
  have hzC : Tendsto (fun δ => ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((zb : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hz
  have hsphere : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ t : ℂ, ‖t‖ = R₀ →
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval t ≠ 0 :=
    eventually_eval_ftDen_ne_zero_on_sphere_of_tendsto hzC hR0 hlimsphere
  -- the count in the disk is two, at the limit and then along the branch
  have hlimcount : (Shields.rootsIn (ftDen (ftRootPoly c a) r ((zb : ℝ) : ℂ))
      0 R₀).card = 2 := by
    set p : Polynomial ℂ := ftDen (ftRootPoly c a) r ((zb : ℝ) : ℂ) with hp
    have hmult : p.roots.count ((ta : ℝ) : ℂ) = 2 := by
      rw [Polynomial.count_roots, hp, hzb]
      exact rootMultiplicity_ftDen_eq_two_at_critical hn ha hc.ne' hr hta.ne' hne hE hQta
    have hfil : p.roots.filter (fun w => dist w 0 < R₀)
        = p.roots.filter (fun w => w = ((ta : ℝ) : ℂ)) := by
      refine Multiset.filter_congr fun w hw => ?_
      constructor
      · intro hlt
        by_contra hwne
        have hroot : p.eval w = 0 := (Polynomial.mem_roots'.1 hw).2
        rw [hp] at hroot
        have := hsep w hroot hwne
        rw [dist_zero_right] at hlt
        linarith
      · intro heq
        rw [heq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hta]
        linarith
    rw [Shields.rootsIn, hfil, Multiset.filter_eq', hmult, Multiset.card_replicate]
  have hcount := card_rootsIn_ftDen_eventuallyEq_of_tendsto (Q := ftRootPoly c a)
    (r := r) hR0 hzC (fun t ht =>
      hlimsphere t (by simpa [Complex.dist_eq, sub_zero] using ht))
  -- assemble
  filter_upwards [harc, hagree, hTsmall, hsphere, hcount] with δ hδarc hδag hδsm hδsp hδct
  have hπarc : δ ∈ Set.Ioo (0 : ℝ) Real.pi := by
    refine ⟨hδarc.1, lt_of_lt_of_le hδarc.2 ?_⟩
    rw [div_le_iff₀ hrR]
    nlinarith [Real.pi_pos, (by exact_mod_cast hr : (1 : ℝ) ≤ r)]
  have hTpos : 0 < ftTauArc a r (n - 1) ta δ := by rw [hδag]; exact hposA _ hδarc
  have hTle : ftTauArc a r (n - 1) ta δ ≤ (ta + R₀) / 2 := by rw [hδag]; exact hδsm.le
  have hPeq : ftPrincipal (ftTauArc a r (n - 1) ta) δ
      = ftPrincipal (ftTau a r (n - 1)) δ := by
    rw [ftPrincipal, ftPrincipal, hδag]
  have hProot : (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval
      (ftPrincipal (ftTauArc a r (n - 1) ta) δ) = 0 := by
    rw [hPeq]; exact hrootA _ hδarc
  have hCjeq : ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)
      = (starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) ta) δ) :=
    (conj_ftPrincipal' (ftTauArc a r (n - 1) ta) δ).symm
  have hnec : ftPrincipal (ftTauArc a r (n - 1) ta) δ ≠
      ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I) := by
    rw [hCjeq]
    exact ftPrincipal_ne_conj_of_pos hTpos hπarc
  have hCjroot : (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval
      (((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)) = 0 := by
    rw [hCjeq]
    exact ftDen_eval_conj_eq_zero (hasRealCoeffs_ftRootPoly c a) hProot
  have hPnorm : ‖ftPrincipal (ftTauArc a r (n - 1) ta) δ‖ = ftTauArc a r (n - 1) ta δ :=
    norm_ftPrincipal_eq hTpos
  have hCjnorm : ‖((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) *
      Complex.exp (-((δ : ℝ) : ℂ) * I)‖ = ftTauArc a r (n - 1) ta δ := by
    rw [hCjeq]; simpa using hPnorm
  have hlt : ftTauArc a r (n - 1) ta δ < R₀ := by linarith
  have hDne : ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hev : (ftDen (ftRootPoly c a) r
        ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval 0 = 0 := by
      rw [h0]; simp
    rw [ftDen_eval, zero_pow (by omega : r ≠ 0), mul_zero, add_zero] at hev
    exact eval_ftRootPoly_zero_ne_zero hc.ne' ha hev
  have hTcard : (({ftPrincipal (ftTauArc a r (n - 1) ta) δ,
      ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) *
        Complex.exp (-((δ : ℝ) : ℂ) * I)} : Finset ℂ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hnec), Finset.card_singleton]
  have hTmem : ∀ w ∈ ({ftPrincipal (ftTauArc a r (n - 1) ta) δ,
      ((ftTauArc a r (n - 1) ta δ : ℝ) : ℂ) *
        Complex.exp (-((δ : ℝ) : ℂ) * I)} : Finset ℂ),
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval w = 0 ∧
        ‖w‖ < R₀ := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hProot, by rw [hPnorm]; exact hlt⟩
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact ⟨hCjroot, by rw [hCjnorm]; exact hlt⟩
  obtain ⟨hsimp, huniq⟩ :=
    simple_and_complete_of_count hDne (by rw [hδct]; exact hlimcount)
      (fun t ht => hδsp t ht) hTcard hTmem
  exact ⟨hTpos, hTle, hProot, hnec,
    fun w hw => ⟨(hTmem w hw).1, (hTmem w hw).2, hsimp w hw⟩, huniq⟩

/-- **A separating radius, produced rather than computed.**  From the pointwise
strict inequality `t < ‖w‖` at every root other than `t`, a single `R₀` strictly
between them.  Finiteness of the root set is what makes the step legitimate, and
it is the whole reason the retained group needs no constant: `R₀` comes out of the
pencil, not out of a formula in the pencil's data.

There is no uniform clearance at `ρ = 1` — the infimum over pencils is `1`,
unattained — so a `R₀` of the form `t·(1 + κ)` cannot exist, and this is what
replaces it. -/
theorem exists_separating_radius {p : Polynomial ℂ} (hp : p ≠ 0) {t : ℝ}
    (hsep : ∀ w : ℂ, p.eval w = 0 → w ≠ ((t : ℝ) : ℂ) → t < ‖w‖) :
    ∃ R₀ : ℝ, t < R₀ ∧ ∀ w : ℂ, p.eval w = 0 → w ≠ ((t : ℝ) : ℂ) → R₀ < ‖w‖ := by
  classical
  set S : Finset ℂ := p.roots.toFinset.erase ((t : ℝ) : ℂ) with hS
  have hmemS : ∀ w : ℂ, p.eval w = 0 → w ≠ ((t : ℝ) : ℂ) → w ∈ S := by
    intro w hw hwne
    rw [hS, Finset.mem_erase]
    exact ⟨hwne, Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨hp, hw⟩)⟩
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨t + 1, by linarith, fun w hw hwne => ?_⟩
    have hw' := hmemS w hw hwne
    rw [hemp] at hw'
    exact absurd hw' (Finset.notMem_empty w)
  · refine ⟨(t + S.inf' hne (fun w => ‖w‖)) / 2, ?_, fun w hw hwne => ?_⟩
    · have htm : t < S.inf' hne (fun w => ‖w‖) := by
        rw [Finset.lt_inf'_iff]
        intro w hwS
        rw [hS, Finset.mem_erase] at hwS
        exact hsep w (Polynomial.mem_roots'.1 (Multiset.mem_toFinset.1 hwS.2)).2 hwS.1
      linarith
    · have htm : t < S.inf' hne (fun w => ‖w‖) := by
        rw [Finset.lt_inf'_iff]
        intro y hyS
        rw [hS, Finset.mem_erase] at hyS
        exact hsep y (Polynomial.mem_roots'.1 (Multiset.mem_toFinset.1 hyS.2)).2 hyS.1
      have hle : S.inf' hne (fun w => ‖w‖) ≤ ‖w‖ :=
        Finset.inf'_le _ (hmemS w hw hwne)
      linarith

end ForgacsTran
