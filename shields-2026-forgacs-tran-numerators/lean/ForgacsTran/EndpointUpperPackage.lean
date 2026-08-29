/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointPackage
import ForgacsTran.FTBranchUpperRefutation
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.FTMinModulus.UpperEndpoint

/-!
# The upper endpoint's package

`EndpointPackage` supplies `thm:weighted-dominance`'s lower-endpoint binders from
the branch.  This module does the same at the upper endpoint, where the geometry
is not the mirror image of the lower one and none of that module's separating
data transfers.

Below, the cluster collapses to the smallest zero `x_1` of `Q`, the separating
circle sits *outside* it, `|Q|` is bounded from *below* on that circle, the
`zt^r` term is negligible, and the count is the multiplicity `ρ`.  Above, the
cluster collapses to the *origin*, the circle sits *inside* the whole spectrum,
`|Q|` is bounded from *above*, `zt^r` is *dominant*, and the count is `r`.

## Main statements

* `ftTauArc` — the branch radius extended to the *closed* viewing arc by its limit
  at each end: `x_1` at `0`, and `0` at `π/r`.  One radius serves both endpoints
  and the interior, which is what a single `τ` in `thm:weighted-dominance` needs.
* `hasDerivWithinAt_ftPrincipal_ftTauArc_upper` — `hγd₁`: the principal branch
  enters the origin with derivative `Le^{iπ/r}`, `L = r/(sin(π/r)∑1/a_k) > 0`.
* `exists_upper_amplitude_floor` — `hamp₁` at exponent `1`, from
  `Amplitude.amplitude_lower_bound_of_origin_form`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`,
  `thm:weighted-dominance`, `eq:principal-infinite-endpoint-regularity`.

## Tags

upper endpoint, branch radius, principal amplitude, weighted dominance
-/

namespace ForgacsTran

open Complex Filter Topology Polynomial
open scoped Topology

/-! ### The branch radius on the closed arc -/

/-- The branch radius extended to the closed viewing arc `[0, π/r]` by its limit at
each end.  Below `π/r` this is `ftTauLower`, which carries the lower endpoint's
value `x_1`; at and beyond `π/r` it is `0`, which is the upper endpoint's limit
(`FTBranchUpper.tendsto_ftTau_nhdsLT_upper`). -/
noncomputable def ftTauArc {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) : ℝ → ℝ :=
  fun θ => if θ < Real.pi / r then ftTauLower a r l x₁ θ else 0

theorem ftTauArc_eq_lower {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) {θ : ℝ}
    (hθ : θ < Real.pi / r) : ftTauArc a r l x₁ θ = ftTauLower a r l x₁ θ := by
  rw [ftTauArc, if_pos hθ]

theorem ftTauArc_agree {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ < Real.pi / r) : ftTauArc a r l x₁ θ = ftTau a r l θ := by
  rw [ftTauArc_eq_lower a r l x₁ hθ, ftTauLower_agree a r l x₁ hθ0]

@[simp] theorem ftTauArc_arc_end {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) :
    ftTauArc a r l x₁ (Real.pi / r) = 0 := by
  rw [ftTauArc, if_neg (lt_irrefl _)]

@[simp] theorem ftPrincipal_ftTauArc_arc_end {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) :
    ftPrincipal (ftTauArc a r l x₁) (Real.pi / r) = 0 := by
  rw [ftPrincipal, ftTauArc_arc_end]
  simp

/-- The two radii agree on the whole open arc, so anything the lower endpoint's
package states on a window near `0` transfers to `ftTauArc` verbatim. -/
theorem ftPrincipal_ftTauArc_eq_lower {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) {θ : ℝ}
    (hθ : θ < Real.pi / r) :
    ftPrincipal (ftTauArc a r l x₁) θ = ftPrincipal (ftTauLower a r l x₁) θ := by
  rw [ftPrincipal, ftPrincipal, ftTauArc_eq_lower a r l x₁ hθ]

/-! ### `hγd₁`: the branch enters the origin with a nonzero one-sided derivative -/

/-- **`eq:principal-infinite-endpoint-regularity` at the branch.**  In the chart
`η ↦ π/r - η` the principal point has the one-sided derivative
`Le^{iπ/r}` at `η = 0`, with `L = r/(sin(π/r)∑1/a_k)` the collapse rate of
`FTBranchUpper.tendsto_ftTau_div_nhdsLT_upper`.

The value at `η = 0` is `0` — the branch runs into the *origin*, which is what
`FTBranchUpperRefutation.not_upper_endpoint_datum_ne_zero` says no nonzero
endpoint datum can be — so the slope is the radius over `η` times the arc factor,
and neither half needs a chart. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauArc_upper {n r : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    HasDerivWithinAt
      (fun η : ℝ => ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - η))
      ((((r : ℝ) / (Real.sin (Real.pi / r) * ∑ k, (a k)⁻¹) : ℝ) : ℂ)
        * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)) (Set.Ici 0) 0 := by
  have hπ := Real.pi_pos
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hb : 0 < Real.pi / r := div_pos hπ hr0
  set L : ℝ := (r : ℝ) / (Real.sin (Real.pi / r) * ∑ k, (a k)⁻¹) with hL
  -- the radius half, transported to the chart
  have hratio : Tendsto (fun η : ℝ => ftTau a r (n - 1) (Real.pi / r - η) / η)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have h := (tendsto_ftTau_div_nhdsLT_upper hn2 ha hr).comp tendsto_sub_nhdsGT_zero
    refine h.congr fun η => ?_
    simp only [Function.comp_def]
    ring_nf
  have hratioC : Tendsto
      (fun η : ℝ => ((ftTau a r (n - 1) (Real.pi / r - η) / η : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((L : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hratio
  -- the arc half
  have hexpc : Tendsto (fun η : ℝ => Complex.exp (((Real.pi / r - η : ℝ) : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I))) := by
    have hc : Continuous fun η : ℝ =>
        Complex.exp (((Real.pi / r - η : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
          continuous_const)
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    simpa using h
  have hcomb := hratioC.mul hexpc
  have hdiff : (Set.Ici (0 : ℝ)) \ {(0 : ℝ)} = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff]
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hb] with η hη hηb
  have hη0 : (0 : ℝ) < η := hη
  have hηC : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hη0
  have hmem : Real.pi / r - η < Real.pi / r := by linarith
  have hmem0 : (0 : ℝ) < Real.pi / r - η := by linarith [hηb.2]
  simp only [slope, vsub_eq_sub, sub_zero, Complex.real_smul, Complex.ofReal_inv]
  rw [ftPrincipal_ftTauArc_arc_end, ftPrincipal,
    ftTauArc_agree a r (n - 1) x₁ hmem0 hmem]
  push_cast
  field

/-! ### One radius for both endpoints

`thm:weighted-dominance` takes a single `τ`, so the lower endpoint's data has to
hold for `ftTauArc` and not merely for `ftTauLower`.  It does, and locally for
free: the two agree on the whole open arc, and `hγ0₀`/`hγd₀` are statements at
`0`, where `Set.Ici 0` meets `Set.Iio (π/r)`. -/

@[simp] theorem ftTauArc_zero {n : ℕ} (a : Fin n → ℝ) {r : ℕ} (hr : 1 ≤ r) (l : ℕ)
    (x₁ : ℝ) : ftTauArc a r l x₁ 0 = x₁ := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  rw [ftTauArc_eq_lower a r l x₁ (by positivity), ftTauLower_zero]

@[simp] theorem ftPrincipal_ftTauArc_zero {n : ℕ} (a : Fin n → ℝ) {r : ℕ} (hr : 1 ≤ r)
    (l : ℕ) (x₁ : ℝ) : ftPrincipal (ftTauArc a r l x₁) 0 = ((x₁ : ℝ) : ℂ) := by
  rw [ftPrincipal, ftTauArc_zero a hr l x₁]
  simp

/-- **`hγd₀` for the arc radius.**  The lower endpoint's derivative datum survives
the change of radius, because `HasDerivWithinAt` is local and the two radii agree
on `Set.Iio (π/r)`. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauArc_lower {n r ρ : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauArc a r (n - 1) x₁) δ)
      (clusterAlpha x₁ ρ 0) (Set.Ici 0) 0 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb : 0 < Real.pi / r := div_pos Real.pi_pos hr0
  have hlow := hasDerivWithinAt_ftPrincipal_ftTauLower hn ha hr hnr hx₁ hmin hcard hρ
  refine hlow.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hb)] with δ hδ
    exact ftPrincipal_ftTauArc_eq_lower a r (n - 1) x₁ hδ
  · exact ftPrincipal_ftTauArc_eq_lower a r (n - 1) x₁ hb

/-! ### The transfers a two-endpoint composition needs

`thm:weighted-dominance` takes one `τ` and one `z`.  The lower endpoint's
producers are stated at `ftTauLower` and `ftBranchZLower`, the upper endpoint's at
`ftTauArc` and `ftBranchZ`, and the four agree pairwise exactly where each side
uses them: `ftTauArc = ftTauLower` on `Iio (π/r)`, and `ftBranchZLower = ftBranchZ`
on `Ioi 0`.  So the shared pair is **`ftTauArc` and `ftBranchZLower`** — the arc
radius, because only it vanishes at the upper endpoint, and the lower spectral
parameter, because only it takes the value `0` at `θ = 0` that `hk₀`'s
multiplicity clause is stated against.

These are one-liners, and they are collected rather than inlined because a
composition that gets one of the four wrong builds green on the other side. -/

/-- The conjugate principal point, in the spelling the binders use, transfers to
the arc radius alongside `ftPrincipal_ftTauArc_eq_lower`. -/
theorem conj_ftPrincipal_ftTauArc_eq_lower {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ)
    {θ : ℝ} (hθ : θ < Real.pi / r) :
    ((ftTauArc a r l x₁ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)
      = ((ftTauLower a r l x₁ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  rw [ftTauArc_eq_lower a r l x₁ hθ]

/-- The two spectral parameters agree at the upper endpoint's angles, which is
where the upper producers are stated and the lower ones are not. -/
theorem ftBranchZLower_arc_end_agree {n : ℕ} (a : Fin n → ℝ) (c : ℝ) {r : ℕ} (l : ℕ)
    (hr : 1 ≤ r) {δ : ℝ} (hδ : δ < Real.pi / r) :
    ftBranchZLower a c r l (Real.pi / r - δ) = ftBranchZ a c r l (Real.pi / r - δ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  exact ftBranchZLower_agree a c r l (by linarith)

/-- `hτle₀`'s companion for the arc radius: below `π/r` the arc radius *is* the
lower one, so the lower endpoint's bound `τ ≤ x_1` transfers unchanged. -/
theorem ftTauArc_le_of_ftTauLower_le {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} {x₁ M θ : ℝ}
    (hθ : θ < Real.pi / r) (h : ftTauLower a r l x₁ θ ≤ M) :
    ftTauArc a r l x₁ θ ≤ M := by
  rwa [ftTauArc_eq_lower a r l x₁ hθ]

/-! ### `hamp₁`: the amplitude floor at the upper endpoint -/

/-- `Q(0) \ne 0` for the pencil's own numerator polynomial: `ftRootPoly` evaluates
to `c\prod a_k` at the origin, and the zeros are positive. -/
theorem eval_ftRootPoly_zero_ne_zero {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (hc : c ≠ 0)
    (ha : ∀ k, 0 < a k) : (ftRootPoly c a).eval 0 ≠ 0 := by
  rw [eval_ftRootPoly]
  refine mul_ne_zero (by exact_mod_cast hc) (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
  simpa using (by exact_mod_cast (ha k).ne' : ((a k : ℝ) : ℂ) ≠ 0)

/-- **`hamp₁`, at the branch.**  `lem:amplitude-divisor`'s bound at the unbounded
upper endpoint, with exponent `1` and no hypothesis on the order of `B`.

The exponent is `1` because the principal point runs into the *origin*, where
`B(0) \ne 0` and `E(0) = -rQ(0) \ne 0`: neither `B` nor the `z`-free factor
vanishes at the limit point, so there is no order to subtract.  That is the
manuscript's own reason, and it is why this has no lower counterpart —
`ftPrincipalAmp_lower_bound` produces `hamp₀` with the orders `ν_B` and `k-1` in
place.

`scripts/check_upper_amplitude_floor.py` measures the same statement at four
pencils: `τ` and `|W|` both vanish to first order in `η`, so `p₁ = 1` is the
exponent with room rather than the exponent that barely fits. -/
theorem exists_upper_amplitude_floor {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 2 ≤ r)
    (hB0 : B.eval 0 ≠ 0) :
    ∃ A₁ > (0 : ℝ), ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ 1 ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
        (ftTauArc a r (n - 1) x₁) (Real.pi / r - η) := by
  have hπ := Real.pi_pos
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hb : 0 < Real.pi / r := div_pos hπ hr0
  have hmemπ : Real.pi / r ∈ Set.Ioo 0 Real.pi := ⟨hb, by
    rw [div_lt_iff₀ hr0]; nlinarith⟩
  have hsin : 0 < Real.sin (Real.pi / r) :=
    Real.sin_pos_of_pos_of_lt_pi hmemπ.1 hmemπ.2
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  have hS : 0 < ∑ k, (a k)⁻¹ := Finset.sum_pos (fun k _ => inv_pos.2 (ha k)) hne
  set L : ℝ := (r : ℝ) / (Real.sin (Real.pi / r) * ∑ k, (a k)⁻¹) with hLdef
  have hLpos : 0 < L := div_pos hr0 (mul_pos hsin hS)
  set γ : ℝ → ℂ := fun η => ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - η) with hγdef
  have hγe : ((L : ℝ) : ℂ) * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hLpos.ne') (Complex.exp_ne_zero _)
  have hγ0 : γ 0 = 0 := by
    rw [hγdef]
    simp
  obtain ⟨T, hTc, hT0, hTmul⟩ := exists_infiniteEndpoint_form hγ0
    (hasDerivWithinAt_ftPrincipal_ftTauArc_upper (x₁ := x₁) hn2 ha hr) hγe
  -- the principal point is a zero of the pencil across the open arc
  have hroot : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (ftDen (ftRootPoly c a) r
        ((ftBranchZ a c r (n - 1) (Real.pi / r - η) : ℝ) : ℂ)).eval (γ η) = 0 := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hb] with η hη hηb
    have hη0 : (0 : ℝ) < η := hη
    have hlt : Real.pi / r - η < Real.pi / r := by linarith
    have hpos : (0 : ℝ) < Real.pi / r - η := by linarith [hηb.2]
    have hmem : Real.pi / r - η ∈ Set.Ioo 0 (Real.pi / r) := ⟨hpos, hlt⟩
    have hkey := (ft_branch_root_and_pos (a := a) (r := r) c hn ha hr1
      (Or.inl hn2)).1 _ hmem
    rw [hγdef]
    simpa only [ftPrincipal, ftTauArc_agree a r (n - 1) x₁ hpos hlt] using hkey
  obtain ⟨A₁, hA₁, e, he, hbound⟩ :=
    amplitude_lower_bound_of_origin_form (Q := ftRootPoly c a) (B := B) hr1 hB0
      (eval_ftRootPoly_zero_ne_zero hc ha) hTc hT0 hTmul hroot
  refine ⟨A₁, hA₁, e, he, fun η hη hηe => ?_⟩
  simpa only [ftPrincipalAmp, pow_one, hγdef] using hbound η hη hηe

/-! ### The upper retained set

The five retained-set binders come out of one count, as they do below — but the
count is `r` rather than `ρ`, the circle sits *inside* the spectrum rather than
outside it, and `zt^r` is the dominant term rather than the negligible one.  The
consumed direction is also reversed: here simplicity is an *input*
(`EndpointSeparation.exists_simple_radius`, uniform in the spectral parameter and
needing no chart) and the count transfers to the set of points; below simplicity
is the count's own output.

The radius is left free rather than fixed at `ftUpperRadius x₁ = x₁/2`, because
the simple-zero radius `exists_simple_radius` returns is the zeros of `E = XQ' - rQ`
away from the origin and has nothing to do with `x₁`.  Both constraints then hold
on the smaller of the two.
-/

/-- **The pencil has exactly `r` zeros inside any circle its own term dominates.**
`card_rootsIn_ftDen_upper` at an arbitrary radius and an arbitrary `Q`: the
argument is Rouché against `zX^r`, whose `r` zeros all sit at the origin, and the
only thing the circle has to do is let `‖zt^r‖` beat `‖Q(t)‖`. -/
theorem card_rootsIn_upper_of_dominant {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {R : ℝ}
    (hR : 0 < R) {z : ℂ} (hzne : z ≠ 0)
    (hdom : ∀ t : ℂ, ‖t‖ = R → ‖Q.eval t‖ < ‖z‖ * R ^ r) :
    Multiset.card (Shields.rootsIn (ftDen Q r z) 0 R) = r := by
  classical
  have hlt : ∀ t ∈ Metric.sphere (0 : ℂ) R,
      ‖Q.eval t‖ < ‖(Polynomial.C z * Polynomial.X ^ r).eval t‖ := by
    intro t htmem
    have ht : ‖t‖ = R := by
      simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 htmem
    have hval : ‖(Polynomial.C z * Polynomial.X ^ r).eval t‖ = ‖z‖ * R ^ r := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, norm_mul, norm_pow, ht]
    rw [hval]
    exact hdom t ht
  have hrou := Shields.card_rootsIn_add_eq (P := Polynomial.C z * Polynomial.X ^ r)
    (Q := Q) (c := 0) hR hlt
  have hsame : Polynomial.C z * Polynomial.X ^ r + Q = ftDen Q r z := by rw [ftDen]; ring
  rw [hsame] at hrou
  rw [← hrou]
  have hmem0 : ∀ w ∈ (Polynomial.C z * Polynomial.X ^ r).roots, w = 0 := by
    intro w hw
    have h2 := (Polynomial.mem_roots'.1 hw).2
    simp only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, mul_eq_zero,
      pow_eq_zero_iff (by omega : r ≠ 0)] at h2
    rcases h2 with h | h
    · exact absurd h hzne
    · exact h
  rw [Shields.rootsIn,
    Multiset.filter_eq_self.2 (fun w hw => by rw [hmem0 w hw]; simpa using hR),
    Polynomial.roots_C_mul _ hzne, Polynomial.roots_pow, Polynomial.roots_X,
    Multiset.card_nsmul, Multiset.card_singleton, mul_one]

/-- **The upper retained set and its five binders**, from the count.  `diskRoots`
lists the zeros inside the circle once each — which is what simplicity buys — so
`hroot₁`, `haR₁`, `hsimple₁`, `huniq₁` and `card = r` are one fact about the
count rather than five facts about the cluster. -/
theorem upper_retained_set_of_dominant {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {R : ℝ}
    (hR : 0 < R)
    (hsimp : ∀ w t : ℂ, ‖t‖ ≤ R → (ftDen Q r w).eval t = 0 →
      (Polynomial.derivative (ftDen Q r w)).eval t ≠ 0)
    {z : ℂ} (hzne : z ≠ 0)
    (hdom : ∀ t : ℂ, ‖t‖ = R → ‖Q.eval t‖ < ‖z‖ * R ^ r) :
    (diskRoots (ftDen Q r z) R).card = r
      ∧ (∀ t ∈ diskRoots (ftDen Q r z) R, (ftDen Q r z).eval t = 0)
      ∧ (∀ t ∈ diskRoots (ftDen Q r z) R, ‖t‖ < R)
      ∧ (∀ t ∈ diskRoots (ftDen Q r z) R,
          (Polynomial.derivative (ftDen Q r z)).eval t ≠ 0)
      ∧ (∀ t : ℂ, ‖t‖ ≤ R → (ftDen Q r z).eval t = 0 → t ∈ diskRoots (ftDen Q r z) R) := by
  classical
  -- the circle is zero-free, because the dominant term is
  have hsphere : ∀ t : ℂ, ‖t‖ = R → (ftDen Q r z).eval t ≠ 0 := by
    intro t ht h0
    have hd := hdom t ht
    have hval : (ftDen Q r z).eval t = z * t ^ r + Q.eval t := by rw [ftDen_eval]; ring
    have hzt : ‖z * t ^ r‖ = ‖z‖ * R ^ r := by rw [norm_mul, norm_pow, ht]
    have : ‖z * t ^ r‖ = ‖Q.eval t‖ := by
      rw [show z * t ^ r = -(Q.eval t) by rw [hval] at h0; linear_combination h0, norm_neg]
    rw [hzt] at this
    linarith
  have hP : ftDen Q r z ≠ 0 := by
    intro h0
    exact hsphere ((R : ℝ) : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR])
      (by rw [h0]; simp)
  have hcard : (diskRoots (ftDen Q r z) R).card = r := by
    rw [card_diskRoots_eq_card_rootsIn hP hsphere (fun t htR ht0 => hsimp z t htR ht0)]
    exact card_rootsIn_upper_of_dominant hr hR hzne hdom
  refine ⟨hcard, fun t ht => ((mem_diskRoots hP).1 ht).1,
    fun t ht => norm_lt_of_mem_diskRoots_of_sphere hP hsphere ht,
    fun t ht => hsimp z t ((mem_diskRoots hP).1 ht).2 ((mem_diskRoots hP).1 ht).1,
    fun t htR ht0 => (mem_diskRoots hP).2 ⟨ht0, htR⟩⟩

/-! ### The retained set at the branch -/

/-- The pencil's numerator is bounded on any disk by the chord lengths at its
radius: `‖a_k - t‖ ≤ a_k + R`. -/
theorem norm_eval_ftRootPoly_le_of_norm_le {n : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (ha : ∀ k, 0 < a k) {R : ℝ} {t : ℂ} (ht : ‖t‖ ≤ R) :
    ‖(ftRootPoly c a).eval t‖ ≤ |c| * ∏ k, (a k + R) := by
  rw [eval_ftRootPoly, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
  calc ‖((a k : ℝ) : ℂ) - t‖ ≤ ‖((a k : ℝ) : ℂ)‖ + ‖t‖ := norm_sub_le _ _
    _ ≤ a k + R := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha k)]; linarith

/-- **The spectral parameter clears any threshold at the upper endpoint.**
`EndpointPackage.exists_upper_z_window` with the threshold free rather than fixed
at `ftUpperWindow`: the separating radius here is the smaller of `x_1/2` and the
simple-zero radius, which is not `ftUpperRadius`, so the threshold that goes with
it is not `ftUpperWindow` either.  At `r = 1` there is no such window and cannot
be — `z` is bounded there — which is why `2 ≤ r`. -/
theorem exists_upper_z_window_ge {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) (K : ℝ) :
    ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      K ≤ ‖((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)‖ := by
  have hr0 : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hb : 0 < Real.pi / r := div_pos Real.pi_pos hr0
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < Real.pi / r := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact (continuousAt_id (x := (0 : ℝ))).eventually_lt_const hb
  have hmap : Filter.Tendsto (fun δ : ℝ => Real.pi / r - δ) (𝓝[>] (0 : ℝ))
      (𝓝[Set.Ioo 0 (Real.pi / r)] (Real.pi / r)) := by
    refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
    · have hcont : Continuous fun δ : ℝ => Real.pi / r - δ := by fun_prop
      simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · rw [Filter.tendsto_principal]
      filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδb
      have hδ0 : (0 : ℝ) < δ := hδ
      exact Set.mem_Ioo.2 ⟨by linarith, by linarith⟩
  have hcomp := (tendsto_ftBranchZ_atTop_arc_end_of_pos hn ha hc hr).comp hmap
  have hev := hcomp.eventually_ge_atTop K
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₀ / 2, by linarith, fun δ hδ hδe => ?_⟩
  have hd : dist δ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith
  have hge := hball hd hδ
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact le_trans hge (le_abs_self _)

open scoped Classical in
/-- The upper retained set: the zeros of the pencil inside the separating circle
at angle `π/r - δ`.  Unlike `ftClusterSet` below, this is *not* a chart image —
the zeros are simple, so listing the points of the disk already enumerates them
without any branch of an `r`-th root being chosen. -/
noncomputable def ftUpperSet {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) (R : ℝ)
    (δ : ℝ) : Finset ℂ :=
  diskRoots (ftDen (ftRootPoly c a) r
    ((ftBranchZ a c r l (Real.pi / r - δ) : ℝ) : ℂ)) R

/-- **The upper retained set, and its five binders, at the branch.**  `hroot₁`,
`haR₁`, `hsimple₁`, `huniq₁` and the count `r` that `hgcard₁` rests on, on one
window of angles.

The separating radius is the smaller of `x_1/2` — which puts the circle inside
the whole spectrum — and the radius on which
`EndpointSeparation.exists_simple_radius` makes every zero of the pencil simple
*for every spectral parameter at once*.  What is owed after this is the
enumeration, which is what turns `r` into `n_1 = r - 2`. -/
theorem exists_upper_retained_set {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) (hx₁ : 0 < x₁) :
    ∃ R₁ > (0 : ℝ), R₁ ≤ x₁ / 2 ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      (ftUpperSet a c r (n - 1) R₁ δ).card = r
        ∧ (∀ t ∈ ftUpperSet a c r (n - 1) R₁ δ,
            (ftDen (ftRootPoly c a) r
              ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0)
        ∧ (∀ t ∈ ftUpperSet a c r (n - 1) R₁ δ, ‖t‖ < R₁)
        ∧ (∀ t ∈ ftUpperSet a c r (n - 1) R₁ δ,
            (Polynomial.derivative (ftDen (ftRootPoly c a) r
              ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ))).eval t ≠ 0)
        ∧ (∀ t : ℂ, ‖t‖ ≤ R₁ →
            (ftDen (ftRootPoly c a) r
              ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0 →
            t ∈ ftUpperSet a c r (n - 1) R₁ δ) := by
  have hr1 : 1 ≤ r := by omega
  obtain ⟨Rs, hRs, hsimp⟩ :=
    exists_simple_radius (Q := ftRootPoly c a) hr1 (eval_ftRootPoly_zero_ne_zero hc.ne' ha)
  set R₁ : ℝ := min Rs (x₁ / 2) with hR₁def
  have hR₁ : 0 < R₁ := lt_min hRs (by linarith)
  have hR₁le : R₁ ≤ x₁ / 2 := min_le_right _ _
  -- the threshold the circle needs, and the window on which the branch clears it
  set K : ℝ := (|c| * ∏ k, (a k + R₁) + 1) / R₁ ^ r with hKdef
  obtain ⟨e, he, hzw⟩ := exists_upper_z_window_ge hn ha hc hr K
  refine ⟨R₁, hR₁, hR₁le, e, he, fun δ hδ hδe => ?_⟩
  set z : ℂ := ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ) with hzdef
  have hzge : K ≤ ‖z‖ := hzw δ hδ hδe
  have hKpos : 0 < K := by
    refine div_pos ?_ (by positivity)
    have : (0 : ℝ) < |c| * ∏ k, (a k + R₁) := by
      refine mul_pos (abs_pos.2 hc.ne') (Finset.prod_pos fun k _ => by
        have := ha k; linarith)
    linarith
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hzge
    linarith
  have hdom : ∀ t : ℂ, ‖t‖ = R₁ → ‖(ftRootPoly c a).eval t‖ < ‖z‖ * R₁ ^ r := by
    intro t ht
    have h1 := norm_eval_ftRootPoly_le_of_norm_le (c := c) ha (R := R₁) (le_of_eq ht)
    have h2 : K * R₁ ^ r ≤ ‖z‖ * R₁ ^ r :=
      mul_le_mul_of_nonneg_right hzge (by positivity)
    have h3 : K * R₁ ^ r = |c| * ∏ k, (a k + R₁) + 1 := by
      rw [hKdef]; field_simp
    linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    upper_retained_set_of_dominant (Q := ftRootPoly c a) hr1 hR₁
      (fun w t htR ht0 => hsimp w t (le_trans htR (min_le_left _ _)) ht0) hzne hdom
  exact ⟨h1, h2, h3, h4, h5⟩


/-! ### Every direction carries a member

The upper cluster is enumerated by the `r`-th roots of unity acting on the
principal point, and this is where that enumeration comes from: near the origin
the pencil is `Q(0) + zt^r`, whose zeros are one orbit of the `r`-th roots of
unity, and each of them carries a genuine zero of the pencil.

Unlike the lower endpoint, no chart is built.  `EndpointBranch`'s `ψ` exists
because the cluster there forms at a *multiple* zero of `Q`, where an analytic
`ρ`-th root has to be extracted; here the collapse point is the origin, `Q(0) ≠ 0`,
and the model's zeros are available in closed form. -/

/-- A nonnegative real with `x^m = 1` is `1`. -/
theorem eq_one_of_pow_eq_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : m ≠ 0)
    (h : x ^ m = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_one₀ hx hlt hm))
  · exact heq
  · exact absurd h (ne_of_gt (one_lt_pow₀ hgt hm))

/-- Every `clusterDir` is unimodular: it is a root of unity. -/
theorem norm_clusterDir {r : ℕ} (hr : 1 ≤ r) (j : ℕ) : ‖clusterDir r j‖ = 1 :=
  norm_eq_one_of_pow_eq_one hr (clusterDir_pow (by omega) j)

/-- **A positive separation between distinct `r`-th roots of unity.**  Finitely
many nonzero distances, so their minimum is positive; no trigonometric bound is
needed and none is asserted. -/
theorem exists_clusterDir_sep (r : ℕ) :
    ∃ s > (0 : ℝ), ∀ i j : ℕ, i < r → j < r → i ≠ j →
      s ≤ ‖clusterDir r i - clusterDir r j‖ := by
  classical
  rcases lt_or_ge r 2 with hr1 | hr2
  · exact ⟨1, one_pos, fun i j hi hj hij => absurd (by omega : i = j) hij⟩
  have hmem : ∀ i j : ℕ, i < r → j < r → i ≠ j →
      (i, j) ∈ ((Finset.range r ×ˢ Finset.range r).filter fun p : ℕ × ℕ => p.1 ≠ p.2) := by
    intro i j hi hj hij
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hi, hj⟩, hij⟩
  have hne : ((Finset.range r ×ˢ Finset.range r).filter
      fun p : ℕ × ℕ => p.1 ≠ p.2).Nonempty :=
    ⟨(0, 1), hmem 0 1 (by omega) (by omega) (by omega)⟩
  refine ⟨((Finset.range r ×ˢ Finset.range r).filter fun p : ℕ × ℕ => p.1 ≠ p.2).inf' hne
      (fun p => ‖clusterDir r p.1 - clusterDir r p.2‖), ?_, ?_⟩
  · refine (Finset.lt_inf'_iff hne).2 fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    refine norm_pos_iff.2 (sub_ne_zero.2 fun hEq => hp.2 ?_)
    exact clusterDir_inj (by omega) hp.1.1 hp.1.2 hEq
  · exact fun i j hi hj hij => Finset.inf'_le _ (hmem i j hi hj hij)

/-- **Each rotated copy of a pencil zero carries a pencil zero.**  Given one zero
`t_p` of `D(·,z)` close enough to the origin, every `μ_jt_p` has a zero of the
same pencil within `ε‖t_p‖`.

The route is through the model `Q(0) + zt^r`, whose zeros form a single orbit:
`t_p` is close to one of them (`exists_root_of_unity_close` on
`(t_p/u)^r = Q(t_p)/Q(0)`), the rotated model zero is again a model zero, and
`exists_ftDen_root_near_origin_model_root` puts a pencil zero beside it.  The
radius `A` depends on `Q`, `r` and `ε` alone — not on `z`, which is what lets one
window of angles serve every direction at once. -/
theorem exists_root_near_scaled_root {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.eval 0 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ A > (0 : ℝ), ∀ z tp : ℂ, z ≠ 0 → (ftDen Q r z).eval tp = 0 → tp ≠ 0 → ‖tp‖ ≤ A →
      ∀ j : ℕ, ∃ t : ℂ, (ftDen Q r z).eval t = 0
        ∧ ‖t - clusterDir r j * tp‖ ≤ ε * ‖tp‖ ∧ ‖t‖ ≤ 2 * ‖tp‖ := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set κ : ℝ := min (ε' / 4) (1 / (4 * r)) with hκdef
  have hκpos : 0 < κ := lt_min (by linarith) (by positivity)
  have hκε : κ ≤ ε' / 4 := min_le_left _ _
  have hκ4 : κ * (4 * r) ≤ 1 := by
    have h : κ ≤ 1 / (4 * r) := min_le_right _ _
    calc κ * (4 * r) ≤ 1 / (4 * r) * (4 * r) := by nlinarith [hrR]
      _ = 1 := by field_simp
  have hκ14 : κ ≤ 1 / 4 := by linarith
  obtain ⟨K, hK0, ε₀, hε₀, hbd⟩ := exists_upper_ratio_bound (Q := Q) hQ0
  set Lc : ℝ := ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ * ((k : ℝ) * 1 ^ (k - 1))
    with hLc
  have hLc0 : 0 ≤ Lc := Finset.sum_nonneg fun k _ =>
    mul_nonneg (norm_nonneg _) (by positivity)
  have hQ0n : (0 : ℝ) < ‖Q.eval 0‖ := norm_pos_iff.2 hQ0
  set C : ℝ := (r : ℝ) / 2 * κ * ‖Q.eval 0‖ with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set A : ℝ := min (min (ε₀ / 2) (ε' / (40 * (K + 1))))
    (min (1 / 4) (C / (4 * (Lc + 1)))) with hA
  have hApos : 0 < A := by
    refine lt_min (lt_min (by linarith) (by positivity)) (lt_min (by norm_num) (by positivity))
  refine ⟨A, hApos, fun z tp hz htp htp0 htpA j => ?_⟩
  have htpn : (0 : ℝ) < ‖tp‖ := norm_pos_iff.2 htp0
  have hAε₀ : A < ε₀ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
    (by linarith)
  obtain ⟨-, hK2, hratio⟩ := hbd A hApos hAε₀ tp 0 htpA (by simpa using hApos.le)
  have hKA : 5 * (K * A) ≤ ε' / 8 := by
    have h1 : A ≤ ε' / (40 * (K + 1)) := le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 : K * A ≤ (K + 1) * (ε' / (40 * (K + 1))) := by nlinarith [hApos.le]
    have h3 : (K + 1) * (ε' / (40 * (K + 1))) = ε' / 40 := by field_simp
    nlinarith [hε'pos]
  have hKA8 : 5 * (K * A) ≤ 1 / 8 := by linarith
  -- a zero of the model `Q(0) + zt^r`
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u ^ r = -Q.eval 0 / z :=
    IsAlgClosed.exists_pow_nat_eq (-Q.eval 0 / z) (n := r) (by omega)
  have huroot : z * u ^ r + Q.eval 0 = 0 := by
    rw [hu]; field
  have hu0 : u ≠ 0 := (model_root_simple hr hQ0 hz huroot).1
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu0
  have h1z : z * tp ^ r = -Q.eval tp := by rw [ftDen_eval] at htp; linear_combination htp
  have h2z : z * u ^ r = -Q.eval 0 := by linear_combination huroot
  have hpow : (tp / u) ^ r = Q.eval tp / Q.eval 0 := by
    have hur : u ^ r ≠ 0 := pow_ne_zero _ hu0
    rw [div_pow, div_eq_div_iff hur hQ0]
    linear_combination (tp ^ r) * h2z - (u ^ r) * h1z
  obtain ⟨μp, hμp, hμpb⟩ :=
    exists_root_of_unity_close (ρ := r) (u := tp / u) (e := K * A) hr (by linarith)
      (by rw [hpow]; exact hratio)
  have hμpn : ‖μp‖ = 1 := norm_eq_one_of_pow_eq_one hr hμp
  have hsep : ‖tp - μp * u‖ ≤ 5 * (K * A) * ‖u‖ := by
    have hid : tp - μp * u = (tp / u - μp) * u := by field_simp
    rw [hid, norm_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [hμpb]) (norm_nonneg _)
  have hcomp : 7 * ‖u‖ ≤ 8 * ‖tp‖ := by
    have h2 : ‖u‖ - ‖tp‖ ≤ ‖tp - μp * u‖ := by
      have h := norm_sub_norm_le (μp * u) tp
      rw [norm_mul, hμpn, one_mul, norm_sub_rev] at h
      exact h
    have h3 : 5 * (K * A) * ‖u‖ ≤ 1 / 8 * ‖u‖ :=
      mul_le_mul_of_nonneg_right hKA8 (norm_nonneg _)
    linarith [hsep, h2, h3]
  have huA : ‖u‖ ≤ 2 * A := by linarith [hcomp, htpA]
  -- the rotated model zero, and a pencil zero beside it
  set w : ℂ := clusterDir r j * μp * u with hw
  have hwn : ‖w‖ = ‖u‖ := by
    rw [hw, norm_mul, norm_mul, norm_clusterDir hr, hμpn, one_mul, one_mul]
  have hwroot : z * w ^ r + Q.eval 0 = 0 := by
    have hpw : w ^ r = u ^ r := by
      rw [hw, mul_pow, mul_pow, clusterDir_pow (by omega) j, hμp, one_mul, one_mul]
    rw [hpw]; exact huroot
  have hκu : κ * ‖u‖ ≤ 1 / 4 * ‖u‖ := mul_le_mul_of_nonneg_right hκ14 (norm_nonneg _)
  have hA14 : A ≤ 1 / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hM : (1 + κ) * ‖w‖ ≤ 1 := by
    rw [hwn]
    have : (1 + κ) * ‖u‖ = ‖u‖ + κ * ‖u‖ := by ring
    rw [this]; linarith [hκu, huA, hA14]
  have hdom : (∑ k ∈ Finset.range (Q.natDegree + 1),
      ‖Q.coeff k‖ * ((k : ℝ) * (1 : ℝ) ^ (k - 1))) * ((1 + κ) * ‖w‖) < C := by
    rw [← hLc, hwn]
    have hLc1 : (0 : ℝ) < Lc + 1 := by linarith
    have hAb : A ≤ C / (4 * (Lc + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Lc + 1))] at hAb
    have hstep1 : (1 + κ) * ‖u‖ ≤ 3 * A := by
      have : (1 + κ) * ‖u‖ = ‖u‖ + κ * ‖u‖ := by ring
      rw [this]; linarith [hκu, huA]
    have hstep2 : Lc * ((1 + κ) * ‖u‖) ≤ Lc * (3 * A) :=
      mul_le_mul_of_nonneg_left hstep1 hLc0
    have hstep3 : Lc * (3 * A) < (Lc + 1) * (4 * A) := by nlinarith [hApos, hLc0]
    linarith [hstep2, hstep3, hAb]
  obtain ⟨t, htb, ht0⟩ :=
    exists_ftDen_root_near_origin_model_root (M := 1) hr hQ0 hz hwroot hκpos hκ4 hM
      (by rw [hCdef] at hdom; exact hdom)
  have htw : ‖t - w‖ ≤ κ * ‖u‖ := by rw [← hwn]; exact htb.le
  refine ⟨t, ht0, ?_, ?_⟩
  · have hid : w - clusterDir r j * tp = clusterDir r j * (μp * u - tp) := by rw [hw]; ring
    have hb1 : ‖w - clusterDir r j * tp‖ ≤ 5 * (K * A) * ‖u‖ := by
      rw [hid, norm_mul, norm_clusterDir hr, one_mul, norm_sub_rev]
      exact hsep
    have hb2 : ‖t - clusterDir r j * tp‖ ≤ ‖t - w‖ + ‖w - clusterDir r j * tp‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hsum : ‖t - clusterDir r j * tp‖ ≤ (κ + 5 * (K * A)) * ‖u‖ := by
      have : (κ + 5 * (K * A)) * ‖u‖ = κ * ‖u‖ + 5 * (K * A) * ‖u‖ := by ring
      rw [this]; linarith [hb1, hb2, htw]
    have hcoef : κ + 5 * (K * A) ≤ 3 * ε' / 8 := by linarith
    have hmul : (κ + 5 * (K * A)) * ‖u‖ ≤ 3 * ε' / 8 * ‖u‖ :=
      mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    have hu8 : 3 * ε' / 8 * ‖u‖ ≤ 3 * ε' / 8 * (8 / 7 * ‖tp‖) :=
      mul_le_mul_of_nonneg_left (by linarith [hcomp]) (by positivity)
    have hfin : 3 * ε' / 8 * (8 / 7 * ‖tp‖) ≤ ε * ‖tp‖ := by
      have hle : 3 * ε' / 7 ≤ ε := by linarith
      have := mul_le_mul_of_nonneg_right hle htpn.le
      calc 3 * ε' / 8 * (8 / 7 * ‖tp‖) = 3 * ε' / 7 * ‖tp‖ := by ring
        _ ≤ ε * ‖tp‖ := this
    linarith [hsum, hmul, hu8, hfin]
  · have hb4 : ‖t‖ ≤ ‖t - w‖ + ‖w‖ := norm_le_norm_sub_add t w
    rw [hwn] at hb4
    linarith [htw, hb4, hκu, hcomp]


/-! ### The enumeration by direction

The retained set is enumerated by *which direction* a member sits in, not by an
arbitrary listing.  Which index a member carries is what `hratio₁` is stated
against, so an enumeration chosen per angle would satisfy `hginj₁`, `hgmem₁` and
`hgcard₁` — all three constrain the map's cardinality, none constrains its values
— and leave the residue ratio with nothing to converge to.

The definition is the *nearest member to `μ_jt_p`*, which is total and needs no
uniqueness argument: any member within `ε‖t_p‖` of `μ_jt_p` bounds the nearest
one, and `exists_root_near_scaled_root` supplies one.  Injectivity then comes from
the separation of the `μ_j`, and surjectivity from the count. -/

/-- `t_+ ≠ 0` wherever the branch radius is positive.  `FTGeometryAssembly` has
the modulus; this is the nonvanishing it gives. -/
theorem ftPrincipal_ne_zero_of_pos {τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ) :
    ftPrincipal τ θ ≠ 0 := by
  intro h0
  have h := norm_ftPrincipal_eq (τ := τ) (θ := θ) hτ
  rw [h0, norm_zero] at h
  exact absurd h.symm hτ.ne'

/-- **The nearest member in each direction.**  A total enumeration `G` of the
retained set by `r`-th root of unity, defined as the argument minimizing the
distance to `μ_jt_p`.  Nothing is claimed here beyond membership and minimality;
the geometry enters when a member near `μ_jt_p` is exhibited. -/
theorem exists_upper_nearest_enumeration {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ)
    (R x₁ : ℝ) :
    ∃ G : ℝ → ℕ → ℂ, ∀ (δ : ℝ) (j : ℕ), (ftUpperSet a c r l R δ).Nonempty →
      G δ j ∈ ftUpperSet a c r l R δ ∧
      ∀ t' ∈ ftUpperSet a c r l R δ,
        ‖G δ j - clusterDir r j * ftPrincipal (ftTauArc a r l x₁) (Real.pi / r - δ)‖
          ≤ ‖t' - clusterDir r j * ftPrincipal (ftTauArc a r l x₁) (Real.pi / r - δ)‖ := by
  classical
  have h : ∀ (δ : ℝ) (j : ℕ), ∃ t : ℂ, (ftUpperSet a c r l R δ).Nonempty →
      t ∈ ftUpperSet a c r l R δ ∧
      ∀ t' ∈ ftUpperSet a c r l R δ,
        ‖t - clusterDir r j * ftPrincipal (ftTauArc a r l x₁) (Real.pi / r - δ)‖
          ≤ ‖t' - clusterDir r j * ftPrincipal (ftTauArc a r l x₁) (Real.pi / r - δ)‖ := by
    intro δ j
    by_cases hne : (ftUpperSet a c r l R δ).Nonempty
    · obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image (ftUpperSet a c r l R δ)
        (fun t => ‖t - clusterDir r j
          * ftPrincipal (ftTauArc a r l x₁) (Real.pi / r - δ)‖) hne
      exact ⟨t, fun _ => ⟨ht, hmin⟩⟩
    · exact ⟨0, fun h' => absurd h' hne⟩
  choose G hG using h
  exact ⟨G, hG⟩


/-! ### The enumeration is a bijection, and where the principal pair sits

Everything below is combinatorics over the separation of the `μ_j`: no analysis
enters, and the only analytic input is the approximation `‖G_j - μ_jt_p‖ ≤ ε‖t_p‖`
with `2ε` below that separation. -/

@[simp] theorem clusterDir_zero (r : ℕ) : clusterDir r 0 = 1 := by
  rw [clusterDir, pow_zero]

/-- **The direction enumeration is a bijection onto the retained set, and its
`0` is the principal point.**  Injectivity is the separation of the `μ_j`;
surjectivity is then the count, with nothing further to prove. -/
theorem upper_enumeration_bijective {r : ℕ} {S : Finset ℂ} {G : ℕ → ℂ}
    {tp : ℂ} (htp0 : tp ≠ 0) (hcard : S.card = r) (htpS : tp ∈ S)
    (hGmem : ∀ j, G j ∈ S)
    (hGmin : ∀ j : ℕ, ∀ t' ∈ S, ‖G j - clusterDir r j * tp‖ ≤ ‖t' - clusterDir r j * tp‖)
    {s ε : ℝ} (hs : ∀ i j : ℕ, i < r → j < r → i ≠ j → s ≤ ‖clusterDir r i - clusterDir r j‖)
    (hεs : 2 * ε < s) (happ : ∀ j : ℕ, ‖G j - clusterDir r j * tp‖ ≤ ε * ‖tp‖) :
    G 0 = tp ∧ (∀ i j : ℕ, i < r → j < r → G i = G j → i = j)
      ∧ ∀ t ∈ S, ∃ j, j < r ∧ G j = t := by
  classical
  have htpn : (0 : ℝ) < ‖tp‖ := norm_pos_iff.2 htp0
  have hzero : G 0 = tp := by
    have h := hGmin 0 tp htpS
    rw [clusterDir_zero, one_mul, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  have hinj : ∀ i j : ℕ, i < r → j < r → G i = G j → i = j := by
    intro i j hi hj hij
    by_contra hne
    have h1 := happ i
    have h2 := happ j
    rw [← hij] at h2
    have hkey : ‖clusterDir r i * tp - clusterDir r j * tp‖ ≤ 2 * ε * ‖tp‖ := by
      calc ‖clusterDir r i * tp - clusterDir r j * tp‖
          ≤ ‖clusterDir r i * tp - G i‖ + ‖G i - clusterDir r j * tp‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε * ‖tp‖ + ε * ‖tp‖ := by
            rw [norm_sub_rev (clusterDir r i * tp) (G i)]
            exact add_le_add h1 h2
        _ = 2 * ε * ‖tp‖ := by ring
    have hfac : ‖clusterDir r i * tp - clusterDir r j * tp‖
        = ‖clusterDir r i - clusterDir r j‖ * ‖tp‖ := by
      rw [← norm_mul]; congr 1; ring
    rw [hfac] at hkey
    have hsle := hs i j hi hj hne
    nlinarith [hkey, hsle, htpn, hεs]
  refine ⟨hzero, hinj, fun t ht => ?_⟩
  -- injective on `range r` into a set of the same size, hence onto
  have himg : (Finset.range r).image G ⊆ S := by
    intro w hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hw
    exact hGmem j
  have hcardimg : ((Finset.range r).image G).card = r := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hEq
    exact hinj i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hEq
  have heq : (Finset.range r).image G = S :=
    Finset.eq_of_subset_of_card_le himg (by rw [hcardimg, hcard])
  rw [← heq] at ht
  obtain ⟨j, hj, hjt⟩ := Finset.mem_image.1 ht
  exact ⟨j, Finset.mem_range.1 hj, hjt⟩

/-- **Which index the conjugate principal point carries.**  It is `r-1`, because
`\overline{t_+}/t_+ = e^{-2i(π/r - δ)} \to μ_{r-1}` and the `μ_j` are separated.
This is the second half of `hgmem₁`'s erasure: the retained group is the indices
`1, …, r-2`, and it is empty exactly at `r = 2`, which is the manuscript's "the
cluster is the principal pair alone". -/
theorem upper_conj_index {r : ℕ} (hr : 2 ≤ r) {S : Finset ℂ} {G : ℕ → ℂ} {tp cj : ℂ}
    (htp0 : tp ≠ 0) (hcjS : cj ∈ S)
    (hsurj : ∀ t ∈ S, ∃ j, j < r ∧ G j = t)
    {s ε ε' : ℝ} (hs : ∀ i j : ℕ, i < r → j < r → i ≠ j → s ≤ ‖clusterDir r i - clusterDir r j‖)
    (happ : ∀ j : ℕ, ‖G j - clusterDir r j * tp‖ ≤ ε * ‖tp‖)
    (hcj : ‖cj - clusterDir r (r - 1) * tp‖ ≤ ε' * ‖tp‖) (hsum : ε + ε' < s) :
    G (r - 1) = cj := by
  have htpn : (0 : ℝ) < ‖tp‖ := norm_pos_iff.2 htp0
  obtain ⟨j, hj, hjt⟩ := hsurj cj hcjS
  have hidx : j = r - 1 := by
    by_contra hne
    have h1 := happ j
    rw [hjt] at h1
    have hkey : ‖clusterDir r j * tp - clusterDir r (r - 1) * tp‖ ≤ (ε + ε') * ‖tp‖ := by
      calc ‖clusterDir r j * tp - clusterDir r (r - 1) * tp‖
          ≤ ‖clusterDir r j * tp - cj‖ + ‖cj - clusterDir r (r - 1) * tp‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε * ‖tp‖ + ε' * ‖tp‖ := by
            rw [norm_sub_rev (clusterDir r j * tp) cj]
            exact add_le_add h1 hcj
        _ = (ε + ε') * ‖tp‖ := by ring
    have hfac : ‖clusterDir r j * tp - clusterDir r (r - 1) * tp‖
        = ‖clusterDir r j - clusterDir r (r - 1)‖ * ‖tp‖ := by
      rw [← norm_mul]; congr 1; ring
    rw [hfac] at hkey
    have hsle := hs j (r - 1) hj (by omega) hne
    nlinarith [hkey, hsle, htpn, hsum]
  rw [← hidx]; exact hjt

/-! ### The branch's own window -/

/-- An eventual statement along `0⁺` as a window `(0, e]`. -/
theorem window_of_eventually {p : ℝ → Prop} (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), p δ) :
    ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → p δ := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε₀ / 2, by linarith, fun δ hδ hδe => ?_⟩
  exact hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith) hδ

/-- **The branch's data on a window at the upper endpoint**: the radius positive
and as small as asked, the extended radius agreeing with the branch there, the
principal point a zero of the pencil, and the spectral parameter nonzero.  The
last is not decoration — `exists_root_near_scaled_root` needs it, and at the upper
endpoint it is free because `‖z‖ → ∞`. -/
theorem exists_upper_branch_window {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) {M : ℝ} (hM : 0 < M) :
    ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      0 < ftTau a r (n - 1) (Real.pi / r - δ)
      ∧ ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) = ftTau a r (n - 1) (Real.pi / r - δ)
      ∧ ftTau a r (n - 1) (Real.pi / r - δ) ≤ M
      ∧ (ftDen (ftRootPoly c a) r
          ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval
          (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)) = 0
      ∧ ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ) ≠ 0 := by
  have hπ := Real.pi_pos
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hb : 0 < Real.pi / r := div_pos hπ hr0
  obtain ⟨ez, hez, hzw⟩ := exists_upper_z_window_ge hn ha hc hr 1
  -- the radius collapses, so it is eventually below `M`
  have hτ : Filter.Tendsto (fun δ : ℝ => ftTau a r (n - 1) (Real.pi / r - δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_ftTau_nhdsLT_upper hn2 ha hr).comp tendsto_sub_nhdsGT_zero
  obtain ⟨eτ, heτ, hτw⟩ := window_of_eventually (hτ.eventually_le_const hM)
  obtain ⟨hbr, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr1 (Or.inl hn2)
  refine ⟨min (min eτ ez) (Real.pi / (2 * r)), lt_min (lt_min heτ hez) (by positivity),
    fun δ hδ hδe => ?_⟩
  have hδτ : δ ≤ eτ := le_trans hδe (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδz : δ ≤ ez := le_trans hδe (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδb : δ < Real.pi / r := by
    have h1 : δ ≤ Real.pi / (2 * r) := le_trans hδe (min_le_right _ _)
    have h2 : Real.pi / (2 * r) < Real.pi / r := by
      rw [div_lt_div_iff₀ (by positivity) hr0]; nlinarith
    linarith
  have hmem : Real.pi / r - δ ∈ Set.Ioo 0 (Real.pi / r) := ⟨by linarith, by linarith⟩
  have hagree := ftTauArc_agree a r (n - 1) x₁ hmem.1 hmem.2
  refine ⟨hpos _ hmem, hagree, hτw δ hδ hδτ, ?_, ?_⟩
  · rw [ftPrincipal, hagree]
    exact hbr _ hmem
  · intro h0
    have h1 := hzw δ hδ hδz
    rw [h0, norm_zero] at h1
    linarith

/-! ### The conjugate principal point sits in direction `r-1` -/

theorem conj_ftPrincipal' (τ : ℝ → ℝ) (θ : ℝ) :
    (starRingEnd ℂ) (ftPrincipal τ θ) = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I) := by
  rw [ftPrincipal, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `μ_{r-1} = e^{-2πi/r}`: the last direction is the first one reflected, which is
why it is the conjugate principal point's. -/
theorem clusterDir_last {r : ℕ} (hr : 1 ≤ r) :
    clusterDir r (r - 1) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / (r : ℂ))) := by
  have hpow : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ))) ^ r = 1 := by
    simpa [clusterDir] using clusterDir_pow (ρ := r) (by omega) 1
  have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hsplit : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ))) ^ (r - 1)
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ)) = 1 := by
    rw [← pow_succ, show r - 1 + 1 = r by omega]
    exact hpow
  rw [clusterDir, Complex.exp_neg]
  field_simp
  linear_combination hsplit

/-- **The conjugate principal point lies in direction `r-1`, to first order in
`δ`.**  `\overline{t_+}/t_+ = e^{-2i(π/r-δ)}` and `μ_{r-1} = e^{-2πi/r}`, so the
two differ by `e^{2iδ} - 1`. -/
theorem norm_conj_ftPrincipal_sub_clusterDir {r : ℕ} (hr : 1 ≤ r) {τ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : 2 * δ ≤ 1) :
    ‖(starRingEnd ℂ) (ftPrincipal τ (Real.pi / r - δ))
        - clusterDir r (r - 1) * ftPrincipal τ (Real.pi / r - δ)‖
      ≤ 4 * δ * |τ (Real.pi / r - δ)| := by
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < (r : ℝ)).ne'
  set θ : ℝ := Real.pi / r - δ with hθ
  set T : ℝ := τ θ with hTdef
  have hid : (starRingEnd ℂ) (ftPrincipal τ θ) - clusterDir r (r - 1) * ftPrincipal τ θ
      = ((T : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)
        * (1 - Complex.exp (-(2 * (δ : ℝ) : ℂ) * I)) := by
    rw [conj_ftPrincipal' τ θ, clusterDir_last hr, ftPrincipal]
    have hexp : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / (r : ℂ)))
        * (((θ : ℝ) : ℂ) * I).exp
        = Complex.exp (-((θ : ℝ) : ℂ) * I) * Complex.exp (-(2 * (δ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hθ]
      push_cast
      field
    calc ((T : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)
          - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / (r : ℂ)))
            * (((T : ℝ) : ℂ) * (((θ : ℝ) : ℂ) * I).exp)
        = ((T : ℝ) : ℂ) * (Complex.exp (-((θ : ℝ) : ℂ) * I)
          - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / (r : ℂ)))
            * (((θ : ℝ) : ℂ) * I).exp) := by ring
      _ = _ := by rw [hexp]; ring
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-((θ : ℝ) : ℂ) * I).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one]
  have hbd : ‖1 - Complex.exp (-(2 * (δ : ℝ) : ℂ) * I)‖ ≤ 4 * δ := by
    have harg : ‖(-(2 * (δ : ℝ) : ℂ) * I)‖ = 2 * δ := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
      simp [Complex.norm_real, abs_of_nonneg hδ]
    have := Complex.norm_exp_sub_one_le (x := -(2 * (δ : ℝ) : ℂ) * I) (by rw [harg]; linarith)
    rw [harg, norm_sub_rev] at this
    linarith
  calc |T| * ‖1 - Complex.exp (-(2 * (δ : ℝ) : ℂ) * I)‖ ≤ |T| * (4 * δ) :=
        mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
    _ = 4 * δ * |T| := by ring

/-! ### The upper cluster package

Everything the upper endpoint's binders are built from, on one window: the
retained set with its five binders, the direction enumeration with its
convergence, and the two indices the principal pair occupies. -/

/-- **The upper cluster, enumerated.**  The retained set of
`exists_upper_retained_set` together with a direction enumeration `G` that is a
bijection onto it, converges to its direction at every rate, and puts the
principal point at index `0` and its conjugate at index `r-1`.

That last pair is what `hgmem₁`'s double erasure removes, so the retained group is
the indices `1, …, r-2` and `n_1 = r - 2`.  At `r = 2` it is empty, which is the
manuscript's "the cluster is the principal pair alone". -/
theorem exists_upper_cluster_package {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) (hx₁ : 0 < x₁) :
    ∃ R₁ > (0 : ℝ), ∃ G : ℝ → ℕ → ℂ,
      (∀ ε > (0 : ℝ), ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ j : ℕ,
        ‖G δ j - clusterDir r j * ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖
          ≤ ε * ftTau a r (n - 1) (Real.pi / r - δ))
      ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
        0 < ftTau a r (n - 1) (Real.pi / r - δ)
        ∧ ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) = ftTau a r (n - 1) (Real.pi / r - δ)
        ∧ 2 * ftTau a r (n - 1) (Real.pi / r - δ) ≤ R₁
        ∧ (ftUpperSet a c r (n - 1) R₁ δ).card = r
        ∧ (∀ t ∈ ftUpperSet a c r (n - 1) R₁ δ,
            (ftDen (ftRootPoly c a) r
              ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0)
        ∧ (∀ t ∈ ftUpperSet a c r (n - 1) R₁ δ, ‖t‖ < R₁)
        ∧ (∀ t ∈ ftUpperSet a c r (n - 1) R₁ δ,
            (Polynomial.derivative (ftDen (ftRootPoly c a) r
              ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ))).eval t ≠ 0)
        ∧ (∀ t : ℂ, ‖t‖ ≤ R₁ →
            (ftDen (ftRootPoly c a) r
              ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0 →
            t ∈ ftUpperSet a c r (n - 1) R₁ δ)
        ∧ ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)
            ∈ ftUpperSet a c r (n - 1) R₁ δ
        ∧ (starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))
            ∈ ftUpperSet a c r (n - 1) R₁ δ
        ∧ G δ 0 = ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)
        ∧ G δ (r - 1)
            = (starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))
        ∧ (∀ i j : ℕ, i < r → j < r → G δ i = G δ j → i = j)
        ∧ (∀ j : ℕ, G δ j ∈ ftUpperSet a c r (n - 1) R₁ δ) := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  obtain ⟨R₁, hR₁, hR₁x, eS, heS, hset⟩ := exists_upper_retained_set hn ha hc hr hx₁
  obtain ⟨G, hG⟩ := exists_upper_nearest_enumeration a c r (n - 1) R₁ x₁
  -- the approximation, at every rate
  have happrox : ∀ ε > (0 : ℝ), ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      (0 < ftTau a r (n - 1) (Real.pi / r - δ)
        ∧ ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) = ftTau a r (n - 1) (Real.pi / r - δ)
        ∧ 2 * ftTau a r (n - 1) (Real.pi / r - δ) ≤ R₁
        ∧ ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)
            ∈ ftUpperSet a c r (n - 1) R₁ δ)
      ∧ ∀ j : ℕ, ‖G δ j - clusterDir r j
          * ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖
        ≤ ε * ftTau a r (n - 1) (Real.pi / r - δ) := by
    intro ε hε
    obtain ⟨A, hA, hnear⟩ := exists_root_near_scaled_root (Q := ftRootPoly c a) hr1 hQ0 hε
    obtain ⟨eb, heb, hbw⟩ := exists_upper_branch_window (x₁ := x₁) hn2 ha hc hr
      (M := min A (R₁ / 2)) (lt_min hA (by linarith))
    refine ⟨min eS eb, lt_min heS heb, fun δ hδ hδe => ?_⟩
    obtain ⟨hτpos, hagree, hτle, hProot, hZne⟩ :=
      hbw δ hδ (le_trans hδe (min_le_right _ _))
    obtain ⟨hcard, hroot, haR, hsimp, huniq⟩ :=
      hset δ hδ (le_trans hδe (min_le_left _ _))
    have hτA : 0 < ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) := by rw [hagree]; exact hτpos
    have hPn : ‖ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖
        = ftTau a r (n - 1) (Real.pi / r - δ) := by
      rw [norm_ftPrincipal_eq hτA, hagree]
    have hP0 : ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ) ≠ 0 :=
      ftPrincipal_ne_zero_of_pos hτA
    have hτA' : ftTau a r (n - 1) (Real.pi / r - δ) ≤ A :=
      le_trans hτle (min_le_left _ _)
    have hτR : 2 * ftTau a r (n - 1) (Real.pi / r - δ) ≤ R₁ := by
      have := le_trans hτle (min_le_right _ _); linarith
    have hPmem : ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)
        ∈ ftUpperSet a c r (n - 1) R₁ δ := by
      refine huniq _ ?_ hProot
      rw [hPn]; linarith [hτpos]
    refine ⟨⟨hτpos, hagree, hτR, hPmem⟩, fun j => ?_⟩
    obtain ⟨t, ht0, htb, htn⟩ := hnear _ _ hZne hProot hP0 (by rw [hPn]; exact hτA') j
    have htmem : t ∈ ftUpperSet a c r (n - 1) R₁ δ := by
      refine huniq t ?_ ht0
      rw [hPn] at htn; linarith
    have hne : (ftUpperSet a c r (n - 1) R₁ δ).Nonempty := ⟨t, htmem⟩
    calc ‖G δ j - clusterDir r j
            * ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖
        ≤ ‖t - clusterDir r j
            * ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖ :=
          (hG δ j hne).2 t htmem
      _ ≤ ε * ftTau a r (n - 1) (Real.pi / r - δ) := by rw [← hPn]; exact htb
  refine ⟨R₁, hR₁, G, fun ε hε => ?_, ?_⟩
  · obtain ⟨e, he, hw⟩ := happrox ε hε
    exact ⟨e, he, fun δ hδ hδe j => (hw δ hδ hδe).2 j⟩
  -- the structure, at the rate the separation fixes
  obtain ⟨s, hs, hsep⟩ := exists_clusterDir_sep r
  obtain ⟨e₁, he₁, hw₁⟩ := happrox (s / 8) (by linarith)
  refine ⟨min (min eS e₁) (min (s / 32) (1 / 4)), lt_min (lt_min heS he₁)
    (lt_min (by linarith) (by norm_num)), fun δ hδ hδe => ?_⟩
  obtain ⟨⟨hτpos, hagree, hτR, hPmem⟩, happ⟩ :=
    hw₁ δ hδ (le_trans hδe (le_trans (min_le_left _ _) (min_le_right _ _)))
  obtain ⟨hcard, hroot, haR, hsimp, huniq⟩ :=
    hset δ hδ (le_trans hδe (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hτA : 0 < ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) := by rw [hagree]; exact hτpos
  have hPn : ‖ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖
      = ftTau a r (n - 1) (Real.pi / r - δ) := by rw [norm_ftPrincipal_eq hτA, hagree]
  have hP0 : ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ) ≠ 0 :=
    ftPrincipal_ne_zero_of_pos hτA
  have hProot := hroot _ hPmem
  have hne : (ftUpperSet a c r (n - 1) R₁ δ).Nonempty := ⟨_, hPmem⟩
  -- the conjugate principal point is in the set, and in direction `r-1`
  have hcjroot : (ftDen (ftRootPoly c a) r
      ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval
      ((starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))) = 0 :=
    ftDen_eval_conj_eq_zero (hasRealCoeffs_ftRootPoly c a) hProot
  have hcjmem : (starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))
      ∈ ftUpperSet a c r (n - 1) R₁ δ := by
    refine huniq _ ?_ hcjroot
    rw [RCLike.norm_conj, hPn]
    linarith [hτpos]
  have happ' : ∀ j : ℕ, ‖G δ j - clusterDir r j
      * ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖
      ≤ s / 8 * ‖ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖ := by
    intro j; rw [hPn]; exact happ j
  obtain ⟨h0, hinj, hsurj⟩ := upper_enumeration_bijective (S := ftUpperSet a c r (n - 1) R₁ δ)
    (G := G δ) hP0 hcard hPmem (fun j => (hG δ j hne).1)
    (fun j t' ht' => (hG δ j hne).2 t' ht') hsep (by linarith) happ'
  have hδs : 4 * δ ≤ s / 8 := by
    have : δ ≤ s / 32 := le_trans hδe (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith
  have hδ1 : 2 * δ ≤ 1 := by
    have : δ ≤ 1 / 4 := le_trans hδe (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  have hcjapp : ‖(starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))
      - clusterDir r (r - 1) * ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖
      ≤ s / 8 * ‖ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖ := by
    have hb := norm_conj_ftPrincipal_sub_clusterDir (r := r)
      (τ := ftTauArc a r (n - 1) x₁) hr1 hδ.le hδ1
    rw [abs_of_pos hτA] at hb
    have hval : ftTauArc a r (n - 1) x₁ (Real.pi / r - δ)
        = ‖ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)‖ :=
      (norm_ftPrincipal_eq hτA).symm
    rw [hval] at hb
    refine le_trans hb ?_
    exact mul_le_mul_of_nonneg_right hδs (norm_nonneg _)
  have hcjidx := upper_conj_index (S := ftUpperSet a c r (n - 1) R₁ δ) (G := G δ)
    hr hP0 hcjmem hsurj hsep happ' hcjapp (by linarith)
  exact ⟨hτpos, hagree, hτR, hcard, hroot, haR, hsimp, huniq, hPmem, hcjmem, h0, hcjidx, hinj,
    fun j => (hG δ j hne).1⟩

end ForgacsTran
