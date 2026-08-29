/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.LowerEndpointSimpleZero
import ForgacsTran.EndpointCollision
import ForgacsTran.EndpointLowerRhoOne
import ForgacsTran.LowerSeparationNormalized
import ForgacsTran.FTMinModulus.RoucheModel
import Shields.Analysis.Complex.MorseLemma

/-!
# The endpoint tangent at a simple smallest zero

`BranchSupplyGeometry` supplies the collar's `hd0` at a **repeated** smallest zero,
where the branch radius runs into `a_i` and arrives with the cluster expansion's
slope `-a_i cot(π/ρ)`.  `LowerEndpointSimpleZero` shows that at a **simple**
smallest zero the endpoint is a different point — the limit `L` sits strictly
inside the first gap and is a zero of `E = XQ' - rQ` — so that statement does not
transfer.  This module proves the tangent there:

  `γ'(0⁺) = L i`,

a purely imaginary vector.  The branch does not arrive along a ray; it arrives
across one, and the radial slope is exactly `0`.

## The route, and why the sign is what decides it

The branch is a level set: the fiber map `f(w) = -Q(w)/w^r` is real along it
(`FTBranchZMono.ftZFun_eq`), and `L` is a critical point of `f` because `E(L) = 0`.
At a quadratic critical point `Shields.exists_morse_square` gives an analytic
coordinate `H` with `H(L) = 0`, `H'(L) = 1` and `f - f(L) = κ H²`, so along the
branch `κ H(γ)² ∈ ℝ` and `H(γ)` is either real or purely imaginary.  The level set
is two arcs and the question is which one the branch is on.

**That question is settled by a sign, not by a local computation.**  `κ < 0`
because `f''(L) = -E'(L)/L^{r+1}` with `E' = -Σ'Q`, where `Σ' > 0` everywhere it
is defined and `Q < 0` strictly inside the first gap.  And `z(θ) > z₀` because the
branch value is strictly increasing across the arc (`ftBranchZ_strictMonoOn`) and
`z₀` is its one-sided limit.  So `κ H² > 0` forces `H² < 0`, which is the
imaginary arc, and `H'(L) = 1` transfers that to the branch point: `Re(γ - L)` is
`o(|γ - L|)`, hence `o(θ)` once `Im(γ - L) = τ sin θ` is known to dominate.

No second-order expansion of the branch is needed, and none is available: the
`ρ ≥ 2` route runs through a cluster of coincident zeros of `Q`
(`exists_bound_ftTau_sub_linear`), and at `ρ = 1` the confluence is of denominator
roots at a nonzero spectral value instead.

## Main statements

* `hasDerivAt_ftFiber`, `iteratedDeriv_two_ftFiber` — the fiber map's first two
  derivatives, the second at a zero of `E`.
* `eval_ftRootPolyReal_neg_of_first_gap` — `Q < 0` inside the first gap.
* `exists_morse_endpoint` — the Morse data with `κ` real and **negative**.
* `re_eq_zero_of_sq_ofReal_neg` — a square that is a negative real is purely
  imaginary; the two-arc dichotomy in one line.
* `exists_morse_imaginary_arc` — the chart together with the arc the branch runs
  along, which is the input any second-order statement starts from.
* `isLittleO_re_ftBranchPoint_sub` — the branch leaves the endpoint
  perpendicular to the real axis.
* `hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero_of_simple`,
  `endpointTangent_ne_zero_of_simple` — `hd0` and `h0` at `ρ = 1`.
* `not_exists_hasDerivWithinAt_ftPrincipal_min_of_simple` — and at the repeated
  case's endpoint value there is **no** `hd0` at all, in the collar's own shape.
* `exists_endpoint_tangent_of_simple` — the package, from the multiplicity
  hypothesis alone.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:ab-def`,
  `thm:FT-geometry`, `lem:principal-endpoint-regularity`,
  `eq:principal-finite-endpoint-regularity`.
* `Forgacs2017RationalDenominator`, Proposition 1, Lemma 4(ii) and Fig. 5.

## Tags

branch endpoint, simple zero, Morse coordinate, critical point, Forgacs-Tran
-/

namespace ForgacsTran

open Real Set Filter Topology Polynomial

/-! ### The fiber map's first two derivatives -/

/-- **`f' = -E/w^{r+1}`**, which is what makes a zero of `E` off the origin a
critical point of the fiber map. -/
theorem hasDerivAt_ftFiber (Q : Polynomial ℂ) {r : ℕ} (hr : 1 ≤ r) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (ftFiber Q r) (-((ftCritical Q r).eval w) / w ^ (r + 1)) w := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hnum : HasDerivAt (fun z : ℂ => -(Q.eval z)) (-((derivative Q).eval w)) w :=
    (Q.hasDerivAt w).neg
  have hden : HasDerivAt (fun z : ℂ => z ^ (m + 1)) (((m : ℂ) + 1) * w ^ m) w := by
    have h := hasDerivAt_pow (m + 1) w
    simpa using h
  have hne : w ^ (m + 1) ≠ 0 := pow_ne_zero _ hw
  have hd := hnum.div hden hne
  refine hd.congr_deriv ?_
  rw [eval_ftCritical]
  field_simp
  push_cast
  ring

/-- **`f'' = -E'/w^{r+1}` at a zero of `E`.**  The second term of the quotient rule
carries `E(w)` and drops. -/
theorem iteratedDeriv_two_ftFiber (Q : Polynomial ℂ) {r : ℕ} (hr : 1 ≤ r) {w : ℂ}
    (hw : w ≠ 0) (hE : (ftCritical Q r).eval w = 0) :
    iteratedDeriv 2 (ftFiber Q r) w = -((derivative (ftCritical Q r)).eval w) / w ^ (r + 1) := by
  have hnbhd : ∀ᶠ z in 𝓝 w, z ≠ 0 := continuousAt_id.eventually_ne hw
  have hderiv : deriv (ftFiber Q r) =ᶠ[𝓝 w]
      fun z : ℂ => -((ftCritical Q r).eval z) / z ^ (r + 1) := by
    filter_upwards [hnbhd] with z hz
    exact (hasDerivAt_ftFiber Q hr hz).deriv
  have hnum : HasDerivAt (fun z : ℂ => -((ftCritical Q r).eval z))
      (-((derivative (ftCritical Q r)).eval w)) w := ((ftCritical Q r).hasDerivAt w).neg
  have hden : HasDerivAt (fun z : ℂ => z ^ (r + 1)) (((r : ℂ) + 1) * w ^ r) w := by
    have h := hasDerivAt_pow (r + 1) w
    simpa using h
  have hne : w ^ (r + 1) ≠ 0 := pow_ne_zero _ hw
  have hq := hnum.fun_div hden hne
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    hderiv.deriv_eq, hq.deriv]
  rw [hE]
  field

/-! ### The pencil at a first-gap critical point -/

/-- `E` over `ℂ` at a real point is `E` over `ℝ`, coerced. -/
theorem eval_ftCritical_ofReal {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {r : ℕ} (t : ℝ) :
    (ftCritical (ftRootPoly c a) r).eval ((t : ℝ) : ℂ)
      = (((ftCriticalReal (ftRootPolyReal c a) r).eval t : ℝ) : ℂ) := by
  rw [ftRootPoly_eq_map, ftCritical_map, eval_map_ofReal]

/-- **`Q < 0` strictly inside the first gap.**  Exactly one factor `a_k - L` is
negative — the smallest zero's — and the rest are positive. -/
theorem eval_ftRootPolyReal_neg_of_first_gap {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {i : Fin n}
    {L : ℝ} (hc : 0 < c) (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j) :
    (ftRootPolyReal c a).eval L < 0 := by
  classical
  rw [eval_ftRootPolyReal]
  have hprod : ∏ k, (a k - L)
      = (a i - L) * ∏ k ∈ Finset.univ.erase i, (a k - L) :=
    (Finset.mul_prod_erase Finset.univ (fun k => a k - L) (Finset.mem_univ i)).symm
  have hpos : 0 < ∏ k ∈ Finset.univ.erase i, (a k - L) :=
    Finset.prod_pos fun k hk => by
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      linarith [hgap k hki]
  rw [hprod]
  have : (a i - L) * ∏ k ∈ Finset.univ.erase i, (a k - L) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hpos
  exact mul_neg_of_pos_of_neg hc this

/-- **Every zero of the pencil is at positive distance from a first-gap point.** -/
theorem sub_ne_zero_of_first_gap {n : ℕ} {a : Fin n → ℝ} {i : Fin n} {L : ℝ}
    (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j) (k : Fin n) : a k - L ≠ 0 := by
  rcases eq_or_ne k i with rfl | hk
  · exact ne_of_lt (by linarith)
  · exact ne_of_gt (by linarith [hgap k hk])

/-- **The Morse data at the lower endpoint, with `κ` real and negative.**

Real because the fiber map has real coefficients and `L` is real; negative
because `f''(L) = -E'(L)/L^{r+1}` with `E'(L) = -Σ'(L)Q(L)`, where `Σ' > 0`
everywhere it is defined and `Q < 0` strictly inside the first gap.  The sign is
what decides, below, which of the two arcs of the level set the branch runs
along, so it is carried rather than discarded. -/
theorem exists_morse_endpoint {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {i : Fin n} {L : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hLi : a i < L)
    (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0) :
    ∃ (H : ℂ → ℂ) (κ : ℝ), κ < 0 ∧ AnalyticAt ℂ H ((L : ℝ) : ℂ) ∧ H ((L : ℝ) : ℂ) = 0 ∧
      deriv H ((L : ℝ) : ℂ) = 1 ∧
      ∀ᶠ t in 𝓝 ((L : ℝ) : ℂ),
        ftFiber (ftRootPoly c a) r t - ftFiber (ftRootPoly c a) r ((L : ℝ) : ℂ)
          = ((κ : ℝ) : ℂ) * H t ^ 2 := by
  classical
  have hL0 : 0 < L := lt_trans (ha i) hLi
  have hLC : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hne : ∀ k, a k - L ≠ 0 := sub_ne_zero_of_first_gap hLi hgap
  -- the critical equation, over `ℂ`
  have hEC : (ftCritical (ftRootPoly c a) r).eval ((L : ℝ) : ℂ) = 0 := by
    rw [eval_ftCritical_ofReal, hLe, Complex.ofReal_zero]
  -- `E'(L) > 0`
  have hSig : ftSigmaReal a r L = 0 :=
    ftSigmaReal_eq_zero_of_eval_ftCriticalReal (ne_of_gt hc) hne hLe
  have hsigmaD : 0 < ∑ k, a k / (a k - L) ^ 2 := sum_div_sq_pos hn ha hne
  have hQ : (ftRootPolyReal c a).eval L < 0 :=
    eval_ftRootPolyReal_neg_of_first_gap hc hLi hgap
  have hE' : 0 < (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L := by
    rw [eval_derivative_ftCriticalReal_of_ftSigmaReal_eq_zero hne hSig]
    exact mul_pos_of_neg_of_neg (by linarith) hQ
  -- the second derivative of the fiber map, in real form
  set E' : ℝ := (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L with hE'def
  set κ : ℝ := -E' / (2 * L ^ (r + 1)) with hκdef
  have hκneg : κ < 0 := by
    rw [hκdef]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hiter : iteratedDeriv 2 (ftFiber (ftRootPoly c a) r) ((L : ℝ) : ℂ)
      = ((2 * κ : ℝ) : ℂ) := by
    rw [iteratedDeriv_two_ftFiber _ hr hLC hEC, eval_derivative_ftCritical_ofReal, hκdef,
      ← hE'def]
    have hpow : (((L : ℝ) : ℂ)) ^ (r + 1) = ((L ^ (r + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [hpow, ← Complex.ofReal_neg, ← Complex.ofReal_div]
    norm_cast
    field_simp
  have h1 : deriv (ftFiber (ftRootPoly c a) r) ((L : ℝ) : ℂ) = 0 := by
    rw [(hasDerivAt_ftFiber (ftRootPoly c a) hr hLC).deriv, hEC]
    simp
  have h2 : iteratedDeriv 2 (ftFiber (ftRootPoly c a) r) ((L : ℝ) : ℂ) ≠ 0 := by
    rw [hiter]
    exact_mod_cast (by linarith : (2 : ℝ) * κ ≠ 0)
  obtain ⟨H, κ', hκ'v, -, hHa, hH0, hHd, hHeq⟩ :=
    Shields.exists_morse_square (analyticAt_ftFiber (ftRootPoly c a) r hLC) rfl h1 h2
  refine ⟨H, κ, hκneg, hHa, hH0, hHd, ?_⟩
  have hκ'eq : κ' = ((κ : ℝ) : ℂ) := by
    rw [hκ'v, hiter]
    push_cast
    ring
  rw [← hκ'eq]
  exact hHeq

/-! ### The branch value at the endpoint -/

theorem eval_ftRootPoly_ofReal {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (t : ℝ) :
    (ftRootPoly c a).eval ((t : ℝ) : ℂ) = (((ftRootPolyReal c a).eval t : ℝ) : ℂ) := by
  rw [ftRootPoly_eq_map, eval_map_ofReal]

/-- The fiber map at a real point is the real fiber value. -/
theorem ftFiber_ofReal {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {r : ℕ} (t : ℝ) :
    ftFiber (ftRootPoly c a) r ((t : ℝ) : ℂ)
      = ((-((ftRootPolyReal c a).eval t) / t ^ r : ℝ) : ℂ) := by
  rw [ftFiber, eval_ftRootPoly_ofReal]
  push_cast
  ring

/-- **The branch value is the fiber map along the branch point**, which is what
puts the branch inside the level set the Morse coordinate describes. -/
theorem ftFiber_ftBranchPoint {n r l : ℕ} {a : Fin n → ℝ} (c : ℝ) (ha : ∀ k, 0 < a k)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ) :
    ftFiber (ftRootPoly c a) r (ftBranchPoint a r l θ) = ((ftBranchZ a c r l θ : ℝ) : ℂ) :=
  ftZFun_eq c ha hθ h

/-- **The branch point tends to the endpoint.** -/
theorem tendsto_ftBranchPoint_nhdsGT_zero {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) {L : ℝ}
    (hL : Tendsto (ftTau a r l) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (ftBranchPoint a r l) (𝓝[>] (0 : ℝ)) (𝓝 ((L : ℝ) : ℂ)) := by
  have h1 : Tendsto (fun θ => ((ftTau a r l θ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ((L : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto L).comp hL
  have hcont : ContinuousAt (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I)) 0 := by
    fun_prop
  have h2 : Tendsto (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := hcont.tendsto
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have := h1.mul h2
  rw [mul_one] at this
  exact this

/-- **The branch value tends to the fiber value at the endpoint.** -/
theorem tendsto_ftBranchZ_nhdsGT_zero {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hL0 : 0 < L)
    (hL : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (ftBranchZ a c r (n - 1)) (𝓝[>] (0 : ℝ))
      (𝓝 (-((ftRootPolyReal c a).eval L) / L ^ r)) := by
  have hn : 0 < n := by omega
  have hLC : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hrpos : (0 : ℝ) < π / r := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    exact div_pos pi_pos hr0
  have hfib : Tendsto (fun θ => ftFiber (ftRootPoly c a) r (ftBranchPoint a r (n - 1) θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (ftFiber (ftRootPoly c a) r ((L : ℝ) : ℂ))) :=
    ((analyticAt_ftFiber (ftRootPoly c a) r hLC).continuousAt).tendsto.comp
      (tendsto_ftBranchPoint_nhdsGT_zero a r (n - 1) hL)
  have hcong : Tendsto (fun θ => ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (ftFiber (ftRootPoly c a) r ((L : ℝ) : ℂ))) := by
    refine hfib.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hrpos] with θ hθ
    exact ftFiber_ftBranchPoint c ha (ftArc_subset hr hθ)
      (ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ)
  have hre := (Complex.continuous_re.tendsto _).comp hcong
  rw [ftFiber_ofReal] at hre
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  exact hre

/-- **A strictly increasing function on the arc exceeds its one-sided limit.** -/
theorem lt_of_strictMonoOn_of_tendsto {f : ℝ → ℝ} {b z₀ : ℝ} (hb : 0 < b)
    (hmono : StrictMonoOn f (Ioo 0 b)) (hL : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 z₀))
    {θ : ℝ} (hθ : θ ∈ Ioo 0 b) : z₀ < f θ := by
  have hhalf : θ / 2 ∈ Ioo (0 : ℝ) b := ⟨by linarith [hθ.1], by linarith [hθ.1, hθ.2]⟩
  have hle : z₀ ≤ f (θ / 2) := by
    refine le_of_tendsto hL ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < θ / 2 by linarith [hθ.1])] with s hs
    exact (hmono ⟨hs.1, by linarith [hs.2, hhalf.2]⟩ hhalf hs.2).le
  exact lt_of_le_of_lt hle (hmono hhalf hθ (by linarith [hθ.1]))

/-! ### Which arc of the level set the branch runs along -/

theorem ftBranchPoint_re {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) :
    (ftBranchPoint a r l θ).re = ftTau a r l θ * Real.cos θ := by
  simp only [ftBranchPoint, ftArcPoint, exp_neg_ofReal_mul_I, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **A square that is a negative real is purely imaginary.**  This is the whole
content of the two-arc picture: `Im(w²) = 2·Re w·Im w`, so `w² ∈ ℝ` forces one of
the two factors to vanish, and `Re(w²) = Re w² - Im w² < 0` decides which. -/
theorem re_eq_zero_of_sq_ofReal_neg {w : ℂ} {y : ℝ} (hy : y < 0)
    (h : w ^ 2 = ((y : ℝ) : ℂ)) : w.re = 0 := by
  have him : w.re * w.im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.ofReal_im, pow_two, Complex.mul_im] at this
    linarith
  have hre : w.re ^ 2 - w.im ^ 2 = y := by
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, pow_two, Complex.mul_re] at this
    linarith [this]
  rcases mul_eq_zero.1 him with h1 | h2
  · exact h1
  · rw [h2] at hre
    nlinarith [sq_nonneg w.re]

/-- **The Morse chart at the endpoint, with the arc the branch runs along named.**

`exists_morse_endpoint` gives the coordinate; this adds the fact that decides the
geometry — `Re H(γ) = 0` along the branch, so `H(γ)` is purely imaginary and `γ`
is `ψ(is)` for a real parameter `s` once the local inverse is taken.

Split out because the tangent below consumes only the first-order consequence, and
throwing the chart away with it would make every second-order statement start from
`exists_morse_endpoint` again and re-derive which arc the branch is on — which is
the part that costs a sign argument rather than a computation. -/
theorem exists_morse_imaginary_arc {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ} {i : Fin n}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hLi : a i < L)
    (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ (H : ℂ → ℂ) (κ : ℝ), κ < 0 ∧ AnalyticAt ℂ H ((L : ℝ) : ℂ) ∧ H ((L : ℝ) : ℂ) = 0 ∧
      deriv H ((L : ℝ) : ℂ) = 1 ∧
      (∀ᶠ t in 𝓝 ((L : ℝ) : ℂ),
        ftFiber (ftRootPoly c a) r t - ftFiber (ftRootPoly c a) r ((L : ℝ) : ℂ)
          = ((κ : ℝ) : ℂ) * H t ^ 2) ∧
      ∀ᶠ θ in 𝓝[>] (0 : ℝ), (H (ftBranchPoint a r (n - 1) θ)).re = 0 := by
  classical
  have hn : 0 < n := by omega
  have hL0 : 0 < L := lt_trans (ha i) hLi
  have hrpos : (0 : ℝ) < π / r := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    exact div_pos pi_pos hr0
  set g : ℝ → ℂ := ftBranchPoint a r (n - 1) with hgdef
  have hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  have hmono : StrictMonoOn (ftBranchZ a c r (n - 1)) (Ioo 0 (π / r)) :=
    ftBranchZ_strictMonoOn hn ha hc hr ⟨n, by omega⟩ hb
  set z₀ : ℝ := -((ftRootPolyReal c a).eval L) / L ^ r with hz₀def
  have hz₀ : Tendsto (ftBranchZ a c r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 z₀) :=
    tendsto_ftBranchZ_nhdsGT_zero hn2 ha hr hL0 hLt
  have hfibL : ftFiber (ftRootPoly c a) r ((L : ℝ) : ℂ) = ((z₀ : ℝ) : ℂ) := ftFiber_ofReal L
  obtain ⟨H, κ, hκneg, hHa, hH0, hHd, hHeq⟩ :=
    exists_morse_endpoint hn ha hc hr hLi hgap hLe
  have hgL : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 ((L : ℝ) : ℂ)) :=
    tendsto_ftBranchPoint_nhdsGT_zero a r (n - 1) hLt
  -- the branch runs along the imaginary arc
  have hdi : ∀ᶠ θ in 𝓝[>] (0 : ℝ), (H (g θ)).re = 0 := by
    filter_upwards [hgL.eventually hHeq, Ioo_mem_nhdsGT hrpos] with θ hθeq hθarc
    have hval : ftFiber (ftRootPoly c a) r (g θ) = ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ) :=
      ftFiber_ftBranchPoint c ha (ftArc_subset hr hθarc) (hb θ hθarc)
    have hpos : 0 < ftBranchZ a c r (n - 1) θ - z₀ := by
      have := lt_of_strictMonoOn_of_tendsto hrpos hmono hz₀ hθarc
      linarith
    have hsq : H (g θ) ^ 2 = (((ftBranchZ a c r (n - 1) θ - z₀) / κ : ℝ) : ℂ) := by
      rw [hval, hfibL] at hθeq
      have hκ0 : ((κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκneg.ne
      push_cast
      field_simp
      linear_combination -hθeq
    exact re_eq_zero_of_sq_ofReal_neg (div_neg_of_pos_of_neg hpos hκneg) hsq
  exact ⟨H, κ, hκneg, hHa, hH0, hHd, hHeq, hdi⟩

/-- **The branch leaves the endpoint perpendicular to the real axis.**

The branch value is real, so the Morse coordinate's square is real, and the level
set is the union of two arcs — the real one and the imaginary one.  Which arc the
branch is on is settled by a *sign*, not by a local computation: `κ < 0` because
`Q < 0` in the first gap, and `z(θ) > z₀` because the branch value is strictly
increasing across the arc and `z₀` is its one-sided limit.  So `κ H² > 0` forces
`H² < 0`, which is the imaginary arc.

The conclusion is the real part alone; the imaginary part of the branch point is
`-τ sin θ` by construction and needs nothing.

**A consumer wanting only `τ'(0⁺) = 0` should take this rather than the tangent
theorem below.**  With `ftBranchPoint_re` this little-o *is* the slope statement,
one step shorter, and it does not pass through the `ftTauArcAt` extension at all —
so nothing has to be transferred across the endpoint convention to use it. -/
theorem isLittleO_re_ftBranchPoint_sub {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ} {i : Fin n}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hLi : a i < L)
    (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    (fun θ => (ftBranchPoint a r (n - 1) θ).re - L) =o[𝓝[>] (0 : ℝ)] id := by
  classical
  have hn : 0 < n := by omega
  have hL0 : 0 < L := lt_trans (ha i) hLi
  have hrpos : (0 : ℝ) < π / r := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    exact div_pos pi_pos hr0
  set g : ℝ → ℂ := ftBranchPoint a r (n - 1) with hgdef
  have hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  obtain ⟨H, κ, hκneg, hHa, hH0, hHd, hHeq, hdi⟩ :=
    exists_morse_imaginary_arc hn2 ha hc hr hLi hgap hLe hLt
  rw [← hgdef] at hdi
  have hgL : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 ((L : ℝ) : ℂ)) :=
    tendsto_ftBranchPoint_nhdsGT_zero a r (n - 1) hLt
  -- the Morse coordinate is the identity to first order
  have hHderiv : HasDerivAt H 1 ((L : ℝ) : ℂ) := by
    have := hHa.differentiableAt.hasDerivAt
    rwa [hHd] at this
  have hlit : (fun t => H t - (t - ((L : ℝ) : ℂ))) =o[𝓝 ((L : ℝ) : ℂ)]
      fun t => t - ((L : ℝ) : ℂ) := by
    have := hasDerivAt_iff_isLittleO.1 hHderiv
    simpa [hH0, smul_eq_mul] using this
  -- and `τ` is bounded near the endpoint
  have hτbd : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftTau a r (n - 1) θ ≤ L + 1 := by
    have := hLt.eventually (eventually_lt_nhds (show L < L + 1 by linarith))
    exact this.mono fun θ h => h.le
  rw [Asymptotics.isLittleO_iff]
  intro c' hc'
  set M : ℝ := L + 1 with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith
  set ε : ℝ := min (1 / 2) (c' / (2 * M)) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hc' (by linarith))
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεc : ε ≤ c' / (2 * M) := min_le_right _ _
  have hRbd : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      ‖H (g θ) - (g θ - ((L : ℝ) : ℂ))‖ ≤ ε * ‖g θ - ((L : ℝ) : ℂ)‖ :=
    hgL.eventually (Asymptotics.isLittleO_iff.1 hlit hε)
  filter_upwards [hdi, hRbd, hτbd, Ioo_mem_nhdsGT hrpos, self_mem_nhdsWithin] with
    θ hre0 hRθ hτθ hθarc hθpos
  set x : ℝ := (g θ).re - L with hxdef
  set y : ℝ := (g θ).im with hydef
  set N : ℝ := ‖g θ - ((L : ℝ) : ℂ)‖ with hNdef
  have hNre : (g θ - ((L : ℝ) : ℂ)).re = x := by simp [hxdef]
  have hNim : (g θ - ((L : ℝ) : ℂ)).im = y := by simp [hydef]
  have hN2 : N ^ 2 = x ^ 2 + y ^ 2 := by
    rw [hNdef, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hNre, hNim]; ring
  have hN0 : 0 ≤ N := norm_nonneg _
  -- `|x| ≤ ε N`
  have hx : |x| ≤ ε * N := by
    have hcomp : |(H (g θ) - (g θ - ((L : ℝ) : ℂ))).re| ≤ ‖H (g θ) - (g θ - ((L : ℝ) : ℂ))‖ :=
      Complex.abs_re_le_norm _
    have hre : (H (g θ) - (g θ - ((L : ℝ) : ℂ))).re = -x := by
      simp only [Complex.sub_re, hre0, hNre]
      ring
    rw [hre, abs_neg] at hcomp
    exact le_trans hcomp hRθ
  -- so `N ≤ 2|y|`, and `|x| ≤ 2 ε |y|`
  have hx2 : x ^ 2 ≤ ε ^ 2 * N ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at h
    calc x ^ 2 ≤ (ε * N) ^ 2 := h
      _ = ε ^ 2 * N ^ 2 := by ring
  have hε2 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have hy2 : y ^ 2 = N ^ 2 - x ^ 2 := by linarith
  have hNy : N ≤ 2 * |y| := by
    by_contra hcon
    push Not at hcon
    have hyy : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [abs_nonneg y]
  have hxy : |x| ≤ 2 * ε * |y| := by
    calc |x| ≤ ε * N := hx
      _ ≤ ε * (2 * |y|) := mul_le_mul_of_nonneg_left hNy hε.le
      _ = 2 * ε * |y| := by ring
  -- `|y| = τ sin θ ≤ M θ`
  have hθ0 : 0 < θ := hθpos
  have hyval : |y| ≤ M * θ := by
    have him : y = -(ftTau a r (n - 1) θ * Real.sin θ) := by
      rw [hydef, hgdef, ftBranchPoint_im]
    have hτ0 : 0 < ftTau a r (n - 1) θ := ftTau_pos (hb θ hθarc)
    have hsin : Real.sin θ ≤ θ := Real.sin_le hθ0.le
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (le_of_lt (ftArc_subset hr hθarc).2)
    rw [him, abs_neg, abs_of_nonneg (mul_nonneg hτ0.le hsin0)]
    exact mul_le_mul hτθ hsin hsin0 hM.le
  have h2ε : 2 * ε * M ≤ c' := by
    have h := hεc
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * M)] at h
    linarith
  have : |x| ≤ c' * θ := by
    calc |x| ≤ 2 * ε * |y| := hxy
      _ ≤ 2 * ε * (M * θ) := mul_le_mul_of_nonneg_left hyval (by positivity)
      _ = (2 * ε * M) * θ := by ring
      _ ≤ c' * θ := mul_le_mul_of_nonneg_right h2ε hθ0.le
  simpa [Real.norm_eq_abs, hxdef, abs_of_pos hθ0] using this

/-! ### The endpoint tangent -/

/-- **The branch arrives at the endpoint with tangent `L i`.**

`hd0` at a simple smallest zero, in the shape the collar takes at a repeated one
— `HasDerivWithinAt (ftPrincipal (ftTauArcAt …)) v (Ici 0) 0` — but at the
endpoint value `L` this multiplicity actually has, and with the perpendicular
tangent the level-set geometry forces.  The radial slope is `0`: the branch does
not arrive along a ray, it arrives across one. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero_of_simple {n r : ℕ} {a : Fin n → ℝ}
    {c L : ℝ} {i : Fin n} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) (aEnd : ℝ) :
    HasDerivWithinAt (ftPrincipal (ftTauArcAt a r (n - 1) L aEnd))
      (((L : ℝ) : ℂ) * Complex.I) (Ici 0) 0 := by
  classical
  have hn : 0 < n := by omega
  have hL0 : 0 < L := lt_trans (ha i) hLi
  have hrpos : (0 : ℝ) < π / r := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    exact div_pos pi_pos hr0
  -- the two real components
  have h1 : (fun θ => ftTau a r (n - 1) θ * Real.cos θ - L) =o[𝓝[>] (0 : ℝ)] id := by
    have := isLittleO_re_ftBranchPoint_sub hn2 ha hc hr hLi hgap hLe hLt
    refine this.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with θ
    rw [ftBranchPoint_re]
  have hsin : (fun θ : ℝ => Real.sin θ - θ) =o[𝓝[>] (0 : ℝ)] id := by
    have h := hasDerivAt_iff_isLittleO.1 (Real.hasDerivAt_sin 0)
    simp only [Real.sin_zero, Real.cos_zero, sub_zero, smul_eq_mul, mul_one] at h
    exact (h.mono nhdsWithin_le_nhds).congr' (by filter_upwards with θ; ring)
      (by filter_upwards with θ; simp)
  have hτL : Tendsto (fun θ => ftTau a r (n - 1) θ - L) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => L) (𝓝[>] (0 : ℝ)) (𝓝 L) := tendsto_const_nhds
    have := hLt.sub hconst
    simpa using this
  have h2 : (fun θ => ftTau a r (n - 1) θ * Real.sin θ - L * θ) =o[𝓝[>] (0 : ℝ)] id := by
    have hA : (fun θ => (ftTau a r (n - 1) θ - L) * Real.sin θ) =o[𝓝[>] (0 : ℝ)] id := by
      rw [Asymptotics.isLittleO_iff]
      intro c' hc'
      filter_upwards [hτL (Metric.ball_mem_nhds (0 : ℝ) hc'), self_mem_nhdsWithin] with
        θ hθ hθpos
      have hθ0 : 0 < θ := hθpos
      have habs : |ftTau a r (n - 1) θ - L| < c' := by
        simpa [Real.dist_eq] using hθ
      have hs : |Real.sin θ| ≤ |θ| := Real.abs_sin_le_abs
      calc ‖(ftTau a r (n - 1) θ - L) * Real.sin θ‖
          = |ftTau a r (n - 1) θ - L| * |Real.sin θ| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ c' * |θ| := by
            exact mul_le_mul habs.le hs (abs_nonneg _) (le_of_lt (lt_of_le_of_lt
              (abs_nonneg _) habs))
        _ = c' * ‖id θ‖ := by simp [Real.norm_eq_abs]
    have hB : (fun θ : ℝ => L * (Real.sin θ - θ)) =o[𝓝[>] (0 : ℝ)] id := hsin.const_mul_left L
    refine (hA.add hB).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with θ
    ring
  -- assemble
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_isLittleO,
    Asymptotics.isLittleO_iff]
  intro c' hc'
  have hA := Asymptotics.isLittleO_iff.1 h1 (half_pos hc')
  have hB := Asymptotics.isLittleO_iff.1 h2 (half_pos hc')
  have hP0 : ftPrincipal (ftTauArcAt a r (n - 1) L aEnd) 0 = ((L : ℝ) : ℂ) := by
    rw [ftPrincipal, ftTauArcAt_zero a r (n - 1) L aEnd hrpos]
    simp
  filter_upwards [hA, hB, Ioo_mem_nhdsGT hrpos, self_mem_nhdsWithin] with θ hAθ hBθ hθarc hθpos
  have hθ0 : 0 < θ := hθpos
  have hagree : ftTauArcAt a r (n - 1) L aEnd θ = ftTau a r (n - 1) θ :=
    ftTauArcAt_agree a r (n - 1) L aEnd hθ0 hθarc.2
  set A : ℝ := ftTau a r (n - 1) θ * Real.cos θ - L with hAdef
  set B : ℝ := ftTau a r (n - 1) θ * Real.sin θ - L * θ with hBdef
  have hE : ftPrincipal (ftTauArcAt a r (n - 1) L aEnd) θ
      - ftPrincipal (ftTauArcAt a r (n - 1) L aEnd) 0 - (θ - 0) • (((L : ℝ) : ℂ) * Complex.I)
      = ((A : ℝ) : ℂ) + ((B : ℝ) : ℂ) * Complex.I := by
    have hexp : Complex.exp ((θ : ℂ) * Complex.I)
        = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hP0, ftPrincipal, hagree, hexp, hAdef, hBdef]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.real_smul, sub_zero]
    ring
  rw [hE]
  have hnorm : ‖((A : ℝ) : ℂ) + ((B : ℝ) : ℂ) * Complex.I‖ ≤ |A| + |B| := by
    have := Complex.norm_le_abs_re_add_abs_im (((A : ℝ) : ℂ) + ((B : ℝ) : ℂ) * Complex.I)
    simpa using this
  have hAb : |A| ≤ c' / 2 * |θ| := by simpa [Real.norm_eq_abs] using hAθ
  have hBb : |B| ≤ c' / 2 * |θ| := by simpa [Real.norm_eq_abs] using hBθ
  calc ‖((A : ℝ) : ℂ) + ((B : ℝ) : ℂ) * Complex.I‖ ≤ |A| + |B| := hnorm
    _ ≤ c' / 2 * |θ| + c' / 2 * |θ| := add_le_add hAb hBb
    _ = c' * ‖θ - 0‖ := by rw [sub_zero, Real.norm_eq_abs]; ring

/-- **`h0` at a simple smallest zero.**  The tangent is `L i` with `L` above the
smallest zero, so it is nonzero for the same reason the repeated case's is: the
imaginary part is the radius, and the radius is positive. -/
theorem endpointTangent_ne_zero_of_simple {L : ℝ} (hL0 : 0 < L) :
    ((L : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro h
  have him : (((L : ℝ) : ℂ) * Complex.I).im = L := by
    simp
  rw [h] at him
  exact absurd him.symm (ne_of_gt hL0)

/-! ### The producer, and the contrast with the repeated case -/

/-- **The radius is recoverable from the branch point**, so a regularity failure
in `τ` is a regularity failure in `γ` and not something the exponential hides. -/
theorem continuousWithinAt_of_ftPrincipal {τ : ℝ → ℝ} {s : Set ℝ} {θ₀ : ℝ}
    (h : ContinuousWithinAt (ftPrincipal τ) s θ₀) : ContinuousWithinAt τ s θ₀ := by
  have hexp : ContinuousWithinAt (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I)) s θ₀ := by
    fun_prop
  have hmul : ContinuousWithinAt
      (fun θ : ℝ => ftPrincipal τ θ * Complex.exp (-(θ : ℂ) * Complex.I)) s θ₀ := h.mul hexp
  have hre := (Complex.continuous_re.continuousAt).comp_continuousWithinAt hmul
  have heq : ∀ θ : ℝ,
      (Complex.re ∘ fun θ : ℝ => ftPrincipal τ θ * Complex.exp (-(θ : ℂ) * Complex.I)) θ
        = τ θ := by
    intro θ
    simp only [Function.comp_apply, ftPrincipal, mul_assoc, ← Complex.exp_add]
    rw [show (θ : ℂ) * Complex.I + -(θ : ℂ) * Complex.I = 0 by ring]
    simp
  exact hre.congr (fun y _ => (heq y).symm) (heq θ₀).symm

/-- **At a simple smallest zero the repeated case's binder is unsatisfiable in the
collar's own shape.**  `ftTauArcAt … (a i)` is discontinuous at `0`, and the
exponential does not hide it, so there is no value at all for which the collar's
`hd0` holds at the repeated case's endpoint value. -/
theorem not_exists_hasDerivWithinAt_ftPrincipal_min_of_simple {n r : ℕ} {a : Fin n → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) {c : ℝ} (hc : 0 < c) (aEnd : ℝ) :
    ¬ ∃ v : ℂ, HasDerivWithinAt (ftPrincipal (ftTauArcAt a r (n - 1) (a i) aEnd)) v
      (Ici 0) 0 := by
  rintro ⟨v, hv⟩
  exact not_continuousWithinAt_ftTauArcAt_min_of_simple hn2 ha hr hmin hsimple hc aEnd
    (continuousWithinAt_of_ftPrincipal hv.continuousWithinAt)

/-- **The endpoint package at a simple smallest zero.**  Everything the collar asks
of the lower endpoint, at the value the branch actually has there: the endpoint,
its position in the first gap, continuity, the one-sided derivative, its
nonvanishing, and the fact that the endpoint is not a zero of the pencil. -/
theorem exists_endpoint_tangent_of_simple {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) (aEnd : ℝ) :
    ∃ L : ℝ, a i < L ∧ (∀ j, j ≠ i → L < a j) ∧
      ContinuousWithinAt (ftTauArcAt a r (n - 1) L aEnd) (Ici 0) 0 ∧
      HasDerivWithinAt (ftPrincipal (ftTauArcAt a r (n - 1) L aEnd))
        (((L : ℝ) : ℂ) * Complex.I) (Ici 0) 0 ∧
      ((L : ℝ) : ℂ) * Complex.I ≠ 0 ∧
      ∀ k, ftPrincipal (ftTauArcAt a r (n - 1) L aEnd) 0 ≠ ((a k : ℝ) : ℂ) := by
  have hrpos : (0 : ℝ) < π / r := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
    exact div_pos pi_pos hr0
  obtain ⟨L, hLi, hgap, hLt, hLe⟩ :=
    exists_lower_endpoint_of_simple (c := c) hn2 ha hr hmin hsimple hc
  refine ⟨L, hLi, hgap,
    continuousWithinAt_ftTauArcAt_Ici_zero a r (n - 1) aEnd hrpos hLt,
    hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero_of_simple hn2 ha hc hr hLi hgap hLe hLt aEnd,
    endpointTangent_ne_zero_of_simple (lt_trans (ha i) hLi),
    fun k => ftPrincipal_lower_endpoint_ne_root r (n - 1) hrpos hLi hgap k⟩

end ForgacsTran
