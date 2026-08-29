/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EndpointCofactorBound

/-!
# `Im(W'/W)` at one parameter, off a local factorization

`ArcPhaseBound` proves `eq:phase-derivative-bound` region by region and joins the
regions.  What every one of those regions runs on is the estimate at a **single**
parameter, and that is what this module carries: the two facts that reduce
`Im(W'/W)` to a cofactor, and the divided difference that cofactor is written in.

**A zero of the amplitude is invisible to `Im(W'/W)`.**  Both of the amplitude's
factorizations write `W` as a power of a real quantity times a cofactor —
`eq:W-local-zero` as `(θ - θ_j)^{ν_j}U_j(θ)` at an interior zero,
`eq:W-endpoint-form` as `δ^{ν-(k-1)}V(δ)` at an endpoint.  The logarithmic
derivative of the power is `m/(θ - θ_j)`, which is real, so it contributes
nothing to the imaginary part.  A pole of `W'/W` at an amplitude zero is
therefore no obstruction at all, and the estimate is entirely about the cofactor.

**Why the divided difference is centered here and one-sided there.**  An interior
center is approached from both sides, so the cofactor `(γ(θ) - γ(θ₀))/(θ - θ₀)`
has to be estimated on a two-sided collar; the endpoint estimate of
`EndpointCofactorBound` is one-sided and does not give it.  The two are the same
object up to a translation, which is what
`centeredCofactor_eq_shift_right`/`_left` say, so the two-sided estimate is
assembled from the one-sided one on each side rather than proved again.

## Main statements

* `logDeriv_congr_of_eventuallyEq` — `logDeriv` is local, which is what lets an
  eventual factorization be used at a point.
* `im_logDeriv_ofRealSub_zpow` — the real power contributes `0`.
* `im_logDeriv_local_factorization`,
  `abs_im_logDeriv_le_of_local_factorization_outer`,
  `abs_im_logDeriv_le_of_local_factorization` — `Im(W'/W) = p·Im(u'/u) + Im(A'/A)`
  off a local factorization `W = c·(s-θ₀)^m·u(s)^p·A(s)`, and the two bounds that
  follow, according as the outer factor is supplied as a bound or as a quotient.
* `centeredCofactor_eq_shift_right`, `centeredCofactor_eq_shift_left` — the
  centered divided difference is the endpoint one translated, on each side.
* `exists_bound_im_logDeriv_centeredCofactor` — the divided-difference estimate on
  a two-sided collar, which is what an interior center needs.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `eq:W-local-zero`,
`eq:W-endpoint-form`, `eq:phase-derivative-bound`).

## Tags

phase derivative, logarithmic derivative, local factorization, divided difference
-/
namespace ForgacsTran

open Set

/-! ### The imaginary part sees a real power as nothing -/

/-- `logDeriv` is local, so an eventual identity at a point transfers it. -/
theorem logDeriv_congr_of_eventuallyEq {W F : ℝ → ℂ} {θ : ℝ} (h : W =ᶠ[nhds θ] F) :
    logDeriv W θ = logDeriv F θ := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

private theorem hasDerivAt_ofRealSub (θ₀ θ : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) - (θ₀ : ℂ)) 1 θ := by
  simpa using ((hasDerivAt_id θ).ofReal_comp).sub_const ((θ₀ : ℂ))

theorem differentiableAt_ofRealSub_zpow (θ₀ : ℝ) (m : ℤ) {θ : ℝ} (hθ : θ ≠ θ₀) :
    DifferentiableAt ℝ (fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ m) θ := by
  have hne : ((θ : ℂ) - (θ₀ : ℂ)) ≠ 0 := by
    simpa [sub_eq_zero, Complex.ofReal_inj] using hθ
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z ^ m) ((θ : ℂ) - (θ₀ : ℂ)) :=
    differentiableAt_zpow.2 (Or.inl hne)
  exact (h1.restrictScalars ℝ).comp θ (hasDerivAt_ofRealSub θ₀ θ).differentiableAt

/-- **The real power drops out of the imaginary part.**  `(s - θ₀)^m` has
logarithmic derivative `m/(s - θ₀)`, and both `m` and `s - θ₀` are real, so the
term is real and contributes nothing.  This is why a zero of the amplitude —
which is exactly such a factor — does not obstruct a bound on `Im(W'/W)`. -/
theorem im_logDeriv_ofRealSub_zpow (θ₀ : ℝ) (m : ℤ) {θ : ℝ} (hθ : θ ≠ θ₀) :
    (logDeriv (fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ m) θ).im = 0 := by
  have hne : ((θ : ℂ) - (θ₀ : ℂ)) ≠ 0 := by
    simpa [sub_eq_zero, Complex.ofReal_inj] using hθ
  rw [logDeriv_fun_zpow (hasDerivAt_ofRealSub θ₀ θ).differentiableAt m, logDeriv_apply,
    (hasDerivAt_ofRealSub θ₀ θ).deriv]
  have hreal : (m : ℂ) * (1 / ((θ : ℂ) - (θ₀ : ℂ)))
      = (((m : ℝ) * (1 / (θ - θ₀)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hreal, Complex.ofReal_im]

/-! ### The local factorization, as a bound -/

/-- **`Im(W'/W)` off a local factorization.**  Where `W = c·(s-θ₀)^m·u(s)^p·A(s)`
near `θ`, the imaginary part of the logarithmic derivative is
`p·Im(u'/u) + Im(A'/A)`: the constant drops out of every logarithmic derivative
and the real power drops out of every imaginary part.

`m` and `p` are separate integers because they are separate at the amplitude —
`eq:W-endpoint-form` carries `δ^{ν-(k-1)}` against a divided difference to the
same power, while `eq:W-local-zero` carries `(θ-θ_j)^{ν_j}` against one to the
power `ν_j`, and nothing forces the two to agree in general. -/
theorem im_logDeriv_local_factorization {u A : ℝ → ℂ} {c : ℂ} {θ₀ θ : ℝ} {m p : ℤ}
    (hθ : θ ≠ θ₀) (hc : c ≠ 0)
    (hud : DifferentiableAt ℝ u θ) (hu0 : u θ ≠ 0)
    (hAd : DifferentiableAt ℝ A θ) (hA0 : A θ ≠ 0) :
    (logDeriv (fun s : ℝ => c * ((s : ℂ) - (θ₀ : ℂ)) ^ m * (u s) ^ p * A s) θ).im
      = (p : ℝ) * (logDeriv u θ).im + (logDeriv A θ).im := by
  have hne : ((θ : ℂ) - (θ₀ : ℂ)) ≠ 0 := by
    simpa [sub_eq_zero, Complex.ofReal_inj] using hθ
  rw [im_logDeriv_endpoint_factorization (γ := fun s : ℝ => ((s : ℂ) - (θ₀ : ℂ)) ^ m)
      hc (differentiableAt_ofRealSub_zpow θ₀ m hθ) (zpow_ne_zero _ hne) hud hu0 hAd hA0,
    im_logDeriv_ofRealSub_zpow θ₀ m hθ, zero_add]

/-- **The same bound with the outer factor supplied as a bound rather than a
quotient.**  `abs_im_logDeriv_le_of_local_factorization` bounds the outer term by
`‖A'‖/‖A‖`, which asks for `A'` itself.  At the amplitude the outer factor is a
product and a quotient of polynomial compositions, whose *logarithmic* derivative
splits term by term while its derivative does not — so the bound is the thing to
take as the hypothesis, and the derivative never has to be assembled. -/
theorem abs_im_logDeriv_le_of_local_factorization_outer {W u A : ℝ → ℂ} {c : ℂ}
    {θ₀ θ : ℝ} {m p : ℤ} {κ κ' : ℝ} (hθ : θ ≠ θ₀) (hc : c ≠ 0)
    (hW : W =ᶠ[nhds θ] fun s : ℝ => c * ((s : ℂ) - (θ₀ : ℂ)) ^ m * (u s) ^ p * A s)
    (hud : DifferentiableAt ℝ u θ) (hu0 : u θ ≠ 0)
    (hAd : DifferentiableAt ℝ A θ) (hA0 : A θ ≠ 0)
    (hmid : |(logDeriv u θ).im| ≤ κ) (houter : |(logDeriv A θ).im| ≤ κ') :
    |(deriv W θ / W θ).im| ≤ |(p : ℝ)| * κ + κ' := by
  have hLD : (deriv W θ / W θ).im
      = (p : ℝ) * (logDeriv u θ).im + (logDeriv A θ).im := by
    rw [show deriv W θ / W θ = logDeriv W θ from rfl, logDeriv_congr_of_eventuallyEq hW,
      im_logDeriv_local_factorization hθ hc hud hu0 hAd hA0]
  rw [hLD]
  have h2 : |(p : ℝ) * (logDeriv u θ).im| ≤ |(p : ℝ)| * κ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
  calc |(p : ℝ) * (logDeriv u θ).im + (logDeriv A θ).im|
      ≤ |(p : ℝ) * (logDeriv u θ).im| + |(logDeriv A θ).im| := abs_add_le _ _
    _ ≤ |(p : ℝ)| * κ + κ' := by gcongr

/-- **The same, as the bound the arc assembly consumes.**  Only the divided
difference is delicate; the outer factor neither vanishes nor blows up, so its
logarithmic derivative is bounded with no cancellation argument.

The factorization is taken as an *eventual* identity at `θ`, which is the form
`Amplitude`'s two factorizations conclude in — they hold on a neighbourhood of
the center, not identically — and `logDeriv` is local, so nothing is lost. -/
theorem abs_im_logDeriv_le_of_local_factorization {W u A : ℝ → ℂ} {c : ℂ} {θ₀ θ : ℝ}
    {m p : ℤ} {κ : ℝ} (hθ : θ ≠ θ₀) (hc : c ≠ 0)
    (hW : W =ᶠ[nhds θ] fun s : ℝ => c * ((s : ℂ) - (θ₀ : ℂ)) ^ m * (u s) ^ p * A s)
    (hud : DifferentiableAt ℝ u θ) (hu0 : u θ ≠ 0)
    (hAd : DifferentiableAt ℝ A θ) (hA0 : A θ ≠ 0)
    (hmid : |(logDeriv u θ).im| ≤ κ) :
    |(deriv W θ / W θ).im| ≤ |(p : ℝ)| * κ + ‖deriv A θ‖ / ‖A θ‖ :=
  abs_im_logDeriv_le_of_local_factorization_outer hθ hc hW hud hu0 hAd hA0 hmid
    (abs_im_logDeriv_le A θ)

/-! ### The divided difference at an interior center, on both sides -/

/-- The centered divided difference is the endpoint one, translated. -/
theorem centeredCofactor_eq_shift_right (γ : ℝ → ℂ) (θ₀ θ : ℝ) :
    centeredCofactor γ θ₀ θ
      = endpointCofactor (fun t : ℝ => γ (t + θ₀) - γ θ₀) (θ - θ₀) := by
  simp [centeredCofactor, endpointCofactor, Complex.ofReal_sub]

/-- The same on the other side, where the reflected branch is what the endpoint
estimate sees and the sign of the divided difference flips with it. -/
theorem centeredCofactor_eq_shift_left (γ : ℝ → ℂ) (θ₀ θ : ℝ) :
    centeredCofactor γ θ₀ θ
      = -endpointCofactor (fun t : ℝ => γ (θ₀ - t) - γ θ₀) (θ₀ - θ) := by
  rw [centeredCofactor, endpointCofactor]
  simp only [sub_sub_cancel]
  rw [← div_neg, Complex.ofReal_sub, neg_sub]

/-- **The cofactor estimate at an interior center, on a two-sided collar.**
`EndpointCofactorBound.exists_bound_im_centeredCofactor_logDeriv` reaches
`[θ₀, θ₀+b']` only, because it is the endpoint estimate translated and the
endpoint has one side.  An interior amplitude zero has two, and
`BoundAssembly.exists_bound_of_finite_exceptional` asks for `|θ - z| < δ` — a
ball, not a half-collar — so the left side is owed rather than optional.

**The left side is the same estimate at the reflected branch**, not a second
estimate: `t ↦ γ(θ₀ - t) - γ(θ₀)` meets every hypothesis the right side does,
with `L` unchanged and `γ'` negated, and negating `γ'` moves neither `‖γ'(θ₀)‖`
nor the constant `3L/‖γ'(θ₀)‖`.  What the reflection does move is a sign: the
divided difference itself flips, and so does its logarithmic derivative, which is
why the two sides land on the same bound only after an absolute value.

`hlip` carries `|θ - θ₀|` rather than `θ - θ₀`, which is the one hypothesis that
genuinely has to be restated for two sides — the one-sided form is vacuous to the
left of the center, where `θ - θ₀ < 0` and no norm is `≤` it. -/
theorem exists_bound_im_logDeriv_centeredCofactor {γ dγ : ℝ → ℂ} {θ₀ b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hd : ∀ θ ∈ Icc (θ₀ - b) (θ₀ + b), HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (θ₀ - b) (θ₀ + b), ‖dγ θ - dγ θ₀‖ ≤ L * |θ - θ₀|)
    (h0 : dγ θ₀ ≠ 0) :
    ∃ b' : ℝ, 0 < b' ∧ b' ≤ b ∧
      (∀ θ, |θ - θ₀| ≤ b' → θ ≠ θ₀ → centeredCofactor γ θ₀ θ ≠ 0) ∧
      (∀ θ, |θ - θ₀| ≤ b' → θ ≠ θ₀ → DifferentiableAt ℝ (centeredCofactor γ θ₀) θ) ∧
      (∀ θ, |θ - θ₀| ≤ b' → θ ≠ θ₀ →
        |(logDeriv (centeredCofactor γ θ₀) θ).im| ≤ 3 * L / ‖dγ θ₀‖) := by
  have hθ₀mem : θ₀ ∈ Icc (θ₀ - b) (θ₀ + b) := ⟨by linarith, by linarith⟩
  -- the right half: the branch translated so the center sits at the origin
  set g : ℝ → ℂ := fun t : ℝ => γ (t + θ₀) - γ θ₀ with hgdef
  set dg : ℝ → ℂ := fun t : ℝ => dγ (t + θ₀) with hdgdef
  have hdg0 : dg 0 = dγ θ₀ := by simp [hdgdef]
  have hgd0 : HasDerivWithinAt g (dg 0) (Ici (0 : ℝ)) 0 := by
    rw [hdg0]
    have hcomp : HasDerivAt (fun u : ℝ => γ (u + θ₀)) (dγ θ₀) 0 :=
      HasDerivAt.comp_add_const (0 : ℝ) θ₀ (by simpa using hd θ₀ hθ₀mem)
    simpa [hgdef] using (hcomp.sub_const (γ θ₀)).hasDerivWithinAt
  have hgd : ∀ t ∈ Ioc (0 : ℝ) b, HasDerivAt g (dg t) t := by
    intro t ht
    have hmem : t + θ₀ ∈ Icc (θ₀ - b) (θ₀ + b) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hcomp : HasDerivAt (fun u : ℝ => γ (u + θ₀)) (dγ (t + θ₀)) t :=
      HasDerivAt.comp_add_const t θ₀ (hd _ hmem)
    simpa [hgdef, hdgdef] using hcomp.sub_const (γ θ₀)
  have hglip : ∀ t ∈ Icc (0 : ℝ) b, ‖dg t - dg 0‖ ≤ L * t := by
    intro t ht
    have hmem : t + θ₀ ∈ Icc (θ₀ - b) (θ₀ + b) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := hlip _ hmem
    rw [show t + θ₀ - θ₀ = t by ring, abs_of_nonneg ht.1] at h
    simpa [hdgdef, hdg0] using h
  obtain ⟨b₁, hb₁0, hb₁b, hne₁, hderiv₁, hbd₁⟩ :=
    exists_bound_im_endpointCofactor_logDeriv hb hL (by simp [hgdef]) hgd0 hgd hglip
      (by rwa [hdg0])
  -- the left half: the same estimate at the reflected branch
  set g' : ℝ → ℂ := fun t : ℝ => γ (θ₀ - t) - γ θ₀ with hg'def
  set dg' : ℝ → ℂ := fun t : ℝ => -dγ (θ₀ - t) with hdg'def
  have hdg'0 : dg' 0 = -dγ θ₀ := by simp [hdg'def]
  have hg'd0 : HasDerivWithinAt g' (dg' 0) (Ici (0 : ℝ)) 0 := by
    rw [hdg'0]
    have hcomp : HasDerivAt (fun u : ℝ => γ (θ₀ - u)) (-dγ θ₀) 0 :=
      HasDerivAt.comp_const_sub θ₀ (0 : ℝ) (by simpa using hd θ₀ hθ₀mem)
    simpa [hg'def] using (hcomp.sub_const (γ θ₀)).hasDerivWithinAt
  have hg'd : ∀ t ∈ Ioc (0 : ℝ) b, HasDerivAt g' (dg' t) t := by
    intro t ht
    have hmem : θ₀ - t ∈ Icc (θ₀ - b) (θ₀ + b) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hcomp : HasDerivAt (fun u : ℝ => γ (θ₀ - u)) (-dγ (θ₀ - t)) t :=
      HasDerivAt.comp_const_sub θ₀ t (hd _ hmem)
    simpa [hg'def, hdg'def] using hcomp.sub_const (γ θ₀)
  have hg'lip : ∀ t ∈ Icc (0 : ℝ) b, ‖dg' t - dg' 0‖ ≤ L * t := by
    intro t ht
    have hmem : θ₀ - t ∈ Icc (θ₀ - b) (θ₀ + b) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := hlip _ hmem
    rw [show θ₀ - t - θ₀ = -t by ring, abs_neg, abs_of_nonneg ht.1] at h
    have hrw : dg' t - dg' 0 = -(dγ (θ₀ - t) - dγ θ₀) := by
      simp only [hdg'def, sub_zero]
      ring
    rw [hrw, norm_neg]
    exact h
  obtain ⟨b₂, hb₂0, hb₂b, hne₂, hderiv₂, hbd₂⟩ :=
    exists_bound_im_endpointCofactor_logDeriv hb hL (by simp [hg'def]) hg'd0 hg'd hg'lip
      (by rw [hdg'0]; simpa using h0)
  have hnorm' : ‖dg' 0‖ = ‖dγ θ₀‖ := by rw [hdg'0, norm_neg]
  refine ⟨min b₁ b₂, lt_min hb₁0 hb₂0, le_trans (min_le_left _ _) hb₁b, ?_, ?_, ?_⟩
  -- the three clauses, each by the side the parameter falls on
  all_goals
    intro θ hθ hθ0
  all_goals
    rcases lt_or_gt_of_ne (sub_ne_zero.2 hθ0) with hlt | hgt
  -- LEFT side, `θ < θ₀`: the reflected estimate at `t = θ₀ - θ`
  · have hmem : θ₀ - θ ∈ Icc (0 : ℝ) b₂ := by
      constructor
      · linarith
      · have := le_trans hθ (min_le_right b₁ b₂)
        rw [abs_of_nonpos hlt.le] at this
        linarith
    have hne : θ₀ - θ ≠ 0 := by intro h; apply hθ0; linarith
    rw [centeredCofactor_eq_shift_left]
    exact neg_ne_zero.2 (hne₂ _ hmem hne)
  -- RIGHT side, `θ > θ₀`
  · have hmem : θ - θ₀ ∈ Icc (0 : ℝ) b₁ := by
      constructor
      · linarith
      · have := le_trans hθ (min_le_left b₁ b₂)
        rwa [abs_of_nonneg hgt.le] at this
    rw [centeredCofactor_eq_shift_right]
    exact hne₁ _ hmem (sub_ne_zero.2 hθ0)
  · have hmem : θ₀ - θ ∈ Icc (0 : ℝ) b₂ := by
      constructor
      · linarith
      · have := le_trans hθ (min_le_right b₁ b₂)
        rw [abs_of_nonpos hlt.le] at this
        linarith
    have hne : θ₀ - θ ≠ 0 := by intro h; apply hθ0; linarith
    have hfun : centeredCofactor γ θ₀
        = fun x : ℝ => -endpointCofactor g' (θ₀ - x) :=
      funext fun x => centeredCofactor_eq_shift_left γ θ₀ x
    rw [hfun]
    exact (((hderiv₂ _ hmem hne).comp_const_sub θ₀ θ).neg).differentiableAt
  · have hmem : θ - θ₀ ∈ Icc (0 : ℝ) b₁ := by
      constructor
      · linarith
      · have := le_trans hθ (min_le_left b₁ b₂)
        rwa [abs_of_nonneg hgt.le] at this
    have hfun : centeredCofactor γ θ₀
        = fun x : ℝ => endpointCofactor g (x - θ₀) :=
      funext fun x => centeredCofactor_eq_shift_right γ θ₀ x
    rw [hfun]
    exact ((hderiv₁ _ hmem (sub_ne_zero.2 hθ0)).comp_sub_const θ θ₀).differentiableAt
  · have hmem : θ₀ - θ ∈ Icc (0 : ℝ) b₂ := by
      constructor
      · linarith
      · have := le_trans hθ (min_le_right b₁ b₂)
        rw [abs_of_nonpos hlt.le] at this
        linarith
    have hne : θ₀ - θ ≠ 0 := by intro h; apply hθ0; linarith
    have hfun : centeredCofactor γ θ₀
        = fun x : ℝ => -endpointCofactor g' (θ₀ - x) :=
      funext fun x => centeredCofactor_eq_shift_left γ θ₀ x
    have hderiv : HasDerivAt (centeredCofactor γ θ₀)
        (endpointCofactorDeriv g' dg' (θ₀ - θ)) θ := by
      rw [hfun]
      have hchain := ((hderiv₂ _ hmem hne).comp_const_sub θ₀ θ).neg
      rwa [neg_neg] at hchain
    rw [logDeriv_apply, hderiv.deriv, centeredCofactor_eq_shift_left, div_neg,
      Complex.neg_im, abs_neg, ← hnorm']
    exact hbd₂ _ hmem hne
  · have hmem : θ - θ₀ ∈ Icc (0 : ℝ) b₁ := by
      constructor
      · linarith
      · have := le_trans hθ (min_le_left b₁ b₂)
        rwa [abs_of_nonneg hgt.le] at this
    have hfun : centeredCofactor γ θ₀
        = fun x : ℝ => endpointCofactor g (x - θ₀) :=
      funext fun x => centeredCofactor_eq_shift_right γ θ₀ x
    have hderiv : HasDerivAt (centeredCofactor γ θ₀)
        (endpointCofactorDeriv g dg (θ - θ₀)) θ := by
      rw [hfun]
      exact (hderiv₁ _ hmem (sub_ne_zero.2 hθ0)).comp_sub_const θ θ₀
    rw [logDeriv_apply, hderiv.deriv, centeredCofactor_eq_shift_right, ← hdg0]
    exact hbd₁ _ hmem (sub_ne_zero.2 hθ0)

end ForgacsTran
