/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EndpointCofactorBound
import ForgacsTran.Amplitude
import ForgacsTran.ArcPhaseLocal

/-!
# The arc-wide bound on `Im(W'/W)`

`AngularDiscrepancyFT.FTPhaseSupply`'s branch hypothesis asks three things of
every block of an arbitrary ordered family placed anywhere in `[0, π/r]`, and
`EndpointCofactorBound.exists_phase_family_of_bound` supplies all three from a
**single** bound on `Im(W'/W)` over the whole arc.  That bound is proved region
by region — a collar at each end and the interior — and this module is what joins
the regions to the amplitude's own factorizations and to each other.

The estimate at a single parameter is `ArcPhaseLocal`'s: a zero of the amplitude
is a real power, so it is invisible to `Im(W'/W)` and the whole estimate reduces
to the cofactor.  What is here is everything above that — the amplitude's own
factorizations at an interior zero, at a finite endpoint and at the origin, the
per-zero bounds turned into one constant across the divisor, and the composition
into `hbranch`'s clauses.

## Main statements

* `abs_im_logDeriv_polyQuotient_le` — the outer factor both factorizations leave
  behind, bounded by `‖γ'‖` against three quantities continuous along the branch.
* `ftAmp_eq_local_factorization`,
  `exists_bound_im_logDeriv_ftAmp_interior` — `eq:W-local-zero` with the divided
  difference visible, and the bound on a punctured ball about an interior
  amplitude zero that follows from it.
* `ftAmp_eq_endpoint_factorization`,
  `exists_bound_im_logDeriv_ftAmp_endpoint` — the same at a finite endpoint, where
  the `z`-free factor degenerates too and the power carried is the integer
  `ν - (k-1)` rather than the natural number `ν`.
* `abs_im_logDeriv_polyRatio_le`, `ftAmp_eq_origin_factorization`,
  `exists_bound_im_logDeriv_ftAmp_origin` — the upper endpoint of an `r ≥ 2` arc,
  where the branch runs into the **origin**.  `t_e = 0` there, which is what
  `FTBranchUpperRefutation.not_upper_endpoint_datum_ne_zero` refutes `t_e ≠ 0`
  with, so the finite-endpoint route does not reach it and this is a separate
  factorization rather than a special case — the exponent is `1`
  unconditionally and the branch is itself the degenerating factor.
* `abs_le_of_cover_three_of_ne_zero` — `BoundAssembly.abs_le_of_cover_three`
  through the nonvanishing guard the arc bound carries.
* `norm_deriv_sub_le_of_norm_deriv2_le_centered`,
  `exists_bound_im_logDeriv_ftAmp_interior_of_deriv2` — the interior bound asking
  what the branch modules carry (`γ` and `γ'` differentiable, `γ''` continuous at
  the center) rather than a collar and a Lipschitz constant built by hand.
* `exists_bound_of_local_on_divisor`,
  `exists_bound_im_logDeriv_ftAmp_interiorRegion`,
  `exists_bound_im_logDeriv_ftAmp_interiorRegion_of_deriv2` — the per-zero bounds
  turned into one constant across the whole divisor, by either route.
* `forall_Icc_of_Ioc_of_eq_zero`, `forall_Icc_of_Ico_of_eq_zero` — **the two seams
  the region binders no longer have.**  They bridged a collar bound on the punctured
  side to a region bound asked on the closed interval, at the cost of `W(0) = 0`,
  which is a real obligation and not free.  `BranchSupply` now asks its first region
  on `Ioc` and its third on `Ico`, so the collar's own interval *is* the binder's and
  neither bridge is crossed.  Kept as the record of what the closed form cost.
* `im_logDeriv_reflect`, `forall_Ico_of_reflected` — the upper endpoint read as
  the lower one reflected, the chain rule's sign dying under the absolute value.
* `exists_phase_family_of_regions` — the three region bounds composed into
  `hbranch`'s first three clauses, with the threshold fixed before the family.
* `exists_phase_family_hasDerivAt_of_bound_of_open`,
  `exists_phase_family_hasDerivAt_of_regions_of_open` — the same with the
  derivative data asked on the OPEN arc, which is what the amplitude has: where
  `E` degenerates at an endpoint `W` blows up there and is not differentiable, so
  the closed-arc binder cannot be met.  The nonvanishing the blocks already carry
  is what pushes every admissible block off the endpoints.  **The phase derivative
  is named in the conclusion**, as `Im(W'/W)`, so a consumer that also needs the
  variation of `ψ` reads it off rather than re-deriving it.
* `exists_phase_family_of_bound_of_open`,
  `exists_phase_family_of_regions_of_open` — those two with `ψ'` under its own
  existential, which is the shape `AngularDiscrepancyFT.FTPhaseSupply` states.
* `exists_bound_im_chord_at_meet`, `exists_bound_im_chord_of_miss`,
  `exists_bound_im_chord_at_collision` — the per-root term of the numerator's logarithmic
  derivative, bounded in the three states a root of `B` can be in relative to the arc:
  missed, met inside, met at a collision.  The third is a separate case for the estimate
  rather than for the geometry, because only one side of the parameter exists there.  With
  `PhaseBranchSplit.im_logDeriv_factorization` these are the general region bounds'
  numerator half, one root at a time.
* `exists_bound_im_logDeriv_ftAmp_interior_witness`,
  `exists_bound_im_logDeriv_ftAmp_endpoint_witness` — the two bundles discharged
  at an explicit pencil: the interior one at a parameter where the amplitude
  really vanishes, the endpoint one at `m = 0`, which is the boundary value of
  the exponent parameter.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `eq:W-local-zero`,
`eq:W-endpoint-form`, `eq:phase-derivative-bound`).

## Tags

phase derivative, logarithmic derivative, amplitude divisor, uniformity
-/
namespace ForgacsTran

open Set

/-! ### The three regions, assembled -/

/-- **`abs_le_of_cover_three` through the nonvanishing guard.**  The arc bound is
not a bound on a function of `θ` alone: it is asserted only where `W(θ) ≠ 0`,
because `Im(W'/W)` is not defined — in the mathematics, not in Lean — at a zero
of the amplitude.  Intersecting each region with `{W ≠ 0}` keeps the cover exact,
so the seam guarantee of `Icc_subset_cover_three` survives the guard. -/
theorem abs_le_of_cover_three_of_ne_zero {W : ℝ → ℂ} {f : ℝ → ℝ}
    {L b₁ b₂ κ₁ κ₂ κ₃ : ℝ}
    (h₁ : ∀ s ∈ Icc (0 : ℝ) b₁, W s ≠ 0 → |f s| ≤ κ₁)
    (h₂ : ∀ s ∈ Icc b₁ b₂, W s ≠ 0 → |f s| ≤ κ₂)
    (h₃ : ∀ s ∈ Icc b₂ L, W s ≠ 0 → |f s| ≤ κ₃) :
    ∀ s ∈ Icc (0 : ℝ) L, W s ≠ 0 → |f s| ≤ max κ₁ (max κ₂ κ₃) := by
  have hcov : Icc (0 : ℝ) L ∩ {s | W s ≠ 0}
      ⊆ (Icc (0 : ℝ) b₁ ∩ {s | W s ≠ 0}) ∪ (Icc b₁ b₂ ∩ {s | W s ≠ 0})
        ∪ (Icc b₂ L ∩ {s | W s ≠ 0}) := by
    intro x hx
    rcases Icc_subset_cover_three b₁ b₂ hx.1 with (h | h) | h
    · exact Or.inl (Or.inl ⟨h, hx.2⟩)
    · exact Or.inl (Or.inr ⟨h, hx.2⟩)
    · exact Or.inr ⟨h, hx.2⟩
  intro s hs hW
  exact abs_le_of_cover_three hcov (fun x hx => h₁ x hx.1 hx.2) (fun x hx => h₂ x hx.1 hx.2)
    (fun x hx => h₃ x hx.1 hx.2) s ⟨hs, hW⟩

/-- **The arc-wide bound, from the three regions, in the shape `hbranch` wants.**
`exists_phase_family_of_bound` turns a single arc-wide `κ` into the first three
clauses of `AngularDiscrepancyFT.FTPhaseSupply`'s branch hypothesis for an
arbitrary ordered family of blocks, with the threshold `M₀` fixed before the
family is seen.  This is that composed with the cover, so what a caller owes is
one bound per region and nothing about blocks at all.

**Not the one to compose against at the amplitude.**  Its derivative data is asked on an
open set containing the **closed** arc, and at the Forgács–Tran amplitude that binder
cannot be met at `L = π/r` — where `E` degenerates `W` blows up and no derivative exists
there.  `exists_phase_family_hasDerivAt_of_regions_of_open` and
`exists_phase_family_of_regions_of_open` are the twins that ask on the open arc and are
what the amplitude reaches; this one is for a `W` that is genuinely differentiable at both
ends. -/
theorem exists_phase_family_of_regions {W dW : ℝ → ℂ} {U : Set ℝ} {L b₁ b₂ κ₁ κ₂ κ₃ : ℝ}
    (hU : IsOpen U) (hsub : Icc (0 : ℝ) L ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (h₁ : ∀ s ∈ Icc (0 : ℝ) b₁, W s ≠ 0 → |(dW s / W s).im| ≤ κ₁)
    (h₂ : ∀ s ∈ Icc b₁ b₂, W s ≠ 0 → |(dW s / W s).im| ≤ κ₂)
    (h₃ : ∀ s ∈ Icc b₂ L, W s ≠ 0 → |(dW s / W s).im| ≤ κ₃) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) L) → (∀ i, Rb i ∈ Icc (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) →
      ∃ ψ dψ : Fin k → ℝ → ℝ,
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = ((‖W θ‖ : ℝ) : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) :=
  exists_phase_family_of_bound hU hsub hd hc
    (abs_le_of_cover_three_of_ne_zero h₁ h₂ h₃)

/-! ### The interior, at the amplitude's own factorization -/

/-- The divided difference clears the denominator, at every parameter — at the
center too, where both sides are `0` and neither is the quotient. -/
theorem sub_eq_mul_centeredCofactor (γ : ℝ → ℂ) (θ₀ θ : ℝ) :
    γ θ - γ θ₀ = ((θ : ℂ) - (θ₀ : ℂ)) * centeredCofactor γ θ₀ θ := by
  rcases eq_or_ne θ θ₀ with rfl | hθ
  · simp
  · have hne : ((θ : ℂ) - (θ₀ : ℂ)) ≠ 0 := by
      simpa [sub_eq_zero, Complex.ofReal_inj] using hθ
    rw [centeredCofactor, mul_div_cancel₀ _ hne]

/-- The derivative of a polynomial along the branch. -/
theorem hasDerivAt_eval_comp {γ dγ : ℝ → ℂ} {θ : ℝ} (P : Polynomial ℂ)
    (hd : HasDerivAt γ (dγ θ) θ) :
    HasDerivAt (fun s : ℝ => P.eval (γ s)) (dγ θ * (Polynomial.derivative P).eval (γ θ)) θ := by
  simpa [Function.comp_def, smul_eq_mul] using (P.hasDerivAt (γ θ)).scomp θ hd

/-- **The outer factor of both factorizations, bounded.**  `eq:W-local-zero` and
`eq:W-endpoint-form` leave the same shape behind once the degenerating factor is
split off: `γ` times a polynomial along `γ`, over a polynomial along `γ`, with
both polynomials nonvanishing at the point.  Its *logarithmic* derivative splits
term by term while its derivative does not, so the three logarithmic derivatives
are bounded separately and `γ'` is what they share.

**Only `‖γ'‖` is asked of the branch.**  The three remaining quantities are
continuous wherever `γ` is, so a caller bounds them by continuity at the center
and bounds `‖γ'‖` by its Lipschitz binder — no continuity of `γ'` enters. -/
theorem abs_im_logDeriv_polyQuotient_le {γ dγ : ℝ → ℂ} {θ : ℝ} (P₁ P₂ : Polynomial ℂ)
    (hd : HasDerivAt γ (dγ θ) θ) (hγ : γ θ ≠ 0)
    (h1 : P₁.eval (γ θ) ≠ 0) (h2 : P₂.eval (γ θ) ≠ 0) :
    |(logDeriv (fun s : ℝ => γ s * P₁.eval (γ s) / P₂.eval (γ s)) θ).im|
      ≤ ‖dγ θ‖ * (1 / ‖γ θ‖ + ‖(Polynomial.derivative P₁).eval (γ θ)‖ / ‖P₁.eval (γ θ)‖
          + ‖(Polynomial.derivative P₂).eval (γ θ)‖ / ‖P₂.eval (γ θ)‖) := by
  have hd1 := hasDerivAt_eval_comp P₁ hd
  have hd2 := hasDerivAt_eval_comp P₂ hd
  have hsplit : logDeriv (fun s : ℝ => γ s * P₁.eval (γ s) / P₂.eval (γ s)) θ
      = (logDeriv γ θ + logDeriv (fun s : ℝ => P₁.eval (γ s)) θ)
        - logDeriv (fun s : ℝ => P₂.eval (γ s)) θ := by
    rw [logDeriv_div (f := fun s : ℝ => γ s * P₁.eval (γ s))
        (g := fun s : ℝ => P₂.eval (γ s)) θ (mul_ne_zero hγ h1) h2
        (hd.differentiableAt.mul hd1.differentiableAt) hd2.differentiableAt,
      logDeriv_mul (f := γ) (g := fun s : ℝ => P₁.eval (γ s)) θ hγ h1
        hd.differentiableAt hd1.differentiableAt]
  have b1 : |(logDeriv γ θ).im| ≤ ‖dγ θ‖ * (1 / ‖γ θ‖) := by
    have h := abs_im_logDeriv_le γ θ
    rwa [hd.deriv, div_eq_mul_one_div] at h
  have b2 : |(logDeriv (fun s : ℝ => P₁.eval (γ s)) θ).im|
      ≤ ‖dγ θ‖ * (‖(Polynomial.derivative P₁).eval (γ θ)‖ / ‖P₁.eval (γ θ)‖) := by
    have h := abs_im_logDeriv_le (fun s : ℝ => P₁.eval (γ s)) θ
    rwa [hd1.deriv, norm_mul, mul_div_assoc] at h
  have b3 : |(logDeriv (fun s : ℝ => P₂.eval (γ s)) θ).im|
      ≤ ‖dγ θ‖ * (‖(Polynomial.derivative P₂).eval (γ θ)‖ / ‖P₂.eval (γ θ)‖) := by
    have h := abs_im_logDeriv_le (fun s : ℝ => P₂.eval (γ s)) θ
    rwa [hd2.deriv, norm_mul, mul_div_assoc] at h
  calc |(logDeriv (fun s : ℝ => γ s * P₁.eval (γ s) / P₂.eval (γ s)) θ).im|
      ≤ |(logDeriv γ θ).im| + |(logDeriv (fun s : ℝ => P₁.eval (γ s)) θ).im|
          + |(logDeriv (fun s : ℝ => P₂.eval (γ s)) θ).im| := by
        rw [hsplit, Complex.sub_im, Complex.add_im]
        exact le_trans (abs_sub _ _) (by gcongr; exact abs_add_le _ _)
    _ ≤ ‖dγ θ‖ * (1 / ‖γ θ‖ + ‖(Polynomial.derivative P₁).eval (γ θ)‖ / ‖P₁.eval (γ θ)‖
          + ‖(Polynomial.derivative P₂).eval (γ θ)‖ / ‖P₂.eval (γ θ)‖) := by
        rw [mul_add, mul_add]
        exact add_le_add (add_le_add b1 b2) b3

/-- **`eq:W-local-zero` at the amplitude's own factorization.**  Rather than the
opaque cofactor `Amplitude.amplitude_local_zero` returns, this exhibits the
factorization with the divided difference visible, which is what the bound needs:
`W = -(θ-θ_j)^{ν}·h(θ)^{ν}·A(θ)` with `h` the divided difference of the branch
about `θ_j` and `A = γ·B̃∘γ/E∘γ`.

**`E` is the `z`-free factor and that is what makes this local.**  Through
`Amplitude.ftAmp_eq_ftCritical` the amplitude depends on `θ` only through `γ`;
the spectral parameter has been eliminated, so no regularity of `z` along the arc
is consumed here and none has to be supplied. -/
theorem ftAmp_eq_local_factorization {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {γ zf : ℝ → ℂ} {θ₀ θ : ℝ} (hγ : γ θ ≠ 0)
    (hroot : (ftDen Q r (zf θ)).eval (γ θ) = 0)
    (hE : (ftCritical Q r).eval (γ θ) ≠ 0) :
    ftAmp Q B r (zf θ) (γ θ)
      = (-1 : ℂ) * ((θ : ℂ) - (θ₀ : ℂ)) ^ (B.rootMultiplicity (γ θ₀) : ℤ)
          * (centeredCofactor γ θ₀ θ) ^ (B.rootMultiplicity (γ θ₀) : ℤ)
          * (γ θ * (B /ₘ (Polynomial.X - Polynomial.C (γ θ₀)) ^ B.rootMultiplicity (γ θ₀)).eval
              (γ θ) / (ftCritical Q r).eval (γ θ)) := by
  classical
  set ν := B.rootMultiplicity (γ θ₀) with hν
  set Bt := B /ₘ (Polynomial.X - Polynomial.C (γ θ₀)) ^ ν with hBt
  have hBfac : (Polynomial.X - Polynomial.C (γ θ₀)) ^ ν * Bt = B :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq B _
  have hBev : B.eval (γ θ) = (γ θ - γ θ₀) ^ ν * Bt.eval (γ θ) := by
    conv_lhs => rw [← hBfac]
    simp
  rw [ftAmp_eq_ftCritical hr hγ hroot, hBev, sub_eq_mul_centeredCofactor γ θ₀ θ, mul_pow,
    zpow_natCast, zpow_natCast]
  field_simp

/-- **`eq:phase-derivative-bound` on a two-sided collar about an interior
amplitude zero.**  This is `BoundAssembly.exists_bound_of_finite_exceptional`'s
`hloc` at the Forgács–Tran amplitude: a bound on `|Im(W'/W)|` on a punctured ball
about `θ_j`, at a constant depending on the center.

**The zero itself is invisible.**  `W` carries the factor `(θ-θ_j)^{ν_j}`, whose
logarithmic derivative `ν_j/(θ-θ_j)` blows up — and is real, so it contributes
nothing to `Im(W'/W)`.  What is left is the divided difference to the same power,
bounded by `exists_bound_im_logDeriv_centeredCofactor`, and a factor that neither
vanishes nor blows up at the center.

**A bound, not a limit, and the branch never has to be `C¹` at the center.**  The
outer factor's logarithmic derivative is bounded by `‖γ'‖` against three
quantities continuous at `θ_j`, and `‖γ'‖` is bounded by `hlip` — no continuity of
`γ'` is consumed anywhere. -/
theorem exists_bound_im_logDeriv_ftAmp_interior {Q B : Polynomial ℂ} (hB : B ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) {γ dγ zf : ℝ → ℂ} {θ₀ b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hd : ∀ θ ∈ Icc (θ₀ - b) (θ₀ + b), HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (θ₀ - b) (θ₀ + b), ‖dγ θ - dγ θ₀‖ ≤ L * |θ - θ₀|)
    (h0 : dγ θ₀ ≠ 0) (hγ0 : γ θ₀ ≠ 0)
    (hEne : (ftCritical Q r).eval (γ θ₀) ≠ 0)
    (hroot : ∀ᶠ θ in nhds θ₀, (ftDen Q r (zf θ)).eval (γ θ) = 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ θ, |θ - θ₀| < δ → θ ≠ θ₀ →
        |(deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) θ
            / ftAmp Q B r (zf θ) (γ θ)).im| ≤ C := by
  classical
  set ν := B.rootMultiplicity (γ θ₀) with hν
  set Bt := B /ₘ (Polynomial.X - Polynomial.C (γ θ₀)) ^ ν with hBt
  set E := ftCritical Q r with hE
  have hBtne : Bt.eval (γ θ₀) ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero _ hB
  set A : ℝ → ℂ := fun s => γ s * Bt.eval (γ s) / E.eval (γ s) with hA
  obtain ⟨b', hb'0, hb'b, hune, hudiff, hubd⟩ :=
    exists_bound_im_logDeriv_centeredCofactor hb hL hd hlip h0
  have hmem₀ : θ₀ ∈ Icc (θ₀ - b) (θ₀ + b) := ⟨by linarith, by linarith⟩
  have hγc : ContinuousAt γ θ₀ := (hd θ₀ hmem₀).continuousAt
  set D : ℝ := ‖dγ θ₀‖ + L * b with hD
  have hD0 : 0 ≤ D := by positivity
  set Ψ : ℝ → ℝ := fun s => 1 / ‖γ s‖ + ‖(Polynomial.derivative Bt).eval (γ s)‖ / ‖Bt.eval (γ s)‖
    + ‖(Polynomial.derivative E).eval (γ s)‖ / ‖E.eval (γ s)‖ with hΨ
  have hΨnn : ∀ s, 0 ≤ Ψ s := fun s => by rw [hΨ]; positivity
  have hΨc : ContinuousAt Ψ θ₀ := by
    have hp : ∀ P : Polynomial ℂ, ContinuousAt (fun s : ℝ => P.eval (γ s)) θ₀ := fun P =>
      ((Polynomial.continuous P).continuousAt).comp hγc
    exact ((continuousAt_const.div hγc.norm (norm_ne_zero_iff.mpr hγ0)).add
      ((hp _).norm.div (hp Bt).norm (norm_ne_zero_iff.mpr hBtne))).add
      ((hp _).norm.div (hp E).norm (norm_ne_zero_iff.mpr hEne))
  set K : ℝ := Ψ θ₀ + 1 with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith [hΨnn θ₀]
  -- the collar, from the conditions that hold near the center
  have hball : ∀ᶠ θ in nhds θ₀, |θ - θ₀| ≤ b' := by
    filter_upwards [Metric.ball_mem_nhds θ₀ hb'0] with x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    exact hx.le
  have hmemb : ∀ᶠ θ in nhds θ₀, θ ∈ Icc (θ₀ - b) (θ₀ + b) := by
    filter_upwards [Metric.ball_mem_nhds θ₀ hb] with x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hγne : ∀ᶠ θ in nhds θ₀, γ θ ≠ 0 := hγc.eventually_ne hγ0
  have hEev : ∀ᶠ θ in nhds θ₀, E.eval (γ θ) ≠ 0 :=
    (((Polynomial.continuous E).continuousAt).comp hγc).eventually_ne hEne
  have hBtev : ∀ᶠ θ in nhds θ₀, Bt.eval (γ θ) ≠ 0 :=
    (((Polynomial.continuous Bt).continuousAt).comp hγc).eventually_ne hBtne
  have hΨev : ∀ᶠ θ in nhds θ₀, Ψ θ < K :=
    hΨc.eventually_lt_const (by rw [hK]; linarith)
  have hev := hroot.and (hγne.and (hEev.and (hBtev.and (hΨev.and (hball.and hmemb)))))
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hev
  have hCnn : 0 ≤ (ν : ℝ) * (3 * L / ‖dγ θ₀‖) + D * K :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (norm_nonneg _)))
      (mul_nonneg hD0 hK0)
  refine ⟨δ, (ν : ℝ) * (3 * L / ‖dγ θ₀‖) + D * K, hδ0, hCnn, ?_⟩
  intro θ hθ hθ0
  have hin : ∀ x : ℝ, |x - θ₀| < δ →
      (ftDen Q r (zf x)).eval (γ x) = 0 ∧ γ x ≠ 0 ∧ E.eval (γ x) ≠ 0 ∧ Bt.eval (γ x) ≠ 0
        ∧ Ψ x < K ∧ |x - θ₀| ≤ b' ∧ x ∈ Icc (θ₀ - b) (θ₀ + b) := by
    intro x hx
    exact hδ (by rw [Metric.mem_ball, Real.dist_eq]; exact hx)
  obtain ⟨-, hγn, hEn, hBtn, hΨθ, hbθ, hmθ⟩ := hin θ hθ
  have hγd : HasDerivAt γ (dγ θ) θ := hd θ hmθ
  have hBd := hasDerivAt_eval_comp Bt hγd
  have hEd := hasDerivAt_eval_comp E hγd
  -- the factorization, on the whole ball and so near `θ`
  have hfac : (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) =ᶠ[nhds θ]
      fun s : ℝ => (-1 : ℂ) * ((s : ℂ) - (θ₀ : ℂ)) ^ (ν : ℤ)
        * (centeredCofactor γ θ₀ s) ^ (ν : ℤ) * A s := by
    have hnb : Metric.ball θ₀ δ ∈ nhds θ :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, Real.dist_eq]; exact hθ)
    filter_upwards [hnb] with x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    obtain ⟨h1, h2, h3, -, -, -, -⟩ := hin x hx
    exact ftAmp_eq_local_factorization (θ₀ := θ₀) hr h2 h1 h3
  have hAd : DifferentiableAt ℝ A θ :=
    (hγd.differentiableAt.mul hBd.differentiableAt).div hEd.differentiableAt hEn
  have hA0 : A θ ≠ 0 := div_ne_zero (mul_ne_zero hγn hBtn) hEn
  -- the outer factor: three logarithmic derivatives, each bounded by `‖γ'‖` against
  -- a quantity continuous at the center
  have houter : |(logDeriv A θ).im| ≤ D * K := by
    have hdb : ‖dγ θ‖ ≤ D := by
      have hnb : ‖dγ θ‖ ≤ ‖dγ θ₀‖ + ‖dγ θ - dγ θ₀‖ := by
        simpa using norm_add_le (dγ θ₀) (dγ θ - dγ θ₀)
      have hl := hlip θ hmθ
      have habs : |θ - θ₀| ≤ b := by
        rw [abs_le]
        exact ⟨by linarith [hmθ.1], by linarith [hmθ.2]⟩
      have hLb : L * |θ - θ₀| ≤ L * b := by nlinarith
      rw [hD]
      linarith
    calc |(logDeriv A θ).im| ≤ ‖dγ θ‖ * Ψ θ := by
          rw [hA, hΨ]
          exact abs_im_logDeriv_polyQuotient_le Bt E hγd hγn hBtn hEn
      _ ≤ D * K := mul_le_mul hdb hΨθ.le (hΨnn θ) hD0
  have hmid := hubd θ hbθ hθ0
  have hkey := abs_im_logDeriv_le_of_local_factorization_outer (θ₀ := θ₀) (m := (ν : ℤ))
    (p := (ν : ℤ)) hθ0 (by norm_num : (-1 : ℂ) ≠ 0) hfac (hudiff θ hbθ hθ0) (hune θ hbθ hθ0)
    hAd hA0 hmid houter
  have hcast : |(((ν : ℤ) : ℝ))| = (ν : ℝ) := by
    push_cast
    exact abs_of_nonneg (Nat.cast_nonneg ν)
  rwa [hcast] at hkey

/-! ### The endpoint, at the amplitude's own factorization -/

/-- **`eq:W-endpoint-form` with the divided difference visible.**  The endpoint
twin of `ftAmp_eq_local_factorization`, and the exponent is the one place the two
differ: at an interior center only `B` degenerates, while at the endpoint the
`z`-free factor `E` degenerates too, to order exactly `k-1`, so the power carried
is `ν - (k-1)` — an **integer**, negative whenever `ν < k-1`, which is the generic
case.

`m` is `k-1` supplied by the caller rather than recomputed, because
`Geometry.exists_ftCritical_factor` produces `H` and that exponent together and
truncated subtraction on `ℕ` is not what the statement wants twice.

**`_hγ0` is inert in the proof and fixes what the statement is about.**
`endpointCofactor f δ` is `f δ / δ`, so without `γ 0 = te` the cofactor carried by the
conclusion is the bare quotient `(γ δ - te)/δ` for an unrelated constant `te`.  With it,
that quotient is the divided difference of `γ` across `[0, δ]` and `te` is the endpoint
the factorization is taken at, which is the only reading under which the `(δ - 0)`
written in the conclusion means anything. -/
theorem ftAmp_eq_endpoint_factorization {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {γ zf : ℝ → ℂ} {te : ℂ} {H : Polynomial ℂ} {m : ℕ} {δ : ℝ}
    (hEfac : ftCritical Q r = (Polynomial.X - Polynomial.C te) ^ m * H)
    (_hγ0 : γ 0 = te) (hδ : δ ≠ 0) (hγ : γ δ ≠ 0)
    (hu : endpointCofactor (fun s : ℝ => γ s - te) δ ≠ 0)
    (hH : H.eval (γ δ) ≠ 0)
    (hroot : (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    ftAmp Q B r (zf δ) (γ δ)
      = (-1 : ℂ) * ((δ : ℂ) - (((0 : ℝ)) : ℂ)) ^ ((B.rootMultiplicity te : ℤ) - (m : ℤ))
          * (endpointCofactor (fun s : ℝ => γ s - te) δ)
              ^ ((B.rootMultiplicity te : ℤ) - (m : ℤ))
          * (γ δ * (B /ₘ (Polynomial.X - Polynomial.C te) ^ B.rootMultiplicity te).eval (γ δ)
              / H.eval (γ δ)) := by
  classical
  set ν := B.rootMultiplicity te with hν
  set Bt := B /ₘ (Polynomial.X - Polynomial.C te) ^ ν with hBt
  have hBfac : (Polynomial.X - Polynomial.C te) ^ ν * Bt = B :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq B _
  have hBev : B.eval (γ δ) = (γ δ - te) ^ ν * Bt.eval (γ δ) := by
    conv_lhs => rw [← hBfac]
    simp
  have hEev : (ftCritical Q r).eval (γ δ) = (γ δ - te) ^ m * H.eval (γ δ) := by
    rw [hEfac]; simp
  have hδne : ((δ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ
  have hXne : ((δ : ℂ) - (((0 : ℝ)) : ℂ)) ≠ 0 := by simpa using hδne
  have hsub : γ δ - te
      = ((δ : ℂ) - (((0 : ℝ)) : ℂ)) * endpointCofactor (fun s : ℝ => γ s - te) δ := by
    rw [endpointCofactor]
    simp only [Complex.ofReal_zero, sub_zero]
    field_simp
  rw [ftAmp_eq_ftCritical hr hγ hroot, hBev, hEev, hsub, mul_pow, mul_pow,
    zpow_sub₀ hXne, zpow_sub₀ hu, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
  field_simp

/-- **`eq:phase-derivative-bound` on the collar, at the amplitude itself.**  The
endpoint twin of `exists_bound_im_logDeriv_ftAmp_interior`, and the same three
ingredients: the degenerating power is real and drops out of `Im(W'/W)`, the
divided difference is bounded by `EndpointCofactorBound`'s own estimate, and the
outer factor is bounded by `‖γ'‖` against quantities continuous at the endpoint.

**What distinguishes the endpoint is the exponent and nothing else.**  `E`
degenerates there too, so the power is `ν - (k-1)` rather than `ν`, and its
absolute value is what multiplies the divided-difference constant.  The estimate
does not care about its sign, which is why nothing here has to know whether `W`
vanishes or blows up at the endpoint.

The binders are one-sided at `0` and two-sided off it, which is what the branch
modules carry — `δ` is an angular distance, so a two-sided derivative at the
endpoint asks for the negation of the phenomenon. -/
theorem exists_bound_im_logDeriv_ftAmp_endpoint {Q B : Polynomial ℂ} (hB : B ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) {γ dγ zf : ℝ → ℂ} {te : ℂ} {H : Polynomial ℂ} {m : ℕ} {b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hEfac : ftCritical Q r = (Polynomial.X - Polynomial.C te) ^ m * H)
    (hH0 : H.eval te ≠ 0) (hte : te ≠ 0) (hγ0 : γ 0 = te)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0)
    (hroot : ∀ δ ∈ Ioc (0 : ℝ) b, (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ C ∧
      ∀ δ ∈ Ioc (0 : ℝ) b',
        |(deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) δ
            / ftAmp Q B r (zf δ) (γ δ)).im| ≤ C := by
  classical
  set ν := B.rootMultiplicity te with hν
  set Bt := B /ₘ (Polynomial.X - Polynomial.C te) ^ ν with hBt
  have hBtne : Bt.eval te ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero _ hB
  set g : ℝ → ℂ := fun s : ℝ => γ s - te with hg
  set A : ℝ → ℂ := fun s => γ s * Bt.eval (γ s) / H.eval (γ s) with hA
  obtain ⟨b₁, hb₁0, hb₁b, hune, hudiff, hubd⟩ :=
    exists_bound_im_logDeriv_endpointCofactor (γ := g) (dγ := dγ) hb hL
      (by simp [hg, hγ0]) (by simpa [hg] using hd0.sub_const te)
      (fun θ hθ => by simpa [hg] using (hd θ hθ).sub_const te) hlip h0
  -- the constants
  set D : ℝ := ‖dγ 0‖ + L * b with hD
  have hD0 : 0 ≤ D := by positivity
  set Ψ : ℝ → ℝ := fun s => 1 / ‖γ s‖ + ‖(Polynomial.derivative Bt).eval (γ s)‖ / ‖Bt.eval (γ s)‖
    + ‖(Polynomial.derivative H).eval (γ s)‖ / ‖H.eval (γ s)‖ with hΨ
  have hΨnn : ∀ s, 0 ≤ Ψ s := fun s => by rw [hΨ]; positivity
  have hγc : ContinuousWithinAt γ (Ici (0 : ℝ)) 0 := hd0.continuousWithinAt
  have hγc' : ContinuousWithinAt γ (Ioi (0 : ℝ)) 0 := hγc.mono Ioi_subset_Ici_self
  have hγ0ne : γ 0 ≠ 0 := by rw [hγ0]; exact hte
  have hΨc : ContinuousWithinAt Ψ (Ioi (0 : ℝ)) 0 := by
    have hp : ∀ P : Polynomial ℂ, ContinuousWithinAt (fun s : ℝ => P.eval (γ s))
        (Ioi (0 : ℝ)) 0 := fun P =>
      ((Polynomial.continuous P).continuousAt).comp_continuousWithinAt hγc'
    have hBt0 : Bt.eval (γ 0) ≠ 0 := by rw [hγ0]; exact hBtne
    have hH0' : H.eval (γ 0) ≠ 0 := by rw [hγ0]; exact hH0
    exact ((continuousWithinAt_const.div hγc'.norm (norm_ne_zero_iff.mpr hγ0ne)).add
      ((hp _).norm.div (hp Bt).norm (norm_ne_zero_iff.mpr hBt0))).add
      ((hp _).norm.div (hp H).norm (norm_ne_zero_iff.mpr hH0'))
  set K : ℝ := Ψ 0 + 1 with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith [hΨnn 0]
  -- the conditions that hold just to the right of the endpoint
  have hγev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), γ δ ≠ 0 := hγc'.eventually_ne hγ0ne
  have hBtev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), Bt.eval (γ δ) ≠ 0 :=
    (((Polynomial.continuous Bt).continuousAt).comp_continuousWithinAt hγc').eventually_ne
      (by simp only [Function.comp_apply, hγ0]; exact hBtne)
  have hHev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), H.eval (γ δ) ≠ 0 :=
    (((Polynomial.continuous H).continuousAt).comp_continuousWithinAt hγc').eventually_ne
      (by simp only [Function.comp_apply, hγ0]; exact hH0)
  have hΨev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), Ψ δ < K :=
    hΨc.eventually_lt_const (by rw [hK]; linarith)
  obtain ⟨b₂, hb₂mem, hb₂⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp (hγev.and (hBtev.and hHev) |>.and hΨev)
  have hb₂0 : (0 : ℝ) < b₂ := hb₂mem
  set bb : ℝ := min b₁ b₂ with hbb
  have hbb0 : 0 < bb := lt_min hb₁0 hb₂0
  refine ⟨bb / 2, |(ν : ℝ) - (m : ℝ)| * (3 * L / ‖dγ 0‖) + D * K,
    by linarith, by
      have : bb ≤ b₁ := min_le_left _ _
      linarith [hb₁b],
    add_nonneg (mul_nonneg (abs_nonneg _) (div_nonneg (by linarith) (norm_nonneg _)))
      (mul_nonneg hD0 hK0), ?_⟩
  intro δ hδ
  have hδlt : δ < bb := by linarith [hδ.2]
  have hδ0 : δ ≠ 0 := ne_of_gt hδ.1
  have hδ₁ : δ ∈ Icc (0 : ℝ) b₁ := ⟨hδ.1.le, le_trans hδlt.le (min_le_left _ _)⟩
  have hδ₂ : δ ∈ Ioc (0 : ℝ) b₂ := ⟨hδ.1, le_trans hδlt.le (min_le_right _ _)⟩
  obtain ⟨⟨hγn, hBtn, hHn⟩, hΨδ⟩ := hb₂ hδ₂
  have hδb : δ ∈ Ioc (0 : ℝ) b :=
    ⟨hδ.1, le_trans (le_trans hδlt.le (min_le_left _ _)) hb₁b⟩
  have hγd : HasDerivAt γ (dγ δ) δ := hd δ hδb
  have hune' := hune δ hδ₁ hδ0
  -- the factorization, on the whole punctured collar and so near `δ`
  have hfac : (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) =ᶠ[nhds δ]
      fun s : ℝ => (-1 : ℂ) * ((s : ℂ) - (((0 : ℝ)) : ℂ)) ^ ((ν : ℤ) - (m : ℤ))
        * (endpointCofactor g s) ^ ((ν : ℤ) - (m : ℤ)) * A s := by
    filter_upwards [Ioo_mem_nhds hδ.1 hδlt] with x hx
    have hx₁ : x ∈ Icc (0 : ℝ) b₁ := ⟨hx.1.le, le_trans hx.2.le (min_le_left _ _)⟩
    have hx₂ : x ∈ Ioc (0 : ℝ) b₂ := ⟨hx.1, le_trans hx.2.le (min_le_right _ _)⟩
    have hxb : x ∈ Ioc (0 : ℝ) b :=
      ⟨hx.1, le_trans (le_trans hx.2.le (min_le_left _ _)) hb₁b⟩
    obtain ⟨⟨hxγ, hxBt, hxH⟩, -⟩ := hb₂ hx₂
    exact ftAmp_eq_endpoint_factorization hr hEfac hγ0 (ne_of_gt hx.1) hxγ
      (hune x hx₁ (ne_of_gt hx.1)) hxH (hroot x hxb)
  -- the outer factor
  have hHd := hasDerivAt_eval_comp H hγd
  have hBd := hasDerivAt_eval_comp Bt hγd
  have hAd : DifferentiableAt ℝ A δ :=
    (hγd.differentiableAt.mul hBd.differentiableAt).div hHd.differentiableAt hHn
  have hA0 : A δ ≠ 0 := div_ne_zero (mul_ne_zero hγn hBtn) hHn
  have houter : |(logDeriv A δ).im| ≤ D * K := by
    have hdb : ‖dγ δ‖ ≤ D := by
      have hnb : ‖dγ δ‖ ≤ ‖dγ 0‖ + ‖dγ δ - dγ 0‖ := by
        simpa using norm_add_le (dγ 0) (dγ δ - dγ 0)
      have hl := hlip δ ⟨hδ.1.le, hδb.2⟩
      have hLb : L * δ ≤ L * b := by nlinarith [hδb.2]
      rw [hD]
      linarith
    calc |(logDeriv A δ).im| ≤ ‖dγ δ‖ * Ψ δ := by
          rw [hA, hΨ]
          exact abs_im_logDeriv_polyQuotient_le Bt H hγd hγn hBtn hHn
      _ ≤ D * K := mul_le_mul hdb hΨδ.le (hΨnn δ) hD0
  have hkey := abs_im_logDeriv_le_of_local_factorization_outer (θ₀ := (0 : ℝ))
    (m := (ν : ℤ) - (m : ℤ)) (p := (ν : ℤ) - (m : ℤ)) hδ0 (by norm_num : (-1 : ℂ) ≠ 0)
    hfac (hudiff δ hδ₁ hδ0) hune' hAd hA0 (hubd δ hδ₁ hδ0) houter
  push_cast at hkey
  exact hkey

/-! ### What the interior bound asks of the branch, reduced to `γ''` -/

/-- **The Lipschitz binder from a second-derivative bound, on a two-sided
collar.**  `EndpointCofactorBound.norm_deriv_sub_le_of_norm_deriv2_le` does this
at an endpoint, where nothing is available at the center and the estimate has to
be reached through a limit.  At an interior center it is the mean value
inequality and nothing else — `γ'` is differentiable on the whole collar, which
is convex. -/
theorem norm_deriv_sub_le_of_norm_deriv2_le_centered {dγ d2γ : ℝ → ℂ} {θ₀ b L : ℝ}
    (hb : 0 ≤ b)
    (hd2 : ∀ θ ∈ Icc (θ₀ - b) (θ₀ + b), HasDerivAt dγ (d2γ θ) θ)
    (hbd : ∀ θ ∈ Icc (θ₀ - b) (θ₀ + b), ‖d2γ θ‖ ≤ L) :
    ∀ θ ∈ Icc (θ₀ - b) (θ₀ + b), ‖dγ θ - dγ θ₀‖ ≤ L * |θ - θ₀| := by
  intro θ hθ
  have h0 : θ₀ ∈ Icc (θ₀ - b) (θ₀ + b) := ⟨by linarith, by linarith⟩
  have h := (convex_Icc (θ₀ - b) (θ₀ + b)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := dγ) (f' := d2γ) (fun x hx => (hd2 x hx).hasDerivWithinAt) hbd h0 hθ
  rwa [Real.norm_eq_abs] at h

/-- **The interior bound with the collar and the Lipschitz constant produced.**
What a caller of `exists_bound_im_logDeriv_ftAmp_interior` actually holds is not a
collar and a constant but the branch modules' own three facts on the open arc:
`γ` differentiable, `γ'` differentiable, `γ''` continuous.  Those give the collar
and the constant, so nothing has to be built by hand.

**`γ''` is asked continuous only AT the center**, which is where the bound is
being taken, and it is what fixes `L = ‖γ''(θ_j)‖ + 1`.  The `+1` is not slack:
`γ''` may vanish at the center — the branch may be affine to second order there —
and a bound of `‖γ''(θ_j)‖` alone would then be `0` on a collar where `γ''` is
merely small, which is a different and false statement. -/
theorem exists_bound_im_logDeriv_ftAmp_interior_of_deriv2 {Q B : Polynomial ℂ}
    (hB : B ≠ 0) {r : ℕ} (hr : 1 ≤ r) {γ dγ d2γ zf : ℝ → ℂ} {θ₀ : ℝ} {V : Set ℝ}
    (hV : V ∈ nhds θ₀)
    (hd : ∀ θ ∈ V, HasDerivAt γ (dγ θ) θ)
    (hd2 : ∀ θ ∈ V, HasDerivAt dγ (d2γ θ) θ)
    (hc2 : ContinuousAt d2γ θ₀)
    (h0 : dγ θ₀ ≠ 0) (hγ0 : γ θ₀ ≠ 0)
    (hEne : (ftCritical Q r).eval (γ θ₀) ≠ 0)
    (hroot : ∀ᶠ θ in nhds θ₀, (ftDen Q r (zf θ)).eval (γ θ) = 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ θ, |θ - θ₀| < δ → θ ≠ θ₀ →
        |(deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) θ
            / ftAmp Q B r (zf θ) (γ θ)).im| ≤ C := by
  set L : ℝ := ‖d2γ θ₀‖ + 1 with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hVev : ∀ᶠ θ in nhds θ₀, θ ∈ V := hV
  have hbound : ∀ᶠ θ in nhds θ₀, ‖d2γ θ‖ ≤ L := by
    have hn : ContinuousAt (fun s : ℝ => ‖d2γ s‖) θ₀ := hc2.norm
    exact (hn.eventually_lt_const (by rw [hL]; linarith)).mono fun _ h => h.le
  obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp (hVev.and hbound)
  have hcol : ∀ θ ∈ Icc (θ₀ - ε / 2) (θ₀ + ε / 2), θ ∈ V ∧ ‖d2γ θ‖ ≤ L := by
    intro θ hθ
    refine hε ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    obtain ⟨h1, h2⟩ := hθ
    constructor <;> linarith
  exact exists_bound_im_logDeriv_ftAmp_interior (b := ε / 2) (L := L) hB hr
    (by linarith) hL0 (fun θ hθ => hd θ (hcol θ hθ).1)
    (norm_deriv_sub_le_of_norm_deriv2_le_centered (d2γ := d2γ) (by linarith)
      (fun θ hθ => hd2 θ (hcol θ hθ).1) (fun θ hθ => (hcol θ hθ).2))
    h0 hγ0 hEne hroot

/-! ### The upper endpoint of an `r ≥ 2` arc, where the branch runs into the origin -/

/-- **The outer factor without the branch in it.**  At the origin endpoint the
branch itself is the degenerating factor, so it is pulled out with the power and
what is left is a quotient of two polynomials along `γ` and nothing else. -/
theorem abs_im_logDeriv_polyRatio_le {γ dγ : ℝ → ℂ} {θ : ℝ} (P₁ P₂ : Polynomial ℂ)
    (hd : HasDerivAt γ (dγ θ) θ) (h1 : P₁.eval (γ θ) ≠ 0) (h2 : P₂.eval (γ θ) ≠ 0) :
    |(logDeriv (fun s : ℝ => P₁.eval (γ s) / P₂.eval (γ s)) θ).im|
      ≤ ‖dγ θ‖ * (‖(Polynomial.derivative P₁).eval (γ θ)‖ / ‖P₁.eval (γ θ)‖
          + ‖(Polynomial.derivative P₂).eval (γ θ)‖ / ‖P₂.eval (γ θ)‖) := by
  have hd1 := hasDerivAt_eval_comp P₁ hd
  have hd2 := hasDerivAt_eval_comp P₂ hd
  have hsplit : logDeriv (fun s : ℝ => P₁.eval (γ s) / P₂.eval (γ s)) θ
      = logDeriv (fun s : ℝ => P₁.eval (γ s)) θ - logDeriv (fun s : ℝ => P₂.eval (γ s)) θ :=
    logDeriv_div (f := fun s : ℝ => P₁.eval (γ s)) (g := fun s : ℝ => P₂.eval (γ s)) θ
      h1 h2 hd1.differentiableAt hd2.differentiableAt
  have b1 : |(logDeriv (fun s : ℝ => P₁.eval (γ s)) θ).im|
      ≤ ‖dγ θ‖ * (‖(Polynomial.derivative P₁).eval (γ θ)‖ / ‖P₁.eval (γ θ)‖) := by
    have h := abs_im_logDeriv_le (fun s : ℝ => P₁.eval (γ s)) θ
    rwa [hd1.deriv, norm_mul, mul_div_assoc] at h
  have b2 : |(logDeriv (fun s : ℝ => P₂.eval (γ s)) θ).im|
      ≤ ‖dγ θ‖ * (‖(Polynomial.derivative P₂).eval (γ θ)‖ / ‖P₂.eval (γ θ)‖) := by
    have h := abs_im_logDeriv_le (fun s : ℝ => P₂.eval (γ s)) θ
    rwa [hd2.deriv, norm_mul, mul_div_assoc] at h
  calc |(logDeriv (fun s : ℝ => P₁.eval (γ s) / P₂.eval (γ s)) θ).im|
      ≤ |(logDeriv (fun s : ℝ => P₁.eval (γ s)) θ).im|
          + |(logDeriv (fun s : ℝ => P₂.eval (γ s)) θ).im| := by
        rw [hsplit, Complex.sub_im]
        exact abs_sub _ _
    _ ≤ ‖dγ θ‖ * (‖(Polynomial.derivative P₁).eval (γ θ)‖ / ‖P₁.eval (γ θ)‖
          + ‖(Polynomial.derivative P₂).eval (γ θ)‖ / ‖P₂.eval (γ θ)‖) := by
        rw [mul_add]
        exact add_le_add b1 b2

/-- **`eq:W-endpoint-form` at the origin.**  `Amplitude.amplitude_endpoint_form_origin`
is a separate theorem from `amplitude_endpoint_form`, and so is this: at the upper
endpoint of an `r ≥ 2` arc the principal root runs into `t = 0`, where neither `B`
nor the `z`-free factor vanishes, so there is no order to subtract and the
exponent is `1` **unconditionally**.

That is not a simplification of the finite-endpoint case but a different
factorization: `t_e = 0` is exactly what
`FTBranchUpperRefutation.not_upper_endpoint_datum_ne_zero` refutes `t_e ≠ 0` with
for every `n ≥ 2` and `r ≥ 2`, so `ftAmp_eq_endpoint_factorization` — whose `A`
carries a `γ` factor that would vanish here — does not reach it.  The branch is
the degenerating factor and is pulled out with the power. -/
theorem ftAmp_eq_origin_factorization {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {γ zf : ℝ → ℂ} {η : ℝ} (hη : η ≠ 0) (hγ : γ η ≠ 0)
    (hE : (ftCritical Q r).eval (γ η) ≠ 0)
    (hroot : (ftDen Q r (zf η)).eval (γ η) = 0) :
    ftAmp Q B r (zf η) (γ η)
      = (-1 : ℂ) * ((η : ℂ) - (((0 : ℝ)) : ℂ)) ^ (1 : ℤ)
          * (endpointCofactor γ η) ^ (1 : ℤ)
          * (B.eval (γ η) / (ftCritical Q r).eval (γ η)) := by
  have hηne : ((η : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
  rw [ftAmp_eq_ftCritical hr hγ hroot, endpointCofactor]
  simp only [Complex.ofReal_zero, sub_zero, zpow_one]
  field_simp

/-- **`eq:phase-derivative-bound` on the collar at the origin endpoint.**  The
twin of `exists_bound_im_logDeriv_ftAmp_endpoint` for the regime that one does
not reach.  Three differences, and each of them makes this the easier case:
the exponent is `1` rather than an integer of either sign, the divided difference
is the branch's own `T = γ(η)/η` rather than a shifted one, and the outer factor
is a ratio of two polynomials along `γ` with no separate branch factor.

`hQ0` is `Q(0) ≠ 0` in the shape `E(0) = -rQ(0) ≠ 0` uses it, and `hB0` is
`B(0) ≠ 0` — the manuscript's observation that `B` does not vanish on the upper
cluster at all. -/
theorem exists_bound_im_logDeriv_ftAmp_origin {Q B : Polynomial ℂ} {r : ℕ}
    (hr : 1 ≤ r) {γ dγ zf : ℝ → ℂ} {b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hB0 : B.eval 0 ≠ 0) (hE0 : (ftCritical Q r).eval 0 ≠ 0) (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0)
    (hroot : ∀ η ∈ Ioc (0 : ℝ) b, (ftDen Q r (zf η)).eval (γ η) = 0) :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ C ∧
      ∀ η ∈ Ioc (0 : ℝ) b',
        |(deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) η
            / ftAmp Q B r (zf η) (γ η)).im| ≤ C := by
  classical
  set E := ftCritical Q r with hE
  set A : ℝ → ℂ := fun s => B.eval (γ s) / E.eval (γ s) with hA
  obtain ⟨b₁, hb₁0, hb₁b, hune, hudiff, hubd⟩ :=
    exists_bound_im_logDeriv_endpointCofactor (γ := γ) (dγ := dγ) hb hL hγ0 hd0 hd hlip h0
  set D : ℝ := ‖dγ 0‖ + L * b with hD
  have hD0 : 0 ≤ D := by positivity
  set Ψ : ℝ → ℝ := fun s => ‖(Polynomial.derivative B).eval (γ s)‖ / ‖B.eval (γ s)‖
    + ‖(Polynomial.derivative E).eval (γ s)‖ / ‖E.eval (γ s)‖ with hΨ
  have hΨnn : ∀ s, 0 ≤ Ψ s := fun s => by rw [hΨ]; positivity
  have hγc : ContinuousWithinAt γ (Ioi (0 : ℝ)) 0 :=
    hd0.continuousWithinAt.mono Ioi_subset_Ici_self
  have hB0' : B.eval (γ 0) ≠ 0 := by rw [hγ0]; exact hB0
  have hE0' : E.eval (γ 0) ≠ 0 := by rw [hγ0]; exact hE0
  have hΨc : ContinuousWithinAt Ψ (Ioi (0 : ℝ)) 0 := by
    have hp : ∀ P : Polynomial ℂ, ContinuousWithinAt (fun s : ℝ => P.eval (γ s))
        (Ioi (0 : ℝ)) 0 := fun P =>
      ((Polynomial.continuous P).continuousAt).comp_continuousWithinAt hγc
    exact ((hp _).norm.div (hp B).norm (norm_ne_zero_iff.mpr hB0')).add
      ((hp _).norm.div (hp E).norm (norm_ne_zero_iff.mpr hE0'))
  set K : ℝ := Ψ 0 + 1 with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith [hΨnn 0]
  have hBev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Ioi 0), B.eval (γ η) ≠ 0 :=
    (((Polynomial.continuous B).continuousAt).comp_continuousWithinAt hγc).eventually_ne hB0'
  have hEev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Ioi 0), E.eval (γ η) ≠ 0 :=
    (((Polynomial.continuous E).continuousAt).comp_continuousWithinAt hγc).eventually_ne hE0'
  have hΨev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Ioi 0), Ψ η < K :=
    hΨc.eventually_lt_const (by rw [hK]; linarith)
  obtain ⟨b₂, hb₂mem, hb₂⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp (hBev.and hEev |>.and hΨev)
  have hb₂0 : (0 : ℝ) < b₂ := hb₂mem
  set bb : ℝ := min b₁ b₂ with hbb
  have hbb0 : 0 < bb := lt_min hb₁0 hb₂0
  refine ⟨bb / 2, 1 * (3 * L / ‖dγ 0‖) + D * K, by linarith, by
      have : bb ≤ b₁ := min_le_left _ _
      linarith [hb₁b],
    add_nonneg (mul_nonneg zero_le_one (div_nonneg (by linarith) (norm_nonneg _)))
      (mul_nonneg hD0 hK0), ?_⟩
  intro η hη
  have hηlt : η < bb := by linarith [hη.2]
  have hη0 : η ≠ 0 := ne_of_gt hη.1
  have hη₁ : η ∈ Icc (0 : ℝ) b₁ := ⟨hη.1.le, le_trans hηlt.le (min_le_left _ _)⟩
  have hη₂ : η ∈ Ioc (0 : ℝ) b₂ := ⟨hη.1, le_trans hηlt.le (min_le_right _ _)⟩
  obtain ⟨⟨hBn, hEn⟩, hΨη⟩ := hb₂ hη₂
  have hηb : η ∈ Ioc (0 : ℝ) b :=
    ⟨hη.1, le_trans (le_trans hηlt.le (min_le_left _ _)) hb₁b⟩
  have hγd : HasDerivAt γ (dγ η) η := hd η hηb
  have hγn : γ η ≠ 0 := by
    have := hune η hη₁ hη0
    rw [endpointCofactor] at this
    exact fun h => this (by rw [h]; simp)
  have hfac : (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) =ᶠ[nhds η]
      fun s : ℝ => (-1 : ℂ) * ((s : ℂ) - (((0 : ℝ)) : ℂ)) ^ (1 : ℤ)
        * (endpointCofactor γ s) ^ (1 : ℤ) * A s := by
    filter_upwards [Ioo_mem_nhds hη.1 hηlt] with x hx
    have hx₁ : x ∈ Icc (0 : ℝ) b₁ := ⟨hx.1.le, le_trans hx.2.le (min_le_left _ _)⟩
    have hx₂ : x ∈ Ioc (0 : ℝ) b₂ := ⟨hx.1, le_trans hx.2.le (min_le_right _ _)⟩
    have hxb : x ∈ Ioc (0 : ℝ) b :=
      ⟨hx.1, le_trans (le_trans hx.2.le (min_le_left _ _)) hb₁b⟩
    obtain ⟨⟨-, hxE⟩, -⟩ := hb₂ hx₂
    have hxγ : γ x ≠ 0 := by
      have := hune x hx₁ (ne_of_gt hx.1)
      rw [endpointCofactor] at this
      exact fun h => this (by rw [h]; simp)
    exact ftAmp_eq_origin_factorization hr (ne_of_gt hx.1) hxγ hxE (hroot x hxb)
  have hBd := hasDerivAt_eval_comp B hγd
  have hEd := hasDerivAt_eval_comp E hγd
  have hAd : DifferentiableAt ℝ A η := hBd.differentiableAt.div hEd.differentiableAt hEn
  have hA0 : A η ≠ 0 := div_ne_zero hBn hEn
  have houter : |(logDeriv A η).im| ≤ D * K := by
    have hdb : ‖dγ η‖ ≤ D := by
      have hnb : ‖dγ η‖ ≤ ‖dγ 0‖ + ‖dγ η - dγ 0‖ := by
        simpa using norm_add_le (dγ 0) (dγ η - dγ 0)
      have hl := hlip η ⟨hη.1.le, hηb.2⟩
      have hLb : L * η ≤ L * b := by nlinarith [hηb.2]
      rw [hD]
      linarith
    calc |(logDeriv A η).im| ≤ ‖dγ η‖ * Ψ η := by
          rw [hA, hΨ]
          exact abs_im_logDeriv_polyRatio_le B E hγd hBn hEn
      _ ≤ D * K := mul_le_mul hdb hΨη.le (hΨnn η) hD0
  have hkey := abs_im_logDeriv_le_of_local_factorization_outer (θ₀ := (0 : ℝ))
    (m := (1 : ℤ)) (p := (1 : ℤ)) hη0 (by norm_num : (-1 : ℂ) ≠ 0) hfac
    (hudiff η hη₁ hη0) (hune η hη₁ hη0) hAd hA0 (hubd η hη₁ hη0) houter
  simpa using hkey

/-! ### The interior across the whole divisor -/

/-- **`exists_bound_of_finite_exceptional` with the local hypothesis stated as the
conclusion the per-zero estimates reach.**  Its own `hloc` quantifies over all of
`ℝ` with the membership inside, which is the tree's idiom for keeping the chosen
radius a total function; a caller holding one bound per member of the divisor has
to shuffle that by hand every time.  This does it once, and decouples the divisor
assembly from **how** each per-zero bound was obtained — which matters because
there are now two routes to one, according as the caller holds a Lipschitz collar
or only `γ''`. -/
theorem exists_bound_of_local_on_divisor {g : ℝ → ℝ} {a c : ℝ} {S : Finset ℝ}
    (hcont : ContinuousOn g (Icc a c \ ↑S))
    (hloc : ∀ z ∈ S, ∃ δ C : ℝ, 0 < δ ∧ ∀ θ, |θ - z| < δ → θ ≠ z → |g θ| ≤ C) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Icc a c, θ ∉ S → |g θ| ≤ κ := by
  classical
  refine exists_bound_of_finite_exceptional hcont ?_
  intro z
  by_cases hz : z ∈ S
  · obtain ⟨δ, C, hδ0, hbd⟩ := hloc z hz
    exact ⟨δ, hδ0, C, fun _ θ _ hθS hθz => hbd θ hθz (by rintro rfl; exact hθS hz)⟩
  · exact ⟨1, one_pos, 0, fun h => absurd h hz⟩

/-- **`eq:phase-derivative-bound` on the interior, across every amplitude zero at
once.**  `BoundAssembly.exists_bound_of_finite_exceptional` turns the per-zero
collars of `exists_bound_im_logDeriv_ftAmp_interior` into one constant: the
complement of the collars is compact and the function is continuous there, and
one `max` finishes.  The exceptional set is a `Finset` because the amplitude
divisor is — `eq:amplitude-zero-count` bounds it by `deg B`.

**Continuity off the divisor is the one thing the per-zero estimate does not
supply, and it is not a defect there.**  A bound near a zero needs `γ'` bounded;
continuity of `Im(W'/W)` away from the zeros needs `γ'` *continuous*, which the
branch modules carry on the open arc but which no local estimate should have to
assume.

**`S` must be the divisor itself and not the set of candidates for it.**  The
conclusion *excludes* `S`, while the region binder it feeds asks at every
parameter where the amplitude is nonzero — so a set larger than the zero set
leaves the binder unreachable at exactly the points of the excess.  The natural
candidate set, the arguments of the roots of `B` that land on the arc
(`AmplitudeBand`), is strictly larger: a root of `B` can have the right argument
without lying on the branch, and there the amplitude does not vanish.  Filtering
that finite set down to where the amplitude really is `0` fixes it and makes
`W θ ≠ 0 → θ ∉ S` immediate.  Nothing in the types distinguishes the two, and
`arg_mem_of_ftAmp_eq_zero` runs in the direction that does *not* settle it. -/
theorem exists_bound_im_logDeriv_ftAmp_interiorRegion {Q B : Polynomial ℂ} (hB : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) {γ dγ zf : ℝ → ℂ} {a c : ℝ} {S : Finset ℝ}
    (hcont : ContinuousOn (fun θ : ℝ => (deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) θ
        / ftAmp Q B r (zf θ) (γ θ)).im) (Icc a c \ ↑S))
    (hloc : ∀ z ∈ S, ∃ b L : ℝ, 0 < b ∧ 0 ≤ L ∧
      (∀ θ ∈ Icc (z - b) (z + b), HasDerivAt γ (dγ θ) θ) ∧
      (∀ θ ∈ Icc (z - b) (z + b), ‖dγ θ - dγ z‖ ≤ L * |θ - z|) ∧
      dγ z ≠ 0 ∧ γ z ≠ 0 ∧ (ftCritical Q r).eval (γ z) ≠ 0 ∧
      (∀ᶠ θ in nhds z, (ftDen Q r (zf θ)).eval (γ θ) = 0)) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Icc a c, θ ∉ S →
      |(deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) θ
          / ftAmp Q B r (zf θ) (γ θ)).im| ≤ κ := by
  refine exists_bound_of_local_on_divisor hcont fun z hz => ?_
  obtain ⟨b, L, hb, hL, hd, hlip, h0, hγ0, hEne, hroot⟩ := hloc z hz
  obtain ⟨δ, C, hδ0, -, hbd⟩ :=
    exists_bound_im_logDeriv_ftAmp_interior hB hr hb hL hd hlip h0 hγ0 hEne hroot
  exact ⟨δ, C, hδ0, hbd⟩

/-- **The same with the per-zero data reduced to `γ''`.**  What the branch modules
carry on the open arc is `γ` differentiable, `γ'` differentiable and `γ''`
continuous — not a collar and a Lipschitz constant.  This is the region bound
asking for exactly those, so nothing between the branch and `eq:phase-derivative-bound`
on the interior has to be built by hand. -/
theorem exists_bound_im_logDeriv_ftAmp_interiorRegion_of_deriv2 {Q B : Polynomial ℂ}
    (hB : B ≠ 0) {r : ℕ} (hr : 1 ≤ r) {γ dγ d2γ zf : ℝ → ℂ} {a c : ℝ} {S : Finset ℝ}
    {V : Set ℝ} (hVopen : IsOpen V)
    (hd : ∀ θ ∈ V, HasDerivAt γ (dγ θ) θ)
    (hd2 : ∀ θ ∈ V, HasDerivAt dγ (d2γ θ) θ)
    (hc2 : ∀ θ ∈ V, ContinuousAt d2γ θ)
    (hcont : ContinuousOn (fun θ : ℝ => (deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) θ
        / ftAmp Q B r (zf θ) (γ θ)).im) (Icc a c \ ↑S))
    (hloc : ∀ z ∈ S, z ∈ V ∧ dγ z ≠ 0 ∧ γ z ≠ 0 ∧ (ftCritical Q r).eval (γ z) ≠ 0 ∧
      (∀ᶠ θ in nhds z, (ftDen Q r (zf θ)).eval (γ θ) = 0)) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Icc a c, θ ∉ S →
      |(deriv (fun s : ℝ => ftAmp Q B r (zf s) (γ s)) θ
          / ftAmp Q B r (zf θ) (γ θ)).im| ≤ κ := by
  refine exists_bound_of_local_on_divisor hcont fun z hz => ?_
  obtain ⟨hzV, h0, hγ0, hEne, hroot⟩ := hloc z hz
  obtain ⟨δ, C, hδ0, -, hbd⟩ :=
    exists_bound_im_logDeriv_ftAmp_interior_of_deriv2 hB hr (hVopen.mem_nhds hzV) hd hd2
      (hc2 z hzV) h0 hγ0 hEne hroot
  exact ⟨δ, C, hδ0, hbd⟩

/-! ### Retired: the two seams the region binders no longer have

Neither lemma below is on any live route.  `BranchSupply` asks its first region on `Ioc`
and its third on `Ico`, so the collar's own interval **is** the binder's and there is no
seam to cross; what these charged for — `W(0) = 0` and `W(L) = 0`, a real obligation at a
simple endpoint root — is gone rather than discharged.  They are kept because an axiom
guard pins them and because `BranchSupply`'s docstring cites them as the record of what the
closed form cost, and they are sectioned off here so that a reader composing against the
region bounds does not reach for one by mistake. -/

/-- **The lower seam, retired.**  The collar bound runs on `(0, b]` — an argument
branch cannot be built through a zero of the amplitude, and `W` vanishes at the
endpoint whenever the exponent is positive.  When the region bound was asked on
`[0, b]` the two met only at `W(0) = 0`, which is what the caller owed rather than
something to be assumed silently: at a simple endpoint root the amplitude has a
genuine nonzero value there and the guard does not discharge itself.

**`BranchSupply` now asks that region on `Ioc`, so there is no seam to cross** —
the collar's interval is the binder's, and the obligation this lemma charged for
is gone rather than discharged.  That is also why the supply's `∀ B` block no
longer carries `hW0`.  Kept as the record of what the closed form cost; nothing
in the tree consumes it. -/
theorem forall_Icc_of_Ioc_of_eq_zero {W : ℝ → ℂ} {f : ℝ → ℝ} {b κ : ℝ}
    (h0 : W 0 = 0) (h : ∀ s ∈ Ioc (0 : ℝ) b, |f s| ≤ κ) :
    ∀ s ∈ Icc (0 : ℝ) b, W s ≠ 0 → |f s| ≤ κ := by
  intro s hs hW
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · exact absurd (by rw [← hs0] at hW ⊢; exact h0) hW
  · exact h s ⟨hs0, hs.2⟩

/-- **The upper seam**, the same statement at the far end of the arc. -/
theorem forall_Icc_of_Ico_of_eq_zero {W : ℝ → ℂ} {f : ℝ → ℝ} {a L κ : ℝ}
    (h0 : W L = 0) (h : ∀ s ∈ Ico a L, |f s| ≤ κ) :
    ∀ s ∈ Icc a L, W s ≠ 0 → |f s| ≤ κ := by
  intro s hs hW
  rcases eq_or_lt_of_le hs.2 with hsL | hsL
  · exact absurd (by rw [hsL]; exact h0) hW
  · exact h s ⟨hs.1, hsL⟩

/-! ### The hypotheses are meetable -/

/-- A pencil whose branch can be written down: `D(t,z) = (t-2) + z t`. -/
private noncomputable def witnessQ : Polynomial ℂ := Polynomial.X - Polynomial.C 2

/-- A numerator vanishing at the branch point, so the witness exhibits an actual
zero of the amplitude rather than a point where the theorem says nothing. -/
private noncomputable def witnessB : Polynomial ℂ := Polynomial.X - Polynomial.C 1

/-- The branch, affine, entering the point `1` at parameter `0`. -/
private noncomputable def witnessBranch (θ : ℝ) : ℂ := (θ : ℂ) + 1

/-- The spectral parameter that puts the branch on the root locus: solving
`D(γ,z) = 0` for `z` is a division, and it is legitimate exactly where `γ ≠ 0`. -/
private noncomputable def witnessZ (θ : ℝ) : ℂ :=
  -(witnessQ.eval (witnessBranch θ)) / (witnessBranch θ) ^ 1

private theorem hasDerivAt_witnessBranch (θ : ℝ) : HasDerivAt witnessBranch 1 θ := by
  have hb : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  exact hb.add_const (1 : ℂ)

private theorem witnessBranch_ne_zero_near :
    ∀ᶠ θ in nhds (0 : ℝ), witnessBranch θ ≠ 0 :=
  (hasDerivAt_witnessBranch 0).continuousAt.eventually_ne (by simp [witnessBranch])

private theorem witnessRoot :
    ∀ᶠ θ in nhds (0 : ℝ), (ftDen witnessQ 1 (witnessZ θ)).eval (witnessBranch θ) = 0 := by
  filter_upwards [witnessBranch_ne_zero_near] with θ hθ
  rw [ftDen_eval, witnessZ]
  field

private theorem witnessCritical :
    (ftCritical witnessQ 1).eval (witnessBranch 0) ≠ 0 := by
  simp [eval_ftCritical, witnessQ, witnessBranch]

/-- **The interior bound's binder bundle is simultaneously satisfiable, at a
parameter where the amplitude really vanishes.**  A theorem stated at a
regularity no branch has, or about a point that is not a zero, would be green and
say nothing; both are ruled out here.  `witnessB` vanishes at the branch point, so
`W(0) = 0` and the collar is around an actual member of the divisor. -/
theorem exists_bound_im_logDeriv_ftAmp_interior_witness :
    ftAmp witnessQ witnessB 1 (witnessZ 0) (witnessBranch 0) = 0 ∧
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ θ, |θ - 0| < δ → θ ≠ 0 →
        |(deriv (fun s : ℝ => ftAmp witnessQ witnessB 1 (witnessZ s) (witnessBranch s)) θ
            / ftAmp witnessQ witnessB 1 (witnessZ θ) (witnessBranch θ)).im| ≤ C := by
  refine ⟨by simp [ftAmp, witnessB, witnessBranch], ?_⟩
  refine exists_bound_im_logDeriv_ftAmp_interior (Q := witnessQ) (B := witnessB)
    (γ := witnessBranch) (dγ := fun _ => 1) (zf := witnessZ) (b := 1) (L := 0)
    (show witnessB ≠ 0 from Polynomial.X_sub_C_ne_zero (1 : ℂ)) le_rfl one_pos le_rfl
    (fun θ _ => hasDerivAt_witnessBranch θ) (fun θ _ => by simp)
    one_ne_zero (by simp [witnessBranch]) witnessCritical witnessRoot

/-- **The endpoint bundle is simultaneously satisfiable too.**  The same pencil,
read at its endpoint `t_e = γ(0) = 1`, which is a *simple* root of the denominator
— so `E` does not degenerate there, `m = 0`, and the exponent is `ν = 1`.  A
witness at `m = 0` is the one that matters here: it is the boundary value of the
`ℕ` parameter, where `k - 1` would mean something else if the exponent were
recomputed rather than supplied.

`hEfac` reads `E = (X - C t_e)^0 * H` with `H = E`, which is not degenerate use of
the hypothesis but the honest statement that at a simple endpoint the `z`-free
factor carries no zero at all. -/
theorem exists_bound_im_logDeriv_ftAmp_endpoint_witness :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ 1 ∧ 0 ≤ C ∧
      ∀ δ ∈ Ioc (0 : ℝ) b',
        |(deriv (fun s : ℝ => ftAmp witnessQ witnessB 1 (witnessZ s) (witnessBranch s)) δ
            / ftAmp witnessQ witnessB 1 (witnessZ δ) (witnessBranch δ)).im| ≤ C := by
  have hroot : ∀ δ ∈ Ioc (0 : ℝ) 1,
      (ftDen witnessQ 1 (witnessZ δ)).eval (witnessBranch δ) = 0 := by
    intro δ hδ
    have hne : witnessBranch δ ≠ 0 := by
      have : (0 : ℝ) < δ + 1 := by linarith [hδ.1]
      simpa [witnessBranch, Complex.ext_iff] using this.ne'
    rw [ftDen_eval, witnessZ]
    field
  refine exists_bound_im_logDeriv_ftAmp_endpoint (Q := witnessQ) (B := witnessB)
    (γ := witnessBranch) (dγ := fun _ => 1) (zf := witnessZ) (te := 1)
    (H := ftCritical witnessQ 1) (m := 0) (b := 1) (L := 0)
    (show witnessB ≠ 0 from Polynomial.X_sub_C_ne_zero (1 : ℂ)) le_rfl one_pos le_rfl
    (by simp) (by simpa [witnessBranch] using witnessCritical) one_ne_zero (by simp [witnessBranch])
    ((hasDerivAt_witnessBranch 0).hasDerivWithinAt)
    (fun θ _ => hasDerivAt_witnessBranch θ) (fun θ _ => by simp) one_ne_zero hroot

/-! ### The upper endpoint is the lower one reflected -/

/-- **Reflecting the arc negates the logarithmic derivative and nothing else.**
`exists_bound_im_logDeriv_ftAmp_endpoint` is stated in the *distance* to the
endpoint, so it reaches the upper end of the arc through `δ ↦ π/r - δ` — a
caller supplies the reflected branch and the reflected spectral parameter and
gets back a statement about `δ`.  What has to be said once is how that statement
reads in `θ`: the chain rule contributes a factor of `-1`, which survives into
the imaginary part and dies under the absolute value. -/
theorem im_logDeriv_reflect (W : ℝ → ℂ) (c θ : ℝ) :
    (deriv (fun s : ℝ => W (c - s)) (c - θ) / W θ).im = -(deriv W θ / W θ).im := by
  have hderiv : deriv (fun s : ℝ => W (c - s)) (c - θ) = -deriv W θ := by
    rw [deriv_comp_const_sub, sub_sub_cancel]
  rw [hderiv, neg_div, Complex.neg_im]

/-- **The upper collar in the arc's own parameter.**  The bound
`exists_bound_im_logDeriv_ftAmp_endpoint` produces for the reflected data on
`(0, b]` is the bound on `[c - b, c)` for the original, which is the half-open
interval the third region binder now asks on directly.  The endpoint `c` itself is
excluded here for the same reason `0` is at the other end — an argument branch
cannot be built through a zero of the amplitude — and since that binder moved to
`Ico`, no seam has to be crossed after this. -/
theorem forall_Ico_of_reflected {W : ℝ → ℂ} {c b κ : ℝ}
    (h : ∀ δ ∈ Ioc (0 : ℝ) b,
      |(deriv (fun s : ℝ => W (c - s)) δ / W (c - δ)).im| ≤ κ) :
    ∀ θ ∈ Ico (c - b) c, |(deriv W θ / W θ).im| ≤ κ := by
  intro θ hθ
  have hmem : c - θ ∈ Ioc (0 : ℝ) b := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hkey := h (c - θ) hmem
  rw [sub_sub_cancel, im_logDeriv_reflect, abs_neg] at hkey
  exact hkey

/-! ### The arc's derivative data does not reach its endpoints -/

/-- **`exists_phase_family_of_bound` with the derivative data asked on the OPEN
arc.**  `EndpointCofactorBound.exists_phase_family_of_bound` asks for
`HasDerivAt W (dW s) s` on an open set containing `[0, L]`, and at the
Forgács–Tran amplitude that binder **cannot be met at `L = π/r`**: where the
`z`-free factor `E` degenerates at an endpoint the amplitude blows up there, so
`W` is unbounded on every neighbourhood of the endpoint while Lean's `W` takes a
finite junk value at it, and no derivative exists.
`../scripts/check_arc_phase_bound.py` (D4) measures the divergence at the cubic
pencil, where `|W| ∼ θ^{-2}`.

**What replaces the missing data is the nonvanishing the blocks already carry.**
A block on which `W` does not vanish cannot contain an endpoint at which `W`
does, so `hW0` and `hWL` push every admissible block into the open arc — where
the branch modules do supply the derivative and its continuity.  The two extra
hypotheses are the same fact the two seam lemmas above ask for, and they are
facts about the amplitude rather than about the blocks.

Everything else is `exists_phase_family_of_bound` unchanged: `M₀ = ⌈κ⌉` is fixed
before the family, the branch on block `i` is `polarAngle W dW 0 (Lb i)` and so is
exhibited rather than chosen, and its derivative `Im(W'/W)` does not depend on `i`
at all. -/
theorem exists_phase_family_hasDerivAt_of_bound_of_open {W dW : ℝ → ℂ} {U : Set ℝ} {L κ : ℝ}
    (hU : IsOpen U) (hsub : Ioo (0 : ℝ) L ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (hW0 : W 0 = 0) (hWL : W L = 0)
    (hbd : ∀ s ∈ Icc (0 : ℝ) L, W s ≠ 0 → |(dW s / W s).im| ≤ κ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) L) → (∀ i, Rb i ∈ Icc (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) →
      ∃ ψ : Fin k → ℝ → ℝ,
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = ((‖W θ‖ : ℝ) : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          HasDerivAt (ψ i) ((dW θ / W θ).im) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          |(dW θ / W θ).im| < (M : ℝ) + 1) := by
  obtain ⟨M₀, hM₀⟩ := exists_threshold_of_bound (κ := κ)
  refine ⟨M₀, fun M hM k Lb Rb hL hR hne => ?_⟩
  refine ⟨fun i => polarAngle W dW 0 (Lb i), ?_, ?_, ?_⟩
  all_goals
    intro i hi θ hθ
  all_goals
    have hblk : Icc (Lb i) (Rb i) ⊆ Icc (0 : ℝ) L := fun x hx =>
      ⟨le_trans (hL i).1 hx.1, le_trans hx.2 (hR i).2⟩
  -- a block on which `W` does not vanish cannot reach an endpoint at which it does
  all_goals
    have hopen : Icc (Lb i) (Rb i) ⊆ U := by
      intro x hx
      refine hsub ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le (hblk hx).1 with h | h
        · exact absurd (show W x = 0 by rw [← h]; exact hW0) (hne i hi x hx)
        · exact h
      · rcases eq_or_lt_of_le (hblk hx).2 with h | h
        · exact absurd (show W x = 0 by rw [h]; exact hWL) (hne i hi x hx)
        · exact h
  · have h := polar_decomposition (β := (0 : ℂ)) hi.le hU hopen hd hc
      (fun x hx => hne i hi x hx) hθ
    rw [sub_zero] at h
    rwa [polarModulus_eq_norm hi.le hU hopen hd hc (fun x hx => hne i hi x hx) hθ] at h
  · have h := hasDerivAt_polarAngle (β := (0 : ℂ)) hU hopen hd hc
      (fun x hx => hne i hi x hx) hθ
    simpa using h
  · exact hM₀ M hM _ (hbd θ (hblk hθ) (hne i hi θ hθ))

/-- **The three regions composed against the open-arc assembly.**  The twin of
`exists_phase_family_of_regions` for the case the amplitude actually presents:
derivative data on the open arc, and the two endpoint values supplied as the
facts they are. -/
theorem exists_phase_family_hasDerivAt_of_regions_of_open {W dW : ℝ → ℂ} {U : Set ℝ}
    {L b₁ b₂ κ₁ κ₂ κ₃ : ℝ}
    (hU : IsOpen U) (hsub : Ioo (0 : ℝ) L ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (hW0 : W 0 = 0) (hWL : W L = 0)
    (h₁ : ∀ s ∈ Icc (0 : ℝ) b₁, W s ≠ 0 → |(dW s / W s).im| ≤ κ₁)
    (h₂ : ∀ s ∈ Icc b₁ b₂, W s ≠ 0 → |(dW s / W s).im| ≤ κ₂)
    (h₃ : ∀ s ∈ Icc b₂ L, W s ≠ 0 → |(dW s / W s).im| ≤ κ₃) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) L) → (∀ i, Rb i ∈ Icc (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) →
      ∃ ψ : Fin k → ℝ → ℝ,
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = ((‖W θ‖ : ℝ) : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          HasDerivAt (ψ i) ((dW θ / W θ).im) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          |(dW θ / W θ).im| < (M : ℝ) + 1) :=
  exists_phase_family_hasDerivAt_of_bound_of_open hU hsub hd hc hW0 hWL
    (abs_le_of_cover_three_of_ne_zero h₁ h₂ h₃)

/-! ### The phase derivative bound under its own existential

The two theorems below are the ones above with `ψ'` bound rather than named.  They
are what `AngularDiscrepancyFT.FTPhaseSupply` states — `∃ ψ dψ` — so a consumer
assembling the supply meets them in this shape; but a consumer that also needs the
**variation** of `ψ` has to know that `ψ' = Im(W'/W)`, and under the existential
that fact is not in the statement even though the proof supplies it.  Recovering it
from outside takes a mean value argument on `W e^{-i\psi}`, which is a whole lemma
spent re-deriving what was already known one level down.

So the named forms are the ones to compose against, and these two are kept for the
shape `FTPhaseSupply` is written in. -/

/-- `exists_phase_family_hasDerivAt_of_bound_of_open` with the phase derivative
existentially bound. -/
theorem exists_phase_family_of_bound_of_open {W dW : ℝ → ℂ} {U : Set ℝ} {L κ : ℝ}
    (hU : IsOpen U) (hsub : Ioo (0 : ℝ) L ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (hW0 : W 0 = 0) (hWL : W L = 0)
    (hbd : ∀ s ∈ Icc (0 : ℝ) L, W s ≠ 0 → |(dW s / W s).im| ≤ κ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) L) → (∀ i, Rb i ∈ Icc (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) →
      ∃ ψ dψ : Fin k → ℝ → ℝ,
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = ((‖W θ‖ : ℝ) : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) := by
  obtain ⟨M₀, hM₀⟩ := exists_phase_family_hasDerivAt_of_bound_of_open hU hsub hd hc hW0 hWL hbd
  refine ⟨M₀, fun M hM k Lb Rb hL hR hne => ?_⟩
  obtain ⟨ψ, h1, h2, h3⟩ := hM₀ M hM k Lb Rb hL hR hne
  exact ⟨ψ, fun _ θ => (dW θ / W θ).im, h1, h2, h3⟩

/-- `exists_phase_family_hasDerivAt_of_regions_of_open` with the phase derivative
existentially bound. -/
theorem exists_phase_family_of_regions_of_open {W dW : ℝ → ℂ} {U : Set ℝ}
    {L b₁ b₂ κ₁ κ₂ κ₃ : ℝ}
    (hU : IsOpen U) (hsub : Ioo (0 : ℝ) L ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (hW0 : W 0 = 0) (hWL : W L = 0)
    (h₁ : ∀ s ∈ Icc (0 : ℝ) b₁, W s ≠ 0 → |(dW s / W s).im| ≤ κ₁)
    (h₂ : ∀ s ∈ Icc b₁ b₂, W s ≠ 0 → |(dW s / W s).im| ≤ κ₂)
    (h₃ : ∀ s ∈ Icc b₂ L, W s ≠ 0 → |(dW s / W s).im| ≤ κ₃) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) L) → (∀ i, Rb i ∈ Icc (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) →
      ∃ ψ dψ : Fin k → ℝ → ℝ,
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = ((‖W θ‖ : ℝ) : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) :=
  exists_phase_family_of_bound_of_open hU hsub hd hc hW0 hWL
    (abs_le_of_cover_three_of_ne_zero h₁ h₂ h₃)

/-! ### The chord's angular velocity, per root of the numerator -/

/-- **`Im(γ'/(γ-β))` is bounded near a parameter the arc meets `β` at.**
`γ - β = (θ - m)·h(θ)` with `h` the divided difference, so
`γ'/(γ-β) = 1/(θ-m) + h'/h` — the first term is **real** and drops out of the imaginary
part, and the second is the divided-difference estimate.

This is the same cancellation as `eq:W-local-zero`, at the bare chord rather than at the
amplitude: a root of `B` on the arc makes `W'/W` blow up and leaves `Im(W'/W)` alone. -/
theorem exists_bound_im_chord_at_meet {γ dγ : ℝ → ℂ} {m b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hd : ∀ θ ∈ Icc (m - b) (m + b), HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (m - b) (m + b), ‖dγ θ - dγ m‖ ≤ L * |θ - m|)
    (h0 : dγ m ≠ 0) {β : ℂ} (hmβ : γ m = β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ, |θ - m| < δ → θ ≠ m →
      |(dγ θ / (γ θ - β)).im| ≤ 3 * L / ‖dγ m‖ := by
  obtain ⟨b', hb'0, hb'b, hune, hudiff, hubd⟩ :=
    exists_bound_im_logDeriv_centeredCofactor hb hL hd hlip h0
  refine ⟨b', hb'0, fun θ hθ hθm => ?_⟩
  have hle : |θ - m| ≤ b' := hθ.le
  have habs := abs_le.1 (le_trans hle hb'b)
  have hmem : θ ∈ Icc (m - b) (m + b) := ⟨by linarith [habs.1], by linarith [habs.2]⟩
  -- `γ - β` factors as the real power times the divided difference
  have hfac : (fun s : ℝ => γ s - β)
      =ᶠ[nhds θ] fun s : ℝ => (1 : ℂ) * ((s : ℂ) - (m : ℂ)) ^ (1 : ℤ)
        * (centeredCofactor γ m s) ^ (1 : ℤ) * (fun _ : ℝ => (1 : ℂ)) s := by
    refine Filter.Eventually.of_forall fun s => ?_
    have hs : γ s - β = ((s : ℂ) - (m : ℂ)) * centeredCofactor γ m s := by
      rw [← hmβ]; exact sub_eq_mul_centeredCofactor γ m s
    simp only [zpow_one, one_mul, mul_one]
    exact hs
  have hkey := abs_im_logDeriv_le_of_local_factorization_outer (θ₀ := m) (m := (1 : ℤ))
    (p := (1 : ℤ)) (A := fun _ : ℝ => (1 : ℂ)) (κ' := 0) hθm one_ne_zero hfac
    (hudiff θ hle hθm) (hune θ hle hθm) (differentiableAt_const _) one_ne_zero
    (hubd θ hle hθm) (by simp)
  have hderiv : deriv (fun s : ℝ => γ s - β) θ = dγ θ := ((hd θ hmem).sub_const β).deriv
  rw [hderiv] at hkey
  simpa using hkey

/-- **The chord's angular velocity is bounded where the arc misses `β`.**  Pure
compactness: the chord is bounded away from zero and the tangent is bounded. -/
theorem exists_bound_im_chord_of_miss {γ dγ : ℝ → ℂ} {a b : ℝ} {β : ℂ}
    (hγc : ContinuousOn γ (Icc a b)) (hdc : ContinuousOn dγ (Icc a b))
    (hne : ∀ s ∈ Icc a b, γ s ≠ β) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s ∈ Icc a b, |(dγ s / (γ s - β)).im| ≤ c := by
  have hcont : ContinuousOn (fun s => ‖dγ s‖ / ‖γ s - β‖) (Icc a b) :=
    hdc.norm.div (hγc.sub continuousOn_const).norm
      fun s hs => norm_ne_zero_iff.2 (sub_ne_zero.2 (hne s hs))
  obtain ⟨c, hc⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|c|, abs_nonneg c, fun s hs => ?_⟩
  calc |(dγ s / (γ s - β)).im| ≤ ‖dγ s / (γ s - β)‖ := Complex.abs_im_le_norm _
    _ = ‖dγ s‖ / ‖γ s - β‖ := norm_div _ _
    _ ≤ |c| := le_trans (by simpa using hc s hs) (le_abs_self c)

/-- **The third state: a root of `B` sitting at a collision.**  `miss_or_meet_once` gives
two states relative to the arc, but a *meeting at an arc endpoint* is a third case for the
estimate, because only one side of the parameter exists there.  The cancellation is the
same — `γ - β = δ·u(δ)` with `u` the divided difference, so `γ'/(γ-β) = 1/δ + u'/u` and
the real term drops out — and only the collar version of the divided-difference bound is
used, which is one-sided by construction.

**The three hypotheses are stated in the shape the branch modules produce them**, so this
plugs in unchanged: `hd0` is the branch's one-sided derivative at the collision with the
collision's *true* value rather than the derivative formula's, `h0` its nonvanishing, and
`hlip` the Lipschitz binder.  Nothing here reads a derivative formula at the collision,
which is where that value is junk.

**At the lower endpoint this instantiates at a repeated smallest zero and not at a simple
one, and the reason is geometric rather than a missing proof.**  `BranchSupplyGeometry`
supplies `hd0` under `2 ≤ ρ`, where the branch runs into `a_i` itself and `γ(0) = a_i` can
be a root of `B`.  At `ρ = 1` the branch runs into a *different point*: its limit `L` sits
strictly inside the first gap and misses every zero of the pencil
(`LowerEndpointSimpleZero.ftPrincipal_lower_endpoint_ne_root`), so unless `B` itself has a
root at `L` there is no collision at that endpoint at all and
`exists_bound_im_chord_of_miss` is the applicable state.  So a reader should not take
"the collision case" as covering every admissible pencil, and should not expect the
`2 ≤ ρ` producer to extend by continuity — `LowerEndpointSimpleZero.endpointSlope_rho_one`
records what its slope formula returns at `ρ = 1`.

**This is not on the region-bound path, and should not be scoped as a prerequisite for
it.**  The three region bounds cover their endpoint intervals through
`exists_bound_im_logDeriv_ftAmp_endpoint`, which takes the same three binders and covers
strictly more: it reads `ν = B.rootMultiplicity te` and divides that factor out, so a root
of `B` *at* the endpoint is inside its scope rather than a case beyond it.  Splitting the
numerator off the cofactor there is the wrong move in any case — the cofactor vanishes at
the endpoint too, and it is precisely the two zeros combining into one real power that
makes `Im(W'/W)` bounded, so separating them discards the cancellation the statement rests
on.  On the *open* arc, which is where `RootBranchState` lives, a root can only miss or
meet once, so the states path reaches the other two lemmas and not this one.

What this states is the third root state itself, and it stays for that reason.

The upper endpoint is this reflected, by `forall_Ico_of_reflected`. -/
theorem exists_bound_im_chord_at_collision {γ dγ : ℝ → ℂ} {b L : ℝ} {β : ℂ}
    (hb : 0 < b) (hL : 0 ≤ L) (hγ0 : γ 0 = β)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0) :
    ∃ b' : ℝ, 0 < b' ∧ b' ≤ b ∧ ∀ θ ∈ Icc (0 : ℝ) b', θ ≠ 0 →
      |(dγ θ / (γ θ - β)).im| ≤ 3 * L / ‖dγ 0‖ := by
  set g : ℝ → ℂ := fun s => γ s - β with hg
  have hg0 : g 0 = 0 := by rw [hg]; simp [hγ0]
  obtain ⟨b', hb'0, hb'b, hune, hudiff, hubd⟩ :=
    exists_bound_im_logDeriv_endpointCofactor (γ := g) (dγ := dγ) hb hL hg0
      (by simpa [hg] using hd0.sub_const β)
      (fun θ hθ => by simpa [hg] using (hd θ hθ).sub_const β) hlip h0
  refine ⟨b', hb'0, hb'b, fun θ hθ hθ0 => ?_⟩
  -- `g` factors as the real power times the divided difference, at every parameter
  have hfac : g =ᶠ[nhds θ] fun s : ℝ => (1 : ℂ) * ((s : ℂ) - (((0 : ℝ)) : ℂ)) ^ (1 : ℤ)
      * (endpointCofactor g s) ^ (1 : ℤ) * (fun _ : ℝ => (1 : ℂ)) s := by
    refine Filter.Eventually.of_forall fun s => ?_
    simp only [zpow_one, one_mul, mul_one, Complex.ofReal_zero, sub_zero, endpointCofactor]
    rcases eq_or_ne s 0 with rfl | hs
    · simp [hg0]
    · have hsc : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
      field_simp
  have hkey := abs_im_logDeriv_le_of_local_factorization_outer (θ₀ := (0 : ℝ))
    (m := (1 : ℤ)) (p := (1 : ℤ)) (A := fun _ : ℝ => (1 : ℂ)) (κ' := 0) hθ0 one_ne_zero
    hfac (hudiff θ hθ hθ0) (hune θ hθ hθ0) (differentiableAt_const _) one_ne_zero
    (hubd θ hθ hθ0) (by simp)
  have hderiv : deriv g θ = dγ θ :=
    ((hd θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), le_trans hθ.2 hb'b⟩).sub_const β).deriv
  rw [hderiv] at hkey
  simpa [hg] using hkey

end ForgacsTran
