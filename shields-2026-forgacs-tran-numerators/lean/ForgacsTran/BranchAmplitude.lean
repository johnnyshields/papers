/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchCurvature
import ForgacsTran.PrincipalSimpleBranch
import ForgacsTran.ConsequencesComposition.ClockSpacing
import ForgacsTran.ViewingAngle

/-!
# The principal amplitude in `C²` along the general branch

`eq:local-strong-clock`'s `O(M^{-3})` term consumes bounds on `ψ'` and `ψ''`
with `ψ = arg W`, and `CubicClockSpacing` supplies them at one pencil by writing
`τ` in closed form.  That route is unavailable in general, where `τ` is only
implicitly defined.  What replaces it is `Amplitude.ftAmp_eq_ftCritical`:
`W = -tB(t)/E(t)` with `E = ftCritical Q r`, a **fixed rational function of the
branch point alone**, `z`-free.  So `W` along the branch is that rational
function composed with `γ`, and `BranchCurvature` already puts `γ` in `C²`.

**No second-order theory of `z` is involved.**  `z` enters only through the
root relation that identifies `W` with the rational function; it does not appear
in the function being differentiated.

## Main statements

* `hasDerivAt_polyQuot` — the quotient rule for two polynomials, in the form
  that iterates: the derivative of `p/q` is again a quotient of polynomials,
  `polyQuotNum p q` over `q^2`.
* `hasDerivAt_ftRatComp`, `hasDerivAt_ftRatCompDeriv` — a polynomial quotient
  composed with a `C²` curve, twice.
* `hasDerivAt_ftBranchAmp`, `hasDerivAt_ftBranchAmpDeriv` — `W` in `C²` along
  the branch of `Forgacs2017RationalDenominator` Eq. (21), with no hypothesis
  beyond the admissible class.
* `ftBranchAmp_eq_ftAmp` — that function is the paper's `𝒲` at the branch.
* `exists_branch_phase_bounds` — `eq:phase-derivative-bound`'s `κ` and
  `eq:local-strong-clock`'s `κ_2` at the general admissible pencil, on a compact
  subarc of `(0, π/r)` on which `B` does not vanish along the branch.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Local phase
quantization and strong-clock spacing» (`subsec:strong-clock`,
`prop:local-strong-clock`, `eq:phase-derivative-bound`), over «Spectral
geometry, residues, and the principal amplitude» (`sec:geometry`,
`eq:residue-amplitude`, `eq:Dprime-identity`).

## Tags

principal amplitude, branch regularity, second derivative, phase bound
-/

namespace ForgacsTran

open Real Set Polynomial

/-! ### A quotient of two polynomials, differentiated repeatedly

The derivative of `p/q` is `(p'q - pq')/q^2`, whose numerator and denominator
are again polynomials.  Keeping that shape is what lets the second derivative be
the same construction applied twice, with no new algebra at the second step. -/

/-- The numerator of `(p/q)'`. -/
noncomputable def polyQuotNum (p q : Polynomial ℂ) : Polynomial ℂ :=
  derivative p * q - p * derivative q

/-- **The quotient rule, in the shape that iterates.** -/
theorem hasDerivAt_polyQuot {p q : Polynomial ℂ} {t : ℂ} (hq : q.eval t ≠ 0) :
    HasDerivAt (fun s : ℂ => p.eval s / q.eval s)
      ((polyQuotNum p q).eval t / (q ^ 2).eval t) t := by
  refine ((p.hasDerivAt t).div (q.hasDerivAt t) hq).congr_deriv ?_
  simp [polyQuotNum]

/-! ### The same, composed with a curve

`W` is a polynomial quotient evaluated at `γ(θ)`, so its two derivatives are the
chain rule over `hasDerivAt_polyQuot`.  Nothing here knows about the branch. -/

/-- A polynomial quotient read along a curve. -/
noncomputable def ftRatComp (p q : Polynomial ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  p.eval (γ θ) / q.eval (γ θ)

/-- Its derivative, `γ'·(p/q)'(γ)`. -/
noncomputable def ftRatCompDeriv (p q : Polynomial ℂ) (γ dγ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  dγ θ * ftRatComp (polyQuotNum p q) (q ^ 2) γ θ

/-- Its second derivative, `γ''·(p/q)'(γ) + (γ')²·(p/q)''(γ)`. -/
noncomputable def ftRatCompDeriv2 (p q : Polynomial ℂ) (γ dγ ddγ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ddγ θ * ftRatComp (polyQuotNum p q) (q ^ 2) γ θ
    + dγ θ ^ 2 * ftRatComp (polyQuotNum (polyQuotNum p q) (q ^ 2)) ((q ^ 2) ^ 2) γ θ

theorem hasDerivAt_ftRatComp {p q : Polynomial ℂ} {γ dγ : ℝ → ℂ} {θ : ℝ}
    (hγ : HasDerivAt γ (dγ θ) θ) (hq : q.eval (γ θ) ≠ 0) :
    HasDerivAt (ftRatComp p q γ) (ftRatCompDeriv p q γ dγ θ) θ := by
  refine ((hasDerivAt_polyQuot (p := p) (q := q) hq).comp θ hγ).congr_deriv ?_
  rw [ftRatCompDeriv, ftRatComp]
  ring

theorem hasDerivAt_ftRatCompDeriv {p q : Polynomial ℂ} {γ dγ ddγ : ℝ → ℂ} {θ : ℝ}
    (hγ : HasDerivAt γ (dγ θ) θ) (hdγ : HasDerivAt dγ (ddγ θ) θ)
    (hq : q.eval (γ θ) ≠ 0) :
    HasDerivAt (ftRatCompDeriv p q γ dγ) (ftRatCompDeriv2 p q γ dγ ddγ θ) θ := by
  have hq2 : (q ^ 2).eval (γ θ) ≠ 0 := by
    rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hq
  refine (hdγ.mul (hasDerivAt_ftRatComp (p := polyQuotNum p q) (q := q ^ 2)
    hγ hq2)).congr_deriv ?_
  rw [ftRatCompDeriv2, ftRatCompDeriv]
  ring

theorem continuousAt_ftRatComp {p q : Polynomial ℂ} {γ : ℝ → ℂ} {θ : ℝ}
    (hγ : ContinuousAt γ θ) (hq : q.eval (γ θ) ≠ 0) :
    ContinuousAt (ftRatComp p q γ) θ :=
  ((Polynomial.continuous p).continuousAt.comp hγ).div
    ((Polynomial.continuous q).continuousAt.comp hγ) hq

theorem continuousAt_ftRatCompDeriv2 {p q : Polynomial ℂ} {γ dγ ddγ : ℝ → ℂ} {θ : ℝ}
    (hγ : ContinuousAt γ θ) (hdγ : ContinuousAt dγ θ) (hddγ : ContinuousAt ddγ θ)
    (hq : q.eval (γ θ) ≠ 0) :
    ContinuousAt (ftRatCompDeriv2 p q γ dγ ddγ) θ := by
  have hq2 : (q ^ 2).eval (γ θ) ≠ 0 := by
    rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hq
  have hq4 : ((q ^ 2) ^ 2).eval (γ θ) ≠ 0 := by
    rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hq2
  exact (hddγ.mul (continuousAt_ftRatComp hγ hq2)).add
    ((hdγ.pow 2).mul (continuousAt_ftRatComp hγ hq4))

/-! ### `eq:Dprime-identity` read as a polynomial quotient

`ftAmp_eq_ftCritical` writes `𝒲 = -tB(t)/E(t)`.  Both sides of that fraction are
polynomials in the branch point, so the amplitude along the branch is exactly the
composition the previous section differentiates. -/

/-- The numerator of `eq:Dprime-identity`'s amplitude form, `N(t) = -tB(t)`. -/
noncomputable def ftAmpNum (B : Polynomial ℂ) : Polynomial ℂ := -(X * B)

@[simp] theorem eval_ftAmpNum (B : Polynomial ℂ) (t : ℂ) :
    (ftAmpNum B).eval t = -(t * B.eval t) := by simp [ftAmpNum]

/-- **`eq:residue-amplitude` is a fixed polynomial quotient of the branch
point.**  The pencil parameter `z` occurs only in the root hypothesis; the
function on the right knows nothing about it. -/
theorem ftAmp_eq_ratio {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {z t : ℂ}
    (ht : t ≠ 0) (hroot : (ftDen Q r z).eval t = 0) :
    ftAmp Q B r z t = (ftAmpNum B).eval t / (ftCritical Q r).eval t := by
  rw [ftAmp_eq_ftCritical hr ht hroot, eval_ftAmpNum]


/-! ### Continuity of `τ''` and of `γ''`

`BranchCurvature` puts `γ` in `C²` but says nothing about whether `γ''` is
*continuous*, and a derivative need not be.  Every ingredient of `ftTauDeriv2` is
an explicit trigonometric quotient in `θ_k(τ(θ),θ)`, `τ(θ)` and `θ`, so
continuity is the composition rule over `hasDerivAt_ftAngle_comp` and the two
denominators `τ > 0`, `\sinθ > 0` — plus `∂_τ(∑θ_k) < 0`, which is the same
nonvanishing the implicit-function step already used. -/

section Curvature

variable {a : ℝ} {u : ℝ → ℝ} {θ : ℝ}

theorem continuousAt_ftAngleDeriv2Tau_comp (hu : ContinuousAt u θ)
    (hy : ContinuousAt (fun t => ftAngle a (u t) t) θ) (hupos : 0 < u θ)
    (hθ : θ ∈ Ioo 0 π) :
    ContinuousAt (fun t => ftAngleDeriv2Tau a (u t) t) θ := by
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hne : u θ ^ 4 * Real.sin θ ^ 2 ≠ 0 := by positivity
  simp only [ftAngleDeriv2Tau]
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hne

theorem continuousAt_ftAngleDeriv2AngleTau_comp (hu : ContinuousAt u θ)
    (hy : ContinuousAt (fun t => ftAngle a (u t) t) θ) (hupos : 0 < u θ)
    (hθ : θ ∈ Ioo 0 π) :
    ContinuousAt (fun t => ftAngleDeriv2AngleTau a (u t) t) θ := by
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hne2 : u θ ^ 2 * Real.sin θ ≠ 0 := by positivity
  simp only [ftAngleDeriv2AngleTau]
  exact ContinuousAt.div (ContinuousAt.mul
    (ContinuousAt.neg (ContinuousAt.div (by fun_prop) (by fun_prop) hne2))
    (by fun_prop)) (by fun_prop) hsin.ne'

theorem continuousAt_ftAngleDeriv2TauAngle_comp (hu : ContinuousAt u θ)
    (hy : ContinuousAt (fun t => ftAngle a (u t) t) θ) (hupos : 0 < u θ)
    (hθ : θ ∈ Ioo 0 π) :
    ContinuousAt (fun t => ftAngleDeriv2TauAngle a (u t) t) θ := by
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hne : u θ ^ 2 ≠ 0 := by positivity
  have hne2 : Real.sin θ ^ 2 ≠ 0 := by positivity
  simp only [ftAngleDeriv2TauAngle]
  refine ContinuousAt.mul (ContinuousAt.neg (ContinuousAt.div (by fun_prop) (by fun_prop) hne))
    (ContinuousAt.div (ContinuousAt.sub (ContinuousAt.mul (ContinuousAt.mul (by fun_prop)
      (ContinuousAt.div (by fun_prop) (by fun_prop) hsin.ne')) (by fun_prop))
      (by fun_prop)) (by fun_prop) hne2)

theorem continuousAt_ftAngleDeriv2Angle_comp
    (hy : ContinuousAt (fun t => ftAngle a (u t) t) θ) (hθ : θ ∈ Ioo 0 π) :
    ContinuousAt (fun t => ftAngleDeriv2Angle a (u t) t) θ := by
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hne2 : Real.sin θ ^ 2 ≠ 0 := by positivity
  have hq : ContinuousAt (fun t => Real.sin (ftAngle a (u t) t)
      * Real.cos (ftAngle a (u t) t - t) / Real.sin t) θ :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hsin.ne'
  simp only [ftAngleDeriv2Angle]
  exact ContinuousAt.div (ContinuousAt.sub (ContinuousAt.mul (ContinuousAt.add
      (ContinuousAt.mul (ContinuousAt.mul (by fun_prop) hq) (by fun_prop))
      (ContinuousAt.mul (by fun_prop)
        (ContinuousAt.mul (by fun_prop) (ContinuousAt.sub hq continuousAt_const))))
      (by fun_prop)) (by fun_prop)) (by fun_prop) hne2

end Curvature


/-! ### `τ''` and `γ''` are continuous on the viewing arc

The four sums, `τ'` and the angle sum's own two partials are continuous by the
previous section and by `BranchCurvature`'s own `hasDerivAt` lemmas; the
quotient closes because `∂_τ(∑θ_k) < 0`.  This is what
`exists_phase_second_derivative_bound` needs and what the compactness bound on
`ψ''` runs on. -/

section BranchCurvatureContinuity

variable {n r l : ℕ} {a : Fin n → ℝ}

/-- The branch angle of the `k`-th zero, read along the branch, is continuous. -/
theorem continuousAt_ftAngle_ftTau (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (hb : ∀ s ∈ Ioo 0 (π / r), FTBranchAt a r l s)
    (k : Fin n) : ContinuousAt (fun t => ftAngle (a k) (ftTau a r l t) t) θ :=
  (hasDerivAt_ftAngle_comp (ha k) (hasDerivAt_ftTau hn ha hr hθ hb)
    (ftTau_pos (hb θ hθ)) (ftArc_subset hr hθ)).continuousAt

private theorem continuousAt_sum {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ} {θ : ℝ}
    (h : ∀ i, ContinuousAt (f i) θ) : ContinuousAt (fun t => ∑ i, f i t) θ := by
  simpa [ContinuousAt] using tendsto_finsetSum Finset.univ fun i _ => h i

/-- **`τ''` is continuous on the viewing arc.** -/
theorem continuousAt_ftTauDeriv2 (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (hb : ∀ s ∈ Ioo 0 (π / r), FTBranchAt a r l s) :
    ContinuousAt (ftTauDeriv2 a r l) θ := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hτ : 0 < ftTau a r l θ := ftTau_pos (hb θ hθ)
  have hT := hasDerivAt_ftTau hn ha hr hθ hb
  have hTc : ContinuousAt (ftTau a r l) θ := hT.continuousAt
  have hy := continuousAt_ftAngle_ftTau (l := l) hn ha hr hθ hb
  have hD := hasDerivAt_ftTauDeriv hn ha hr hθ hb
  have hDc : ContinuousAt (ftTauDeriv a r l) θ := hD.continuousAt
  have hHc : ContinuousAt (fun t => ftAngleSumDerivTau a (ftTau a r l t) t) θ :=
    (hasDerivAt_ftAngleSumDerivTau_comp ha hT hτ hθπ).continuousAt
  have hGc : ContinuousAt (fun t => ftAngleSumDerivAngle a (ftTau a r l t) t) θ :=
    (hasDerivAt_ftAngleSumDerivAngle_comp ha hT hτ hθπ).continuousAt
  have hHne : ftAngleSumDerivTau a (ftTau a r l θ) θ ≠ 0 :=
    (ftAngleSumDerivTau_neg hn ha hτ hθπ).ne
  have h1 : ContinuousAt
      (fun t => ∑ k, ftAngleDeriv2AngleTau (a k) (ftTau a r l t) t) θ :=
    continuousAt_sum fun k =>
      continuousAt_ftAngleDeriv2AngleTau_comp hTc (hy k) hτ hθπ
  have h2 : ContinuousAt (fun t => ∑ k, ftAngleDeriv2Angle (a k) (ftTau a r l t) t) θ :=
    continuousAt_sum fun k => continuousAt_ftAngleDeriv2Angle_comp (hy k) hθπ
  have h3 : ContinuousAt (fun t => ∑ k, ftAngleDeriv2Tau (a k) (ftTau a r l t) t) θ :=
    continuousAt_sum fun k => continuousAt_ftAngleDeriv2Tau_comp hTc (hy k) hτ hθπ
  have h4 : ContinuousAt
      (fun t => ∑ k, ftAngleDeriv2TauAngle (a k) (ftTau a r l t) t) θ :=
    continuousAt_sum fun k =>
      continuousAt_ftAngleDeriv2TauAngle_comp hTc (hy k) hτ hθπ
  change ContinuousAt (fun t => ftTauDeriv2 a r l t) θ
  simp only [ftTauDeriv2]
  exact ContinuousAt.div
    (((((h1.mul hDc).add h2).neg).mul hHc).sub
      (((hGc.sub continuousAt_const).neg).mul ((h3.mul hDc).add h4)))
    (hHc.pow 2) (pow_ne_zero 2 hHne)

/-- **`γ''` is continuous on the viewing arc.**  `γ'' = e^{iθ}(τ'' + 2iτ' - τ)`,
so this is `continuousAt_ftTauDeriv2` with the two lower-order terms carried
along. -/
theorem continuousAt_ftGammaDeriv2 (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (hb : ∀ s ∈ Ioo 0 (π / r), FTBranchAt a r l s) :
    ContinuousAt (ftGammaDeriv2 a r l) θ := by
  have hTc : ContinuousAt (fun t : ℝ => ((ftTau a r l t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp
      (hasDerivAt_ftTau hn ha hr hθ hb).continuousAt
  have hDc : ContinuousAt (fun t : ℝ => ((ftTauDeriv a r l t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp
      (hasDerivAt_ftTauDeriv hn ha hr hθ hb).continuousAt
  have hD2c : ContinuousAt (fun t : ℝ => ((ftTauDeriv2 a r l t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_ftTauDeriv2 hn ha hr hθ hb)
  have hE : ContinuousAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) θ := by fun_prop
  change ContinuousAt (fun t => ftGammaDeriv2 a r l t) θ
  simp only [ftGammaDeriv2]
  exact hE.mul ((hD2c.add ((continuousAt_const.mul hDc).mul continuousAt_const)).sub hTc)

/-- **`γ'` is continuous on the viewing arc.** -/
theorem continuousAt_ftGammaDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (hb : ∀ s ∈ Ioo 0 (π / r), FTBranchAt a r l s) :
    ContinuousAt (ftGammaDeriv a r l) θ :=
  (hasDerivAt_ftGammaDeriv hn ha hr hθ hb).continuousAt

end BranchCurvatureContinuity


/-! ### The principal amplitude along the general branch

`ftAmp_eq_ratio` and `BranchCurvature` meet here: `W` is the fixed rational
function `N/E` read along `γ`, so its two derivatives are the composition rule
and nothing else.  Every hypothesis below is either the admissible class or the
subarc's disjointness from the amplitude divisor. -/

section Branch

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}

/-- `W` along the branch of `Forgacs2017RationalDenominator` Eq. (21). -/
noncomputable def ftBranchAmp (Q B : Polynomial ℂ) {n : ℕ} (a : Fin n → ℝ)
    (r l : ℕ) : ℝ → ℂ :=
  ftRatComp (ftAmpNum B) (ftCritical Q r) (ftPrincipal (ftTau a r l))

/-- `W'` along that branch. -/
noncomputable def ftBranchAmpDeriv (Q B : Polynomial ℂ) {n : ℕ} (a : Fin n → ℝ)
    (r l : ℕ) : ℝ → ℂ :=
  ftRatCompDeriv (ftAmpNum B) (ftCritical Q r) (ftPrincipal (ftTau a r l))
    (ftGammaDeriv a r l)

/-- `W''` along that branch. -/
noncomputable def ftBranchAmpDeriv2 (Q B : Polynomial ℂ) {n : ℕ} (a : Fin n → ℝ)
    (r l : ℕ) : ℝ → ℂ :=
  ftRatCompDeriv2 (ftAmpNum B) (ftCritical Q r) (ftPrincipal (ftTau a r l))
    (ftGammaDeriv a r l) (ftGammaDeriv2 a r l)

theorem ftPrincipal_ne_zero {τ : ℝ → ℝ} {θ : ℝ} (hτ : τ θ ≠ 0) :
    ftPrincipal τ θ ≠ 0 :=
  mul_ne_zero (by simpa using hτ) (Complex.exp_ne_zero _)

/-- **The pole side of the amplitude is empty on the viewing arc.**
`E(γ(θ)) = 0` would make the principal root a *multiple* zero of the pencil, and
`eq:principal-simple` says it is simple at every angle of the arc. -/
theorem eval_ftCritical_ftPrincipal_ne_zero (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    (ftCritical (ftRootPoly c a) r).eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0 := by
  obtain ⟨hroot, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  have hγ : ftPrincipal (ftTau a r (n - 1)) θ ≠ 0 := ftPrincipal_ne_zero (hpos θ hθ).ne'
  have hsimple := (ft_principal_simple_at_branch hn ha hc hr hnr hθ).1
  rw [eval_derivative_ftDen_eq_ftCritical_div hr hγ (hroot θ hθ)] at hsimple
  exact fun h => hsimple (by rw [h, zero_div])

/-- **`W` is differentiable along the branch**, with no hypothesis beyond the
admissible class. -/
theorem hasDerivAt_ftBranchAmp (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftBranchAmp (ftRootPoly c a) B a r (n - 1))
      (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ) θ :=
  hasDerivAt_ftRatComp
    (hasDerivAt_ftBranchGamma hn ha hr hθ
      fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs)
    (eval_ftCritical_ftPrincipal_ne_zero hn ha hc hr hnr hθ)

/-- **`W` is twice differentiable along the branch**, likewise. -/
theorem hasDerivAt_ftBranchAmpDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1))
      (ftBranchAmpDeriv2 (ftRootPoly c a) B a r (n - 1) θ) θ :=
  hasDerivAt_ftRatCompDeriv
    (hasDerivAt_ftBranchGamma hn ha hr hθ
      fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs)
    (hasDerivAt_ftGammaDeriv hn ha hr hθ
      fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs)
    (eval_ftCritical_ftPrincipal_ne_zero hn ha hc hr hnr hθ)

/-- **`W''` is continuous along the branch.**  This is where
`continuousAt_ftGammaDeriv2` is spent: without it the second derivative would
exist and carry no bound. -/
theorem continuousAt_ftBranchAmpDeriv2 (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ContinuousAt (ftBranchAmpDeriv2 (ftRootPoly c a) B a r (n - 1)) θ :=
  continuousAt_ftRatCompDeriv2
    (hasDerivAt_ftBranchGamma hn ha hr hθ
      (fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs)).continuousAt
    (continuousAt_ftGammaDeriv hn ha hr hθ
      fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs)
    (continuousAt_ftGammaDeriv2 hn ha hr hθ
      fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs)
    (eval_ftCritical_ftPrincipal_ne_zero hn ha hc hr hnr hθ)

/-- **The function differentiated above is the paper's `𝒲`.**  Without this the
`C²` layer would be about a rational function that merely resembles the
amplitude. -/
theorem ftBranchAmp_eq_ftAmp (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ
      = ftAmp (ftRootPoly c a) B r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)
          (ftPrincipal (ftTau a r (n - 1)) θ) := by
  obtain ⟨hroot, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  rw [ftAmp_eq_ratio hr (ftPrincipal_ne_zero (hpos θ hθ).ne') (hroot θ hθ)]
  rfl

/-- **`W` vanishes exactly where `B` does along the branch.**  The `≠ 0` side is
what `eq:phase-derivative-bound` and the Taylor producer consume, and it is the
one hypothesis a subarc has to be *chosen* to meet. -/
theorem ftBranchAmp_ne_zero (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hB : B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ ≠ 0 := by
  obtain ⟨-, hpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  refine div_ne_zero ?_ (eval_ftCritical_ftPrincipal_ne_zero hn ha hc hr hnr hθ)
  rw [eval_ftAmpNum]
  exact neg_ne_zero.2 (mul_ne_zero (ftPrincipal_ne_zero (hpos θ hθ).ne') hB)

end Branch


/-! ### `κ`, `κ_2` and the differentiable phase, on a compact subarc

The three constants `prop:local-strong-clock` takes from the branch side, at the
general admissible pencil.  The subarc is asked for one thing only: that `B` not
vanish along the branch on it, which is disjointness from
`InteriorSupply.ftAmplitudeDivisor`.  Everything else — the two derivatives, the
continuity of the second, the nonvanishing of `E` — is a theorem of the class. -/

section Subarc

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ} {lo hi : ℝ}

/-- The continuous branch of `arg W` along the branch, based at `lo`. -/
noncomputable def ftBranchPhase (Q B : Polynomial ℂ) {n : ℕ} (a : Fin n → ℝ)
    (r l : ℕ) (lo : ℝ) : ℝ → ℝ :=
  polarAngle (ftBranchAmp Q B a r l) (ftBranchAmpDeriv Q B a r l) 0 lo

/-- `W` is continuous on the arc. -/
theorem continuousOn_ftBranchAmp (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {s : Set ℝ} (hs : s ⊆ Ioo 0 (π / r)) :
    ContinuousOn (ftBranchAmp (ftRootPoly c a) B a r (n - 1)) s := fun _θ hθ =>
  (hasDerivAt_ftBranchAmp hn ha hc hr hnr (hs hθ)).continuousAt.continuousWithinAt

/-- `W'` is continuous on the arc. -/
theorem continuousOn_ftBranchAmpDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {s : Set ℝ} (hs : s ⊆ Ioo 0 (π / r)) :
    ContinuousOn (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1)) s := fun _θ hθ =>
  (hasDerivAt_ftBranchAmpDeriv hn ha hc hr hnr (hs hθ)).continuousAt.continuousWithinAt

/-- **`ψ' = Im(W'/W)` at the general branch.**  The phase is constructed, not
hypothesized: `polarAngle` lifts `arg W` along the arc, and
`ViewingAngle.hasDerivAt_polarAngle` differentiates it. -/
theorem hasDerivAt_ftBranchPhase (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hB : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc lo hi) :
    HasDerivAt (ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo)
      ((ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
        / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ).im) θ := by
  have h := hasDerivAt_polarAngle (γ := ftBranchAmp (ftRootPoly c a) B a r (n - 1))
    (dγ := ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1)) (β := 0)
    (U := Ioo 0 (π / r)) isOpen_Ioo harc
    (fun s hs => hasDerivAt_ftBranchAmp hn ha hc hr hnr hs)
    (continuousOn_ftBranchAmpDeriv hn ha hc hr hnr (subset_refl _))
    (fun s hs => ftBranchAmp_ne_zero hn ha hc hr hnr (harc hs) (hB s hs)) hθ
  rwa [sub_zero] at h

/-- **`W = ‖W‖e^{iψ}` at the general branch**, with `ψ` the constructed
differentiable phase.  This is what lets the same `ψ` serve
`interior_cos_decomposition_on_subarc`, whose own `exists_polar_phase` returns
the non-differentiable `arg`. -/
theorem ftBranchAmp_eq_polar (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hlohi : lo ≤ hi)
    (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hB : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc lo hi) :
    ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ
      = ((‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖ : ℝ) : ℂ)
        * Complex.exp ((ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo θ : ℂ)
            * Complex.I) := by
  have hd := polar_decomposition (γ := ftBranchAmp (ftRootPoly c a) B a r (n - 1))
    (dγ := ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1)) (β := 0)
    (U := Ioo 0 (π / r)) hlohi isOpen_Ioo harc
    (fun s hs => hasDerivAt_ftBranchAmp hn ha hc hr hnr hs)
    (continuousOn_ftBranchAmpDeriv hn ha hc hr hnr (subset_refl _))
    (fun s hs => ftBranchAmp_ne_zero hn ha hc hr hnr (harc hs) (hB s hs)) hθ
  rw [sub_zero] at hd
  have hnorm : ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖
      = polarModulus (ftBranchAmp (ftRootPoly c a) B a r (n - 1))
          (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1)) 0 lo θ := by
    rw [hd, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (polarModulus_pos _ _ _ _ _)]
  rw [hnorm]
  exact hd

/-- **`eq:principal-decomposition`'s polar form at the general branch**, in the
spelling `PhaseQuantization.interior_cos_error_geometric` consumes: the paper's
`𝒲` written as `|W|e^{iψ}` with the *differentiable* `ψ`, rather than with the
`arg` that `exists_polar_phase` returns. -/
theorem ftAmp_eq_polar_at_branch (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hlohi : lo ≤ hi)
    (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hB : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc lo hi) :
    ftAmp (ftRootPoly c a) B r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)
        (ftPrincipal (ftTau a r (n - 1)) θ)
      = ((ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
            (ftTau a r (n - 1)) θ : ℝ) : ℂ)
        * Complex.exp ((ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo θ : ℂ)
            * Complex.I) := by
  have hpolar := ftBranchAmp_eq_polar (B := B) hn ha hc hr hnr hlohi harc hB hθ
  have hval := ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (harc hθ)
  rw [hval] at hpolar
  rw [hpolar]
  rfl

/-- **The `C²` combination `Im(W''/W - (W'/W)^2)` is continuous on the subarc.**
This is `ψ''`, and it is the input `ClockSpacing.exists_phase_taylor_bound`
consumes; the compactness bound below is the only thing done with it. -/
theorem continuousOn_ftBranchPhaseCurvature (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hB : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ContinuousOn (fun θ =>
      (ftBranchAmpDeriv2 (ftRootPoly c a) B a r (n - 1) θ
          / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ
        - (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
          / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ) ^ 2).im) (Icc lo hi) := by
  have hne : ∀ θ ∈ Icc lo hi, ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ ≠ 0 :=
    fun θ hθ => ftBranchAmp_ne_zero hn ha hc hr hnr (harc hθ) (hB θ hθ)
  have hcont2 : ContinuousOn (ftBranchAmpDeriv2 (ftRootPoly c a) B a r (n - 1))
      (Icc lo hi) := fun θ hθ =>
    (continuousAt_ftBranchAmpDeriv2 hn ha hc hr hnr (harc hθ)).continuousWithinAt
  exact Complex.continuous_im.comp_continuousOn
    ((hcont2.div (continuousOn_ftBranchAmp hn ha hc hr hnr harc) hne).sub
      (((continuousOn_ftBranchAmpDeriv hn ha hc hr hnr harc).div
        (continuousOn_ftBranchAmp hn ha hc hr hnr harc) hne).pow 2))

/-- **`eq:phase-derivative-bound` at the general admissible pencil.**  The
constant `κ` of `prop:local-strong-clock`, produced by compactness on a subarc
that misses the amplitude divisor.  `CubicClockSpacing` reaches the same bound at
one pencil with the explicit value `3/2`; here there is no closed form to read a
number off, so the constant is the one compactness supplies. -/
theorem exists_ftBranch_phase_deriv_bound (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hB : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ∃ κ ≥ (0 : ℝ), ∀ θ ∈ Icc lo hi,
      |(ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
        / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ).im| ≤ κ := by
  have hne : ∀ θ ∈ Icc lo hi, ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ ≠ 0 :=
    fun θ hθ => ftBranchAmp_ne_zero hn ha hc hr hnr (harc hθ) (hB θ hθ)
  have hcont : ContinuousOn (fun θ => (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
      / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ).im) (Icc lo hi) :=
    Complex.continuous_im.comp_continuousOn
      ((continuousOn_ftBranchAmpDeriv hn ha hc hr hnr harc).div
        (continuousOn_ftBranchAmp hn ha hc hr hnr harc) hne)
  obtain ⟨κ, hκ⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max κ 0, le_max_right _ _, fun θ hθ =>
    le_trans (by simpa [Real.norm_eq_abs] using hκ θ hθ) (le_max_left _ _)⟩

/-- **`eq:local-strong-clock`'s `κ_2` at the general admissible pencil.**  The
`ψ''` bound, produced by compactness from `continuousAt_ftBranchAmpDeriv2` — the
step `CubicClockSpacing` could take only because `τ` was in closed form there.

`scripts/check_cubic_strong_clock.py` measures `max|ψ''| = 0.0512` against
`max|ψ'| = 0.7754` at the witness pencil, so this constant is not zero and a
route that drops the `ψ''` term proves a different statement. -/
theorem exists_ftBranch_phase_curvature_bound (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hB : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ∃ κ₂ ≥ (0 : ℝ), ∀ θ ∈ Icc lo hi,
      |(ftBranchAmpDeriv2 (ftRootPoly c a) B a r (n - 1) θ
            / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ
          - (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ
            / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ) ^ 2).im| ≤ κ₂ := by
  have hcont := continuousOn_ftBranchPhaseCurvature hn ha hc hr hnr harc hB
  obtain ⟨κ₂, hκ⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max κ₂ 0, le_max_right _ _, fun θ hθ =>
    le_trans (by simpa [Real.norm_eq_abs] using hκ θ hθ) (le_max_left _ _)⟩

/-- **`eq:local-strong-clock`'s `κ_2` in the shape the clock consumes**, at the
general admissible pencil: one Taylor constant for the whole subarc, produced
before any pair of zeros is chosen.

`exists_ftBranch_phase_curvature_bound` is the `ψ''` bound; this is what
`ClockSpacing.exists_phase_taylor_bound` makes of it, and it is the form
`ft_local_strong_clock_on_FM_of` takes as a parameter.  The scope is the point:
a `κ_2` chosen after the zeros can absorb any error
(`ClockSpacing.exists_absorbing_constant`). -/
theorem exists_ftBranch_taylor_bound (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hB : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    ∃ κ₂ ≥ (0 : ℝ), ∀ θa ∈ Icc lo hi, ∀ θb ∈ Icc lo hi, θa ≤ θb →
      |ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo θb
          - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo θa
          - (ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θa
              / ftBranchAmp (ftRootPoly c a) B a r (n - 1) θa).im * (θb - θa)|
        ≤ κ₂ * (θb - θa) ^ 2 :=
  exists_phase_taylor_bound
    (fun _θ hθ => hasDerivAt_ftBranchPhase hn ha hc hr hnr harc hB hθ)
    (fun _θ hθ => hasDerivAt_ftBranchAmp hn ha hc hr hnr (harc hθ))
    (fun _θ hθ => hasDerivAt_ftBranchAmpDeriv hn ha hc hr hnr (harc hθ))
    (fun θ hθ => ftBranchAmp_ne_zero hn ha hc hr hnr (harc hθ) (hB θ hθ))
    (continuousOn_ftBranchPhaseCurvature hn ha hc hr hnr harc hB)

end Subarc

/-! ### The amplitude's modulus

`eq:C1-interior-remainder` differentiates a quotient whose denominator is
`2‖W‖`, so the modulus has to be differentiable and its derivative bounded.
Both are general facts about a nonvanishing `C^1` curve in `ℂ`, so they are
stated that way and instantiated at the branch below —
`CubicInteriorRemainder.hasDerivAt_cubicAmpNorm` is the same statement written
at one pencil. -/

section Modulus

/-- **`d‖W‖/dθ = Re(W' \overline{W})/‖W‖`.**  Through `‖·‖ = √(re² + im²)`, which
is where `W θ ≠ 0` is spent. -/
theorem hasDerivAt_norm_comp {W : ℝ → ℂ} {W' : ℂ} {θ : ℝ}
    (hW : HasDerivAt W W' θ) (h0 : W θ ≠ 0) :
    HasDerivAt (fun s => ‖W s‖) ((W' * (starRingEnd ℂ) (W θ)).re / ‖W θ‖) θ := by
  have hre : HasDerivAt (fun s => (W s).re) W'.re θ :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ hW
  have him : HasDerivAt (fun s => (W s).im) W'.im θ :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hW
  have hns : HasDerivAt (fun s => (W s).re * (W s).re + (W s).im * (W s).im)
      (W'.re * (W θ).re + (W θ).re * W'.re + (W'.im * (W θ).im + (W θ).im * W'.im)) θ :=
    (hre.mul hre).add (him.mul him)
  have hpos : 0 < (W θ).re * (W θ).re + (W θ).im * (W θ).im := by
    have h := Complex.normSq_pos.2 h0
    rwa [Complex.normSq_apply] at h
  refine ((hns.sqrt hpos.ne').congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by
      simp only [Complex.norm_def, Complex.normSq_apply])
  have hs : 0 < Real.sqrt ((W θ).re * (W θ).re + (W θ).im * (W θ).im) :=
    Real.sqrt_pos.2 hpos
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- **`|d‖W‖/dθ| ≤ ‖W'‖`**, which is what the quotient rule needs and all it
needs — the modulus can move no faster than the curve. -/
theorem abs_norm_deriv_le {W' w : ℂ} (h0 : w ≠ 0) :
    |(W' * (starRingEnd ℂ) w).re / ‖w‖| ≤ ‖W'‖ := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 h0
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [norm_mul, RCLike.norm_conj]

end Modulus

section BranchModulus

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ} {lo hi : ℝ}

/-- `d‖W‖/dθ` along the branch. -/
noncomputable def ftBranchAmpNormDeriv (Q B : Polynomial ℂ) {n : ℕ} (a : Fin n → ℝ)
    (r l : ℕ) (θ : ℝ) : ℝ :=
  (ftBranchAmpDeriv Q B a r l θ
      * (starRingEnd ℂ) (ftBranchAmp Q B a r l θ)).re / ‖ftBranchAmp Q B a r l θ‖

theorem hasDerivAt_ftBranchAmpNorm (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hB : B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    HasDerivAt (fun s => ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) s‖)
      (ftBranchAmpNormDeriv (ftRootPoly c a) B a r (n - 1) θ) θ :=
  hasDerivAt_norm_comp (hasDerivAt_ftBranchAmp hn ha hc hr hnr hθ)
    (ftBranchAmp_ne_zero hn ha hc hr hnr hθ hB)

theorem abs_ftBranchAmpNormDeriv_le (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hB : B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0) :
    |ftBranchAmpNormDeriv (ftRootPoly c a) B a r (n - 1) θ|
      ≤ ‖ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ‖ :=
  abs_norm_deriv_le (ftBranchAmp_ne_zero hn ha hc hr hnr hθ hB)

/-- **`‖W'‖` is bounded on a compact subarc off the divisor**, which is the
`W_d` of the `C¹` quotient rule. -/
theorem exists_ftBranchAmpDeriv_norm_bound (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (harc : Icc lo hi ⊆ Ioo 0 (π / r)) :
    ∃ Wd ≥ (0 : ℝ), ∀ θ ∈ Icc lo hi,
      ‖ftBranchAmpDeriv (ftRootPoly c a) B a r (n - 1) θ‖ ≤ Wd := by
  obtain ⟨Wd, hWd⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_ftBranchAmpDeriv (B := B) hn ha hc hr hnr harc).norm)
  exact ⟨max Wd 0, le_max_right _ _, fun θ hθ =>
    le_trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hWd θ hθ)
      (le_max_left _ _)⟩

end BranchModulus

end ForgacsTran
