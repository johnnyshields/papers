/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Shields.Analysis.Complex.Hurwitz
import Shields.Analysis.Complex.RealRootedPolynomial

/-!
# The Laguerre--Pólya class

Entire functions that are locally uniform limits of real-rooted polynomials.

## Main results

* `Shields.IsLaguerrePolyaLimit`: the class, in its limit-of-real-rooted-polynomials
  characterization.
* `Shields.IsLaguerrePolyaLimit.of_tendstoLocallyUniformly`: closure under locally uniform limits.
* `Shields.IsLaguerrePolyaLimit.im_eq_zero_of_eq_zero`: every zero of a member that does not vanish
  identically is real.
* `Shields.exists_radius_eventually_card_rootsIn_eq_one`: near a simple real zero of the limit, a
  disc carrying exactly one zero of each large-`n` approximant, with multiplicity.
* `Shields.isLaguerrePolyaLimit_exp`, `Shields.exists_isLaguerrePolyaLimit_not_polynomial`: the
  class strictly contains the real-rooted polynomials that generate it.
* `Shields.exists_tendstoLocallyUniformly_exp`: the Euler approximants of `exp` with their roots
  located, not merely real --- `(1 + z/n)^n` vanishes only at `-n`.  `IsRealRooted` drops that,
  and a consumer localizing zeros to a ray needs it.

## Implementation notes

The class is *defined* as a limit rather than by a Hadamard product, because that is the form every
consumer here uses and it makes closure under locally uniform limits immediate.

Mathlib defines no Laguerre--Pólya class at the pinned revision: `laguerre`, `realRooted` and
`real-rooted` have no occurrence anywhere in the library, and every `Hurwitz` occurrence is Hurwitz
zeta. `HasRealCoeffs` is likewise local.

## References

* [G. Pólya and J. Schur, *Über zwei Arten von Faktorenfolgen in der Theorie der algebraischen
  Gleichungen*][PolyaSchur1914]

## Tags

Laguerre-Polya, real-rooted, entire function, Hurwitz theorem, locally uniform convergence
-/

namespace Shields

open Complex Filter Metric Polynomial Set Topology

/-! ### Real coefficients -/

/-- A complex polynomial with real coefficients.  Mathlib has no predicate for this at revision
`8e45b05`; the condition is the hypothesis shape that `eval_conj_of_coeff_im_eq_zero` consumes. -/
def HasRealCoeffs (p : Polynomial ℂ) : Prop := ∀ i, (p.coeff i).im = 0

/-- A real-coefficient polynomial takes real values at real points. -/
theorem HasRealCoeffs.im_eval_ofReal {p : Polynomial ℂ} (hp : HasRealCoeffs p) (x : ℝ) :
    (p.eval (x : ℂ)).im = 0 := by
  have h := eval_conj_of_coeff_im_eq_zero hp (x : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- The derivative of a real-coefficient polynomial has real coefficients. -/
theorem HasRealCoeffs.derivative {p : Polynomial ℂ} (hp : HasRealCoeffs p) :
    HasRealCoeffs (Polynomial.derivative p) := by
  intro i
  rw [coeff_derivative]
  simp [Complex.mul_im, hp (i + 1)]

/-! ### The class -/

/-- **The Laguerre--Pólya class**, in its limit-of-real-rooted-polynomials characterization: `f` is
a locally uniform limit on `ℂ` of polynomials with real coefficients all of whose roots are real.

This is **not** the Hadamard-product definition.  The equivalence with the genus-`≤ 1` product form
`e^{-a z² + b z + c} z^m ∏ (1 + z/x_k) e^{-z/x_k}` is **not proved here**: it needs Hadamard
factorization, which Mathlib does not have at revision `8e45b05`. -/
def IsLaguerrePolyaLimit (f : ℂ → ℂ) : Prop :=
  ∃ p : ℕ → Polynomial ℂ, (∀ n, IsRealRooted (p n)) ∧ (∀ n, HasRealCoeffs (p n)) ∧
    TendstoLocallyUniformly (fun n z => (p n).eval z) f atTop

/-- A member of the class is entire: it is a locally uniform limit of polynomials. -/
theorem IsLaguerrePolyaLimit.differentiable {f : ℂ → ℂ} (hf : IsLaguerrePolyaLimit f) :
    Differentiable ℂ f := by
  obtain ⟨p, -, -, hconv⟩ := hf
  rw [← differentiableOn_univ]
  exact (tendstoLocallyUniformlyOn_univ.mpr hconv).differentiableOn
    (.of_forall fun n => (p n).differentiable.differentiableOn) isOpen_univ

/-- A member of the class is analytic on all of `ℂ`. -/
theorem IsLaguerrePolyaLimit.analyticOnNhd {f : ℂ → ℂ} (hf : IsLaguerrePolyaLimit f) :
    AnalyticOnNhd ℂ f univ :=
  hf.differentiable.differentiableOn.analyticOnNhd isOpen_univ

/-- A locally uniform limit of real-coefficient polynomials is real on the real axis. -/
theorem im_apply_ofReal_of_tendsto {p : ℕ → Polynomial ℂ} {f : ℂ → ℂ}
    (hcoeff : ∀ n, HasRealCoeffs (p n))
    (hconv : TendstoLocallyUniformly (fun n z => (p n).eval z) f atTop) (x : ℝ) :
    (f (x : ℂ)).im = 0 := by
  have hpt : Tendsto (fun n => ((p n).eval (x : ℂ)).im) atTop (𝓝 (f (x : ℂ)).im) :=
    (Complex.continuous_im.tendsto _).comp
      ((tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at (mem_univ _))
  have hconst : (fun n => ((p n).eval (x : ℂ)).im) = fun _ => (0 : ℝ) :=
    funext fun n => (hcoeff n).im_eval_ofReal x
  rw [hconst] at hpt
  exact tendsto_nhds_unique hpt tendsto_const_nhds

/-- A member of the class is real on the real axis. -/
theorem IsLaguerrePolyaLimit.im_apply_ofReal {f : ℂ → ℂ} (hf : IsLaguerrePolyaLimit f) (x : ℝ) :
    (f (x : ℂ)).im = 0 := by
  obtain ⟨p, -, hcoeff, hconv⟩ := hf
  exact im_apply_ofReal_of_tendsto hcoeff hconv x

/-! ### Closure under locally uniform limits -/

/-- **The diagonal choice.**  A locally uniform limit of locally uniform limits of polynomials
satisfying `P` is again a locally uniform limit of polynomials satisfying `P`.

Nothing about `P` is used: the content is that one polynomial can be chosen per radius, close to the
limit on the closed ball of that radius, by going through an intermediate approximant.  Stated for a
bare predicate so that the real-rooted class and the nonpositive-rooted class share the argument. -/
theorem exists_poly_tendstoLocallyUniformly_of_tendstoLocallyUniformly
    {P : Polynomial ℂ → Prop} {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ n, ∃ p : ℕ → Polynomial ℂ, (∀ m, P (p m)) ∧
      TendstoLocallyUniformly (fun m z => (p m).eval z) (f n) atTop)
    (hF : TendstoLocallyUniformly f F atTop) :
    ∃ p : ℕ → Polynomial ℂ, (∀ m, P (p m)) ∧
      TendstoLocallyUniformly (fun m z => (p m).eval z) F atTop := by
  choose p hP hconv using hf
  have key : ∀ k : ℕ, ∃ q : Polynomial ℂ, P q ∧
      ∀ z ∈ closedBall (0 : ℂ) k, dist (F z) (q.eval z) < 1 / (k + 1) := by
    intro k
    have hεpos : (0 : ℝ) < 1 / (2 * (k + 1)) := by positivity
    have h1 : TendstoUniformlyOn f F atTop (closedBall (0 : ℂ) k) :=
      tendstoLocallyUniformly_iff_forall_isCompact.mp hF _ (isCompact_closedBall _ _)
    obtain ⟨j, hj⟩ := (Metric.tendstoUniformlyOn_iff.mp h1 _ hεpos).exists
    have h2 : TendstoUniformlyOn (fun m z => (p j m).eval z) (f j) atTop
        (closedBall (0 : ℂ) k) :=
      tendstoLocallyUniformly_iff_forall_isCompact.mp (hconv j) _ (isCompact_closedBall _ _)
    obtain ⟨m, hm⟩ := (Metric.tendstoUniformlyOn_iff.mp h2 _ hεpos).exists
    refine ⟨p j m, hP j m, fun z hz => ?_⟩
    calc dist (F z) ((p j m).eval z)
        ≤ dist (F z) (f j z) + dist (f j z) ((p j m).eval z) := dist_triangle _ _ _
      _ < 1 / (2 * (k + 1)) + 1 / (2 * (k + 1)) := add_lt_add (hj z hz) (hm z hz)
      _ = 1 / (k + 1) := by field
  choose q hqP hqapprox using key
  refine ⟨q, hqP, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max R (1 / ε))
  filter_upwards [eventually_ge_atTop k₀] with n hn z hz
  have hRn : R ≤ (n : ℝ) :=
    le_trans (le_max_left _ _) (le_trans hk₀.le (by exact_mod_cast hn))
  have hzn : z ∈ closedBall (0 : ℂ) (n : ℝ) := closedBall_subset_closedBall hRn (hR hz)
  have hεn : 1 / ((n : ℝ) + 1) < ε := by
    have h1 : 1 / ε ≤ (n : ℝ) :=
      le_trans (le_max_right _ _) (le_trans hk₀.le (by exact_mod_cast hn))
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ h2]
    have : 1 / ε * ε ≤ (n : ℝ) * ε := by nlinarith
    rw [one_div, inv_mul_cancel₀ hε.ne'] at this
    nlinarith
  exact lt_trans (hqapprox n z hzn) hεn

/-- **The class is closed under locally uniform limits.**  If every `f n` is a locally uniform limit
of real-rooted real-coefficient polynomials and `f n → F` locally uniformly, then so is `F`. -/
theorem IsLaguerrePolyaLimit.of_tendstoLocallyUniformly {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ n, IsLaguerrePolyaLimit (f n)) (hF : TendstoLocallyUniformly f F atTop) :
    IsLaguerrePolyaLimit F := by
  have hf' : ∀ n, ∃ p : ℕ → Polynomial ℂ,
      (∀ m, IsRealRooted (p m) ∧ HasRealCoeffs (p m)) ∧
      TendstoLocallyUniformly (fun m z => (p m).eval z) (f n) atTop := by
    intro n
    obtain ⟨p, hreal, hcoeff, hconv⟩ := hf n
    exact ⟨p, fun m => ⟨hreal m, hcoeff m⟩, hconv⟩
  obtain ⟨q, hq, hconv⟩ :=
    exists_poly_tendstoLocallyUniformly_of_tendstoLocallyUniformly
      (P := fun q => IsRealRooted q ∧ HasRealCoeffs q) hf' hF
  exact ⟨q, fun m => (hq m).1, fun m => (hq m).2, hconv⟩

/-! ### Vertical monotonicity of the modulus

A polynomial with only real roots grows in modulus as the point moves away from the real axis along
a vertical line: each factor `|z - r|² = (Re z - r)² + (Im z)²` does.  This is the one inequality
the reality of the limit's zeros is read off from, and it survives the limit. -/

private theorem norm_sub_le_of_im_eq_zero {a : ℂ} (ha : a.im = 0) {x y y' : ℝ} (h : |y'| ≤ |y|) :
    ‖(x : ℂ) + y' * I - a‖ ≤ ‖(x : ℂ) + y * I - a‖ := by
  have hy : y' ^ 2 ≤ y ^ 2 := sq_le_sq.mpr h
  have hsq : ‖(x : ℂ) + y' * I - a‖ ^ 2 ≤ ‖(x : ℂ) + y * I - a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, ha]
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

private theorem prod_norm_le_of_im_eq_zero {x y y' : ℝ} (h : |y'| ≤ |y|) (M : Multiset ℂ) :
    (∀ a ∈ M, a.im = 0) →
      ‖(M.map fun a => (x : ℂ) + y' * I - a).prod‖ ≤
        ‖(M.map fun a => (x : ℂ) + y * I - a).prod‖ := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
      intro hM
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_mul (norm_sub_le_of_im_eq_zero (hM a (Multiset.mem_cons_self a M)) h)
        (ih fun b hb => hM b (Multiset.mem_cons_of_mem hb)) (norm_nonneg _) (norm_nonneg _)

/-- **A real-rooted polynomial grows away from the real axis.**  Along a vertical line the modulus
is monotone in the distance to the real axis. -/
theorem norm_eval_le_of_isRealRooted {p : Polynomial ℂ} (hp : IsRealRooted p) {x y y' : ℝ}
    (h : |y'| ≤ |y|) : ‖p.eval ((x : ℂ) + y' * I)‖ ≤ ‖p.eval ((x : ℂ) + y * I)‖ := by
  obtain ⟨hcard, him⟩ := hp
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  conv_rhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub,
    eval_X, norm_mul]
  exact mul_le_mul_of_nonneg_left (prod_norm_le_of_im_eq_zero h _ him) (norm_nonneg _)

/-- The vertical monotonicity passes to the limit: it holds for every member of the class. -/
theorem IsLaguerrePolyaLimit.norm_le {f : ℂ → ℂ} (hf : IsLaguerrePolyaLimit f) {x y y' : ℝ}
    (h : |y'| ≤ |y|) : ‖f ((x : ℂ) + y' * I)‖ ≤ ‖f ((x : ℂ) + y * I)‖ := by
  obtain ⟨p, hreal, -, hconv⟩ := hf
  have hpt : ∀ w : ℂ, Tendsto (fun n => ‖(p n).eval w‖) atTop (𝓝 ‖f w‖) := fun w =>
    ((tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at (mem_univ w)).norm
  exact le_of_tendsto_of_tendsto' (hpt _) (hpt _) fun n => norm_eval_le_of_isRealRooted (hreal n) h

/-! ### The zeros of a member are real -/

/-- **Every zero of a nonzero member of the class is real.**

The proof needs neither Rouché nor Hurwitz.  Vertical monotonicity forces `f` to vanish on the whole
vertical segment joining a putative nonreal zero to the real axis, so `f` vanishes frequently in
every punctured neighborhood of the real point below it, and the identity theorem makes `f`
identically zero. -/
theorem IsLaguerrePolyaLimit.im_eq_zero_of_eq_zero {f : ℂ → ℂ} (hf : IsLaguerrePolyaLimit f)
    (hne : ∃ w, f w ≠ 0) {z : ℂ} (hz : f z = 0) : z.im = 0 := by
  by_contra him
  have hseg : ∀ t : ℝ, |t| ≤ |z.im| → f ((z.re : ℂ) + t * I) = 0 := by
    intro t ht
    have hle := hf.norm_le (x := z.re) (y := z.im) (y' := t) ht
    rw [Complex.re_add_im z, hz] at hle
    simpa using hle
  have hfreq : ∃ᶠ w in 𝓝[≠] ((z.re : ℂ)), f w = 0 := by
    have hg : Tendsto (fun t : ℝ => (z.re : ℂ) + t * I) (𝓝[≠] (0 : ℝ)) (𝓝[≠] ((z.re : ℂ))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous fun t : ℝ => (z.re : ℂ) + t * I := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht hcon
        exact ht (by simpa using congrArg Complex.im hcon)
    refine hg.frequently (Filter.Eventually.frequently ?_)
    have h1 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| ≤ |z.im| := by
      have habs : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_abs.tendsto (0 : ℝ))
      exact (habs.eventually_lt_const (abs_pos.mpr him)).mono fun t ht => ht.le
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with t ht using hseg t ht
  have hEq : EqOn f 0 univ :=
    hf.analyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ _) hfreq
  obtain ⟨w, hw⟩ := hne
  exact hw (by simpa using hEq (mem_univ w))

/-! ### Convergence of the derivatives -/

/-- The derivatives of an approximating family converge locally uniformly to the derivative of the
limit. -/
theorem tendstoLocallyUniformly_derivative {p : ℕ → Polynomial ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly (fun n z => (p n).eval z) f atTop) :
    TendstoLocallyUniformly (fun n z => (Polynomial.derivative (p n)).eval z) (deriv f) atTop := by
  have h := (tendstoLocallyUniformlyOn_univ.mpr hconv).deriv
    (.of_forall fun n => (p n).differentiable.differentiableOn) isOpen_univ
  rw [tendstoLocallyUniformlyOn_univ] at h
  have heq : (deriv ∘ fun n z => (p n).eval z) =
      fun n z => (Polynomial.derivative (p n)).eval z :=
    funext fun n => funext fun z => by simp [Polynomial.deriv]
  rwa [heq] at h

/-! ### One finite zero near a simple real zero of the limit

The count is obtained without Rouché.  Two zeros of a finite real-rooted polynomial in a disc
about a real point are both real, so Rolle's theorem puts a critical point between them; the
derivative of the limit does not vanish at a simple zero, and the derivatives converge, so no
critical point is available.  A zero is produced by the real intermediate value theorem from the
sign change the nonvanishing derivative forces on the limit. -/

private theorem dist_ofReal_ofReal (s t : ℝ) : dist ((s : ℂ)) ((t : ℂ)) = |s - t| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

private theorem exists_derivative_eq_zero_of_eval_eq_zero {q : Polynomial ℂ}
    (hcoeff : HasRealCoeffs q) {a b : ℝ} (hab : a < b) (ha : q.eval (a : ℂ) = 0)
    (hb : q.eval (b : ℂ) = 0) : ∃ c ∈ Ioo a b, (Polynomial.derivative q).eval (c : ℂ) = 0 := by
  have hcont : ContinuousOn (fun t : ℝ => (q.eval (t : ℂ)).re) (Icc a b) :=
    (Complex.continuous_re.comp (q.continuous.comp Complex.continuous_ofReal)).continuousOn
  have hval : (q.eval (a : ℂ)).re = (q.eval (b : ℂ)).re := by rw [ha, hb]
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_zero hab hcont hval
  refine ⟨c, hc, ?_⟩
  have hd : HasDerivAt (fun t : ℝ => (q.eval (t : ℂ)).re)
      ((Polynomial.derivative q).eval (c : ℂ)).re c := (q.hasDerivAt (c : ℂ)).real_of_complex
  rw [hd.deriv] at hderiv
  exact Complex.ext (by simpa using hderiv) (by simpa using hcoeff.derivative.im_eval_ofReal c)

/-- **A real sign change gives a real zero.**  A polynomial with real coefficients whose values at
two real points have opposite sign vanishes at a real point between them: on the real axis the real
part is a real continuous function that changes sign, and the imaginary part vanishes identically.

This is the intermediate value theorem half of the count, the mirror of Rolle's theorem above. -/
private theorem exists_ofReal_root_of_re_mul_neg {q : Polynomial ℂ} (hcoeff : HasRealCoeffs q)
    {a b : ℝ} (hsign : (q.eval (a : ℂ)).re * (q.eval (b : ℂ)).re < 0) :
    ∃ t ∈ uIcc a b, q.eval (t : ℂ) = 0 := by
  have hcont : ContinuousOn (fun t : ℝ => (q.eval (t : ℂ)).re) (uIcc a b) :=
    (Complex.continuous_re.comp (q.continuous.comp Complex.continuous_ofReal)).continuousOn
  have hmem : (0 : ℝ) ∈ uIcc ((q.eval (a : ℂ)).re) ((q.eval (b : ℂ)).re) :=
    Set.mem_uIcc.mpr ((mul_nonpos_iff.mp hsign.le).elim (fun h => Or.inr ⟨h.2, h.1⟩) Or.inl)
  obtain ⟨t, ht, htz⟩ := intermediate_value_uIcc hcont hmem
  exact ⟨t, ht, Complex.ext (by simpa using htz) (by simpa using hcoeff.im_eval_ofReal t)⟩

/-- **A root of a real-rooted polynomial in a disc about a real center is real**, and the three
facts that follow from it: the root is the coercion of its own real part, it is a root there, and
its real part lies in the real interval the disc cuts out.  Those three are exactly what the Rolle
and intermediate value arguments consume, and reality is what makes them available. -/
private theorem ofReal_re_of_mem_rootsIn {q : Polynomial ℂ} (hreal : IsRealRooted q) {x₀ r : ℝ}
    {z : ℂ} (hz : z ∈ rootsIn q ((x₀ : ℂ)) r) :
    ((z.re : ℝ) : ℂ) = z ∧ q.eval ((z.re : ℝ) : ℂ) = 0 ∧ |z.re - x₀| < r := by
  obtain ⟨hroot, hball⟩ := mem_rootsIn.mp hz
  have hre : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hreal.2 z hroot])
  refine ⟨hre, by rw [hre]; exact (mem_roots'.mp hroot).2, ?_⟩
  have h := mem_ball.mp hball
  rwa [← hre, dist_ofReal_ofReal] at h

/-- **A disc on which the derivative does not vanish carries at most one zero.**  For a real-rooted
polynomial with real coefficients, all the zeros in a disc about a real point are real; two of them
give a critical point between them by Rolle's theorem, and a double one is a critical point
itself. -/
theorem card_rootsIn_le_one_of_derivative_ne_zero {q : Polynomial ℂ} (hreal : IsRealRooted q)
    (hcoeff : HasRealCoeffs q) {x₀ r : ℝ}
    (hder : ∀ z ∈ ball ((x₀ : ℂ)) r, (Polynomial.derivative q).eval z ≠ 0) :
    (rootsIn q ((x₀ : ℂ)) r).card ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a, ha⟩ :=
    Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (rootsIn q ((x₀ : ℂ)) r).card)
  obtain ⟨M, hM⟩ := Multiset.exists_cons_of_mem ha
  have hcardM : 0 < Multiset.card M := by
    have h := congrArg Multiset.card hM
    rw [Multiset.card_cons] at h
    omega
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp hcardM
  have hbM : b ∈ rootsIn q ((x₀ : ℂ)) r := by rw [hM]; exact Multiset.mem_cons_of_mem hb
  obtain ⟨haroot, haball⟩ := mem_rootsIn.mp ha
  obtain ⟨hbroot, hbball⟩ := mem_rootsIn.mp hbM
  have hq0 : q ≠ 0 := fun h => by simp [h] at haroot
  by_cases hab : a = b
  · have hcount : 1 < q.rootMultiplicity a := by
      have hle : rootsIn q ((x₀ : ℂ)) r ≤ q.roots := Multiset.filter_le _ _
      rw [← Polynomial.count_roots q]
      refine lt_of_lt_of_le ?_ (Multiset.count_le_of_le a hle)
      rw [hM, Multiset.count_cons_self]
      have hpos : 0 < Multiset.count a M := Multiset.count_pos.mpr (by rw [hab]; exact hb)
      omega
    exact hder a haball ((one_lt_rootMultiplicity_iff_isRoot hq0).mp hcount).2
  · obtain ⟨ha', hea, haball'⟩ := ofReal_re_of_mem_rootsIn hreal ha
    obtain ⟨hb', heb, hbball'⟩ := ofReal_re_of_mem_rootsIn hreal hbM
    have hne : a.re ≠ b.re := fun h => hab (by rw [← ha', ← hb', h])
    have key : ∀ u v : ℝ, u < v → q.eval (u : ℂ) = 0 → q.eval (v : ℂ) = 0 →
        |u - x₀| < r → |v - x₀| < r → False := by
      intro u v huv hu hv hub hvb
      obtain ⟨w, hw, hwz⟩ := exists_derivative_eq_zero_of_eval_eq_zero hcoeff huv hu hv
      refine hder (w : ℂ) (mem_ball.mpr ?_) hwz
      rw [dist_ofReal_ofReal, abs_lt]
      rw [abs_lt] at hub hvb
      exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a.re b.re h hea heb haball' hbball'
    · exact key b.re a.re h heb hea hbball' haball'

/-- A nonzero derivative at a zero forces a sign change across it. -/
private theorem exists_sign_change {G : ℝ → ℝ} {x₀ c ρ : ℝ} (hd : HasDerivAt G c x₀)
    (h0 : G x₀ = 0) (hc : c ≠ 0) (hρ : 0 < ρ) :
    ∃ a b : ℝ, x₀ - ρ < a ∧ a < x₀ ∧ x₀ < b ∧ b < x₀ + ρ ∧ G a * G b < 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hpos : (0 : ℝ) < c * c := mul_self_pos.mpr hc
  have hev := (hd.mul_const c).eventually_const_lt hpos
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδmem⟩ := hev
  obtain ⟨d, hdpos, hdδ, hdρ⟩ : ∃ d : ℝ, 0 < d ∧ d < δ ∧ d < ρ := by
    have h := lt_min hδ hρ
    exact ⟨min δ ρ / 2, by linarith, by linarith [min_le_left δ ρ], by linarith [min_le_right δ ρ]⟩
  have key : ∀ y : ℝ, y ≠ x₀ → G y = slope G x₀ y * (y - x₀) := fun y hy => by
    rw [slope_def_field, h0, sub_zero]
    field_simp [sub_ne_zero.mpr hy]
  have hslope : ∀ y : ℝ, y ≠ x₀ → |y - x₀| < δ → 0 < slope G x₀ y * c := fun y hy hyd =>
    hδmem (by rwa [Real.dist_eq]) (by simpa using hy)
  have hsa := hslope (x₀ - d) (by intro h; linarith) (by rw [abs_lt]; constructor <;> linarith)
  have hsb := hslope (x₀ + d) (by intro h; linarith) (by rw [abs_lt]; constructor <;> linarith)
  have hprod : 0 < slope G x₀ (x₀ - d) * slope G x₀ (x₀ + d) := by
    nlinarith [mul_pos hsa hsb, hpos]
  refine ⟨x₀ - d, x₀ + d, by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [key (x₀ - d) (by intro h; linarith), key (x₀ + d) (by intro h; linarith)]
  nlinarith [mul_pos hprod (mul_pos hdpos hdpos)]

/-- **A simple real zero of the limit attracts exactly one finite zero.**  Below some threshold
radius, *every* disc about `x₀` carries exactly one
zero of `p n` for all large `n`, counted with multiplicity.  The quantifier over the radius is what
makes the finite zeros converge to `x₀`, rather than merely be unique in one fixed disc. -/
theorem exists_radius_eventually_card_rootsIn_eq_one {p : ℕ → Polynomial ℂ} {f : ℂ → ℂ}
    (hreal : ∀ n, IsRealRooted (p n)) (hcoeff : ∀ n, HasRealCoeffs (p n))
    (hconv : TendstoLocallyUniformly (fun n z => (p n).eval z) f atTop)
    {x₀ : ℝ} (hzero : f (x₀ : ℂ) = 0) (hsimple : deriv f (x₀ : ℂ) ≠ 0) :
    ∃ r > 0, ∀ ε, 0 < ε → ε ≤ r →
      ∀ᶠ n in atTop, (rootsIn (p n) ((x₀ : ℂ)) ε).card = 1 := by
  have hdiff : Differentiable ℂ f := IsLaguerrePolyaLimit.differentiable ⟨p, hreal, hcoeff, hconv⟩
  have hderconv := tendstoLocallyUniformly_derivative hconv
  have hdcont : Continuous (deriv f) :=
    (differentiableOn_univ.mp ((tendstoLocallyUniformlyOn_univ.mpr hderconv).differentiableOn
      (.of_forall fun n => (Polynomial.derivative (p n)).differentiable.differentiableOn)
      isOpen_univ)).continuous
  obtain ⟨r₁, hr₁, hsub⟩ := Metric.isOpen_iff.mp (isOpen_compl_singleton.preimage hdcont)
    ((x₀ : ℂ)) (by simpa using hsimple)
  refine ⟨r₁ / 2, by linarith, ?_⟩
  have hrpos : (0 : ℝ) < r₁ / 2 := by linarith
  have hcb : closedBall ((x₀ : ℂ)) (r₁ / 2) ⊆ ball ((x₀ : ℂ)) r₁ :=
    closedBall_subset_ball (by linarith)
  have hunifder : TendstoUniformlyOn (fun n z => (Polynomial.derivative (p n)).eval z) (deriv f)
      atTop (closedBall ((x₀ : ℂ)) (r₁ / 2)) :=
    tendstoLocallyUniformly_iff_forall_isCompact.mp hderconv _ (isCompact_closedBall _ _)
  have hevder : ∀ᶠ n in atTop, ∀ z ∈ closedBall ((x₀ : ℂ)) (r₁ / 2),
      (Polynomial.derivative (p n)).eval z ≠ 0 :=
    eventually_zero_free_of_tendstoUniformlyOn (isCompact_closedBall _ _) hdcont.continuousOn
      (fun z hz => by simpa using hsub (hcb hz)) hunifder
  have hderim : (deriv f ((x₀ : ℂ))).im = 0 :=
    im_apply_ofReal_of_tendsto (fun n => (hcoeff n).derivative) hderconv x₀
  have hcre : (deriv f ((x₀ : ℂ))).re ≠ 0 := fun h =>
    hsimple (Complex.ext (by simpa using h) (by simpa using hderim))
  have hG : HasDerivAt (fun t : ℝ => (f (t : ℂ)).re) ((deriv f ((x₀ : ℂ))).re) x₀ :=
    (hdiff ((x₀ : ℂ))).hasDerivAt.real_of_complex
  have hpt : ∀ w : ℂ, Tendsto (fun n => ((p n).eval w).re) atTop (𝓝 (f w).re) := fun w =>
    (Complex.continuous_re.tendsto _).comp
      ((tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at (mem_univ w))
  intro ε hε hεr
  obtain ⟨a, b, hab1, hab2, hab3, hab4, hsign⟩ :=
    exists_sign_change hG (by simpa using congrArg Complex.re hzero) hcre hε
  have hsigneq : ∀ᶠ n in atTop, ((p n).eval ((a : ℂ))).re * ((p n).eval ((b : ℂ))).re < 0 :=
    ((hpt (a : ℂ)).mul (hpt (b : ℂ))).eventually_lt_const hsign
  filter_upwards [hevder, hsigneq] with n hnder hnsign
  refine le_antisymm (card_rootsIn_le_one_of_derivative_ne_zero (hreal n) (hcoeff n)
    (fun z hz => hnder z (ball_subset_closedBall (ball_subset_ball hεr hz)))) ?_
  obtain ⟨t, ht, hroot⟩ := exists_ofReal_root_of_re_mul_neg (hcoeff n) hnsign
  have hpn0 : p n ≠ 0 := fun h => by simp [h] at hnsign
  have htdist : |t - x₀| < ε := by
    rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [abs_lt] <;> constructor <;> linarith
  have hmemroots : (t : ℂ) ∈ rootsIn (p n) ((x₀ : ℂ)) ε :=
    mem_rootsIn.mpr ⟨mem_roots'.mpr ⟨hpn0, hroot⟩,
      mem_ball.mpr (by rw [dist_ofReal_ofReal]; exact htdist)⟩
  have hcard : 0 < (rootsIn (p n) ((x₀ : ℂ)) ε).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨_, hmemroots⟩
  omega

/-! ### The corollary -/

/-- **The locally uniform limit of real-rooted polynomials lies in the class.**  A family of
real-rooted polynomials with real coefficients
converging locally uniformly on `ℂ` to a limit that is not identically zero puts the limit in the
Laguerre--Pólya class; the limit is entire, real on the real axis, and every one of its zeros is
real.

The real-rootedness of the approximating polynomials is a hypothesis, never a conclusion. -/
theorem isLaguerrePolyaLimit_of_tendsto {p : ℕ → Polynomial ℂ} {f : ℂ → ℂ}
    (hreal : ∀ n, IsRealRooted (p n)) (hcoeff : ∀ n, HasRealCoeffs (p n))
    (hconv : TendstoLocallyUniformly (fun n z => (p n).eval z) f atTop) (hne : ∃ w, f w ≠ 0) :
    IsLaguerrePolyaLimit f ∧ Differentiable ℂ f ∧ (∀ x : ℝ, (f (x : ℂ)).im = 0) ∧
      ∀ z : ℂ, f z = 0 → z.im = 0 := by
  have hLP : IsLaguerrePolyaLimit f := ⟨p, hreal, hcoeff, hconv⟩
  exact ⟨hLP, hLP.differentiable, hLP.im_apply_ofReal, fun z hz => hLP.im_eq_zero_of_eq_zero hne hz⟩

/-! ### Members of the class

Every real-rooted polynomial with real coefficients lies in the class by the constant family, so a
witness of that shape says nothing about the limit.  `exp` is a member that is not a polynomial at
all: the Euler approximants `(1 + z/n)^n` have real coefficients and the single real root `-n`, and
they converge to `exp` uniformly on every ball.  The class therefore strictly contains the
real-rooted polynomials, which is the whole point of closing it under limits. -/

/-- Every real-rooted polynomial with real coefficients lies in the class, by the constant
family. -/
theorem isLaguerrePolyaLimit_eval {q : Polynomial ℂ} (hreal : IsRealRooted q)
    (hcoeff : HasRealCoeffs q) : IsLaguerrePolyaLimit (fun z => q.eval z) := by
  refine ⟨fun _ => q, fun _ => hreal, fun _ => hcoeff, ?_⟩
  intro u hu x
  refine ⟨univ, univ_mem, ?_⟩
  filter_upwards with n y _
  simpa using refl_mem_uniformity hu

/-- The Euler approximant `(1 + z/n)^n`, built by coercing a real polynomial so that its
coefficients are real by construction. -/
private noncomputable def expApprox (n : ℕ) : Polynomial ℂ :=
  ((Polynomial.C ((n : ℝ)⁻¹) * Polynomial.X + 1) ^ n).map (algebraMap ℝ ℂ)

private theorem hasRealCoeffs_expApprox (n : ℕ) : HasRealCoeffs (expApprox n) := fun i => by
  rw [expApprox, Polynomial.coeff_map]
  simp

private theorem eval_expApprox (n : ℕ) (z : ℂ) : (expApprox n).eval z = (1 + z / n) ^ n := by
  simp [expApprox, div_eq_mul_inv, add_comm]
  ring

private theorem isRealRooted_expApprox (n : ℕ) : IsRealRooted (expApprox n) := by
  rw [isRealRooted_iff_forall_im]
  intro z hz
  have hval : (1 + z / (n : ℂ)) ^ n = 0 := by
    rw [← eval_expApprox]; exact (mem_roots'.mp hz).2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hval
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have h1 : 1 + z / (n : ℂ) = 0 := pow_eq_zero_iff hn.ne' |>.mp hval
    have hzn : z = -(n : ℂ) := by
      field_simp at h1
      linear_combination h1
    simp [hzn]

/-- The Euler approximants converge to `exp` at the rate `1/n`, uniformly on a ball.  The estimate
is the logarithm one: `n log (1 + z/n)` differs from `z` by `O(1/n)`, and `exp` is Lipschitz on the
bounded set where that difference lives. -/
private theorem norm_eval_expApprox_sub_exp_le {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn2 : 2 * R ≤ n) (hnsq : R ^ 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖(expApprox n).eval z - Complex.exp z‖ ≤ 2 * Real.exp R * R ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by exact_mod_cast hn0.ne')
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = z / (n : ℂ) := ⟨_, rfl⟩
  have heval : (expApprox n).eval z = (1 + w) ^ n := by rw [eval_expApprox, hwdef]
  have hnw : (n : ℂ) * w = z := by rw [hwdef]; field_simp
  have hwn : ‖w‖ ≤ R / n := by
    rw [hwdef, norm_div, Complex.norm_natCast]
    gcongr
  have hwhalf : ‖w‖ ≤ 1 / 2 :=
    hwn.trans (by rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith)
  have hwlt : ‖w‖ < 1 := by linarith
  have h1w : (1 : ℂ) + w ≠ 0 := fun h => by
    rw [show w = -1 by linear_combination h] at hwhalf; norm_num at hwhalf
  have hlog : ‖(n : ℂ) * Complex.log (1 + w) - z‖ ≤ R ^ 2 / n := by
    have hfac : (n : ℂ) * Complex.log (1 + w) - z = (n : ℂ) * (Complex.log (1 + w) - w) := by
      rw [mul_sub, hnw]
    have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hstep : ‖Complex.log (1 + w) - w‖ ≤ (R / n) ^ 2 := by
      refine (Complex.norm_log_one_add_sub_self_le hwlt).trans ?_
      calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ (R / n) ^ 2 * 2 / 2 := by gcongr
        _ = (R / n) ^ 2 := by ring
    rw [hfac, norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ‖Complex.log (1 + w) - w‖ ≤ (n : ℝ) * (R / n) ^ 2 := by gcongr
      _ = R ^ 2 / n := by field_simp
  have hle1 : ‖(n : ℂ) * Complex.log (1 + w) - z‖ ≤ 1 := hlog.trans ((div_le_one hn0).mpr hnsq)
  have hpow : (expApprox n).eval z = Complex.exp ((n : ℂ) * Complex.log (1 + w)) := by
    rw [heval, Complex.exp_nat_mul, Complex.exp_log h1w]
  have hsplit : Complex.exp ((n : ℂ) * Complex.log (1 + w)) - Complex.exp z
      = Complex.exp z * (Complex.exp ((n : ℂ) * Complex.log (1 + w) - z) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; ring
  rw [hpow, hsplit, norm_mul, Complex.norm_exp]
  have hre : Real.exp z.re ≤ Real.exp R :=
    Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans hz)
  have hc : ‖Complex.exp ((n : ℂ) * Complex.log (1 + w) - z) - 1‖ ≤ 2 * (R ^ 2 / n) :=
    (Complex.norm_exp_sub_one_le hle1).trans (by gcongr)
  calc Real.exp z.re * ‖Complex.exp ((n : ℂ) * Complex.log (1 + w) - z) - 1‖
      ≤ Real.exp R * (2 * (R ^ 2 / n)) :=
        mul_le_mul hre hc (norm_nonneg _) (Real.exp_pos R).le
    _ = 2 * Real.exp R * R ^ 2 / n := by ring

private theorem tendstoUniformlyOn_expApprox {R : ℝ} (hR : 0 < R) :
    TendstoUniformlyOn (fun n z => (expApprox n).eval z) Complex.exp atTop
      (closedBall (0 : ℂ) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max (2 * R) (R ^ 2)) (2 * Real.exp R * R ^ 2 / ε))
  filter_upwards [eventually_ge_atTop N] with n hn z hz
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : 2 * R ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hN.le.trans hNn)
  have hnsq : R ^ 2 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hN.le.trans hNn)
  have hnε : 2 * Real.exp R * R ^ 2 / ε < n :=
    lt_of_le_of_lt (le_max_right _ _) (hN.trans_le hNn)
  have hn0 : (0 : ℝ) < n := by linarith
  have hzR : ‖z‖ ≤ R := by simpa using mem_closedBall.mp hz
  rw [dist_eq_norm, norm_sub_rev]
  refine lt_of_le_of_lt (norm_eval_expApprox_sub_exp_le hR hn2 hnsq hzR) ?_
  rw [div_lt_iff₀ hε] at hnε
  rw [div_lt_iff₀ hn0]
  linarith [mul_comm ε (n : ℝ)]

private theorem tendstoLocallyUniformly_expApprox :
    TendstoLocallyUniformly (fun n z => (expApprox n).eval z) Complex.exp atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
  have hR : (0 : ℝ) < ‖x‖ + 1 := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_expApprox hR) ε hε] with
    n hn y hy
  refine hn y (mem_closedBall.mpr ?_)
  have h1 : dist y x < 1 := mem_ball.mp hy
  have h2 : dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
  have h3 : dist x 0 = ‖x‖ := by simp [dist_eq_norm]
  linarith

/-- **The Euler approximants have their roots on the closed negative ray.**  `(1 + z/n)^n` vanishes
only at `z = -n`, and `expApprox 0 = 1` has no root at all.

The nonpositivity is what `IsRealRooted` drops: it records that the roots are real and not where
they sit.  A consumer localizing zeros to a ray needs the sharper statement, so it is given here
rather than reconstructed from the class. -/
theorem exists_tendstoLocallyUniformly_exp :
    ∃ p : ℕ → Polynomial ℂ, (∀ n, HasRealCoeffs (p n)) ∧
      (∀ n, ∀ z : ℂ, (p n).eval z = 0 → z.im = 0 ∧ z.re ≤ 0) ∧
      TendstoLocallyUniformly (fun n z => (p n).eval z) Complex.exp atTop := by
  refine ⟨expApprox, hasRealCoeffs_expApprox, ?_, ?_⟩
  · intro n z hz
    rw [eval_expApprox] at hz
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hz
    · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have h1 : 1 + z / (n : ℂ) = 0 := pow_eq_zero_iff hn.ne' |>.mp hz
      have hzn : z = -(n : ℂ) := by
        field_simp at h1
        linear_combination h1
      rw [hzn]
      refine ⟨by simp, ?_⟩
      simp only [Complex.neg_re, Complex.natCast_re, neg_nonpos]
      positivity
  · exact tendstoLocallyUniformly_expApprox

/-- **`exp` lies in the Laguerre--Pólya class.**  A member that is not a polynomial: the class is
strictly larger than the real-rooted polynomials it is generated from. -/
theorem isLaguerrePolyaLimit_exp : IsLaguerrePolyaLimit Complex.exp :=
  ⟨expApprox, isRealRooted_expApprox, hasRealCoeffs_expApprox, tendstoLocallyUniformly_expApprox⟩

/-- `exp` is not the evaluation of any polynomial: a polynomial with no zero is constant, and `exp`
has no zero and is not constant.  With `isLaguerrePolyaLimit_exp` this makes the containment of the
real-rooted polynomials in the class strict. -/
theorem not_exists_polynomial_eval_eq_exp :
    ¬ ∃ q : Polynomial ℂ, ∀ z : ℂ, q.eval z = Complex.exp z := by
  rintro ⟨q, hq⟩
  have hdeg : q.natDegree = 0 := by
    by_contra hne
    obtain ⟨z, hz⟩ := Complex.exists_root (degree_pos_of_ne_zero_of_nonunit
      (fun h => hne (by simp [h])) (fun h => hne (natDegree_eq_zero_of_isUnit h)))
    exact Complex.exp_ne_zero z (by rw [← hq z]; exact hz)
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  have h0 : Complex.exp 0 = c := by rw [← hq 0, ← hc]; simp
  have h1 : Complex.exp 1 = c := by rw [← hq 1, ← hc]; simp
  have hR0 : ((Real.exp 0 : ℝ) : ℂ) = c := by rw [Complex.ofReal_exp]; simpa using h0
  have hR1 : ((Real.exp 1 : ℝ) : ℂ) = c := by rw [Complex.ofReal_exp]; simpa using h1
  have hRe : Real.exp 0 = Real.exp 1 := by exact_mod_cast hR0.trans hR1.symm
  linarith [Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)]

/-- **The class strictly contains the real-rooted polynomials it is generated from.**  Together with
`isLaguerrePolyaLimit_eval`, which puts every such polynomial in the class, this is what the passage
to the limit buys. -/
theorem exists_isLaguerrePolyaLimit_not_polynomial :
    ∃ f : ℂ → ℂ, IsLaguerrePolyaLimit f ∧ ¬ ∃ q : Polynomial ℂ, ∀ z : ℂ, q.eval z = f z :=
  ⟨Complex.exp, isLaguerrePolyaLimit_exp, not_exists_polynomial_eval_eq_exp⟩


/-! ### Axiom footprint -/

/-- info: 'Shields.IsLaguerrePolyaLimit.of_tendstoLocallyUniformly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLaguerrePolyaLimit.of_tendstoLocallyUniformly

/-- info: 'Shields.IsLaguerrePolyaLimit.im_eq_zero_of_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLaguerrePolyaLimit.im_eq_zero_of_eq_zero

/-- info: 'Shields.exists_radius_eventually_card_rootsIn_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_radius_eventually_card_rootsIn_eq_one

/-- info: 'Shields.exists_isLaguerrePolyaLimit_not_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_isLaguerrePolyaLimit_not_polynomial

/-- info: 'Shields.exists_tendstoLocallyUniformly_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_tendstoLocallyUniformly_exp

end Shields
