/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Topology.EMetricSpace.BoundedVariationRestrict
import ForgacsTran.BranchSupply
import ForgacsTran.BranchAmplitude
import ForgacsTran.FTGeometryAssembly
import ForgacsTran.TauArcAt
import ForgacsTran.FTBranchLimitPoint
import ForgacsTran.EndpointCofactorBound
import ForgacsTran.BranchAngleDerivSum
import ForgacsTran.PolarAngleBase
import ForgacsTran.AngleChartForm

/-!
# The branch-geometry group of the supply, at a general pencil

`BranchSupply.exists_uniform_ftBranchSupply` asks four things of the branch — `hγd`, `hd2`,
`hc2`, `hreg` — and everything the tree has assembled for them so far has been at one
worked pencil.  This module supplies all four at a **general** admissible pencil.

**Why that is reachable at all.**  Those four clauses used to be asked on an open set
containing the *closed* arc, and there they are not merely unproved but **unsatisfiable**:
`ftTauLower` extends the radius below `0` by the constant `x₁`, slope `0`, while the branch
leaves the collision with slope `τ'(0)`, so no two-sided derivative exists at `0`
(`BranchSupplyCubicWitness.not_exists_hasDerivAt_ftPrincipal_ftTauArcAt_cubic_zero`, and
`ftTauLower` does not mention `r`, so it is not an `r = 1` phenomenon).  Once the branches
of `RootBranchState` were pinned inside the arc rather than at its ends, the supply began
asking on the **open** arc instead — and there the tree already had every ingredient.  What
follows is four lines of assembly over `hasDerivAt_ftPrincipal_ftTau`,
`BranchCurvature.hasDerivAt_ftGammaDeriv` and `BranchAmplitude.continuousAt_ftGammaDeriv2`.

`hreg` needs no hypothesis at all: `γ' = (τ' + iτ)e^{iθ}` has imaginary part `τ`, positive
wherever the branch exists.

## What the collar still needs, and two values that had to be corrected

The **collar** of `hloc` reaches the collision, and the branch's behaviour there is not
supplied by anything above.  Of the three facts, the **first is now proved** at a general
pencil, off `FTBranchLimitPoint.exists_bound_ftTau_sub_linear` — the paper's cluster
expansion `τ(δ) = a_i - a_i·cot(π/ρ)·δ + O(δ²)`:

* `hasDerivWithinAt_ftTauArcAt_zero` — the branch's one-sided derivative at `0`.
* `hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero` — and so `hd0`, the collar's own binder.

**Two values had to be corrected on the way, and both are the division convention.**
`ftTauDeriv a r l 0 = 0` (`ftTauDeriv_zero`): its denominator `ftAngleSumDerivTau` carries
`sin θ`, which vanishes at the collision, so the formula returns a well-formed `0` that is
**not** the branch's slope — at the worked cubic the true slope is `-1/√3`.  And
`ftGammaDeriv a r l 0` is junk for the same reason plus `ftTau`'s own fallthrough
(`ftGammaDeriv_zero_eq`).  So a collar stated with either of those as its `dγ 0` would be
stating something false; the corrected `γ'(0) = -a_i·cot(π/ρ) + i·a_i` is what the two
theorems above deliver.

`ftGammaDeriv_zero_corrected_ne_zero` gives `h0`, and it survives the `ρ = 2` corner where
`cot(π/2) = 0` kills the slope: it goes through `Im γ'(0) = τ(0) = a_i > 0`, not through
`τ'(0) ≠ 0`.

**The second-order half does not need a second-order expansion, and in the end it collapses
to one statement.**  `ftTauDeriv2 a r l 0` is `0` by the same convention
(`ftTauDeriv2_zero`), so nothing may be written against it.  Asking what `hlip` consumes
then removes the endpoint derivative entirely —
`exists_lipschitz_of_bound_of_continuousWithinAt` runs on `[ε, θ]` and `ε → 0⁺` — and what
is left is supplied by machinery `EndpointCofactorBound` already carries.  The whole of it
comes from

* `∃ D2, Tendsto (ftTauDeriv2 a r l) (𝓝[>] 0) (𝓝 D2)` — `τ''` **converges** at the
  collision,

through `exists_lipschitz_ftGammaDerivAt_of_tendsto_ftTauDeriv2`: the tree turns that into
limits for `τ` and `τ'` (`exists_tau_limits_of_tendsto_ftTauDeriv2`) and for `γ''`
(`tendsto_ftGammaDeriv2_of_tendsto`), a convergent `γ''` is bounded just to the right of
the endpoint, and the Lipschitz lemma asks nothing more.  So the general collar's remaining
analytic input is **one limit**, not a two-sided bound and not an expansion.

`ftCurvature_pos` gives `τ'' < τ + 2τ'²/τ` on the open arc, which is an upper bound on
`τ''` **conditional on `τ'` being bounded** — the right-hand side carries `τ'²` — so it
does not by itself supply the statement above, and `τ'` bounded near the collision is not
proved either.  At the worked cubic all of it holds and `τ''` is finite there
(`BranchSupplyCubicWitness.cubicTauDeriv2_zero` gives `7/9`), so the general statement is
unproved rather than false.

`ftGammaDerivAt` is `γ'` with the collision value supplied, the same device `ftTauArcAt`
uses at the far endpoint and for the same reason: the formula's own value there is junk.

Two boundaries on the expansion itself: it carries `hρ : 2 ≤ ρ`, so a simple smallest zero
needs a different route, and at `ρ = 2` its linear coefficient vanishes.

**The diagnosis, which is a reading rather than a theorem here.**  A collision is where two
branches of the pencil meet, so the branch equation `F(τ,θ) = 0` has *both* first partials
vanishing there and the local structure is set by the Hessian.  At the worked cubic
`F = 2τ³cos θ − 3τ² + 1` gives `F_ττ = 6`, `F_τθ = 0`, `F_θθ = −2` at `(1,0)`, an
indefinite form, so the two branches cross transversally with slopes `±1/√3` and each is
smooth up to the meeting point — which is why `cubicTauDeriv 0 = -√3/3` is finite rather
than infinite.  A cusp would give `τ' → ∞` and the collar would genuinely fail.  So what
the three statements above really need is that the collision is a **node**, and that is a
nondegeneracy of the Hessian rather than an estimate.  Not proved here at any pencil; the
cubic's numbers are arithmetic I did by hand, not a formalized derivation.

Sorry-free.

## Main statements

* `hasDerivAt_ftPrincipal_ftTauArcAt` — `hγd`, in the arc's own parametrization.
* `ft_geometry_group` — the four clauses together.
* `eVariationOn_le_of_forall_Icc`, `ft_hKvar`, `ft_curvature_group` — `hKvar` at a general
  pencil, carried from the compact bound to the open arc at an arbitrary base.
* `ftDen_coeff_one_of_two_le` — why `hWL` cannot be repaired by an endpoint value for the
  spectral parameter.
* `ftTauDeriv_zero`, `ftGammaDeriv_zero_eq` — the two junk values at the collision.
* `ftTauDeriv2_zero`, `ftGammaDerivAt` — the second-order junk value, and `γ'` with the
  collision's value supplied.
* `exists_lipschitz_of_bound_of_continuousWithinAt` — `hlip` from a limit and a bound,
  with no derivative at the endpoint.
* `tendsto_ftGammaDeriv_of_tendsto`,
  `exists_lipschitz_ftGammaDerivAt_of_tendsto_ftTauDeriv2` — `hlip` at a general pencil from
  the single hypothesis that `τ''` converges at the collision.
* `hasDerivWithinAt_ftTauArcAt_zero`,
  `hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero`,
  `gammaDerivValue_ne_zero`, `ftGammaDeriv_zero_corrected_ne_zero` — the collar's `hd0` and
  `h0`, at a general pencil, with `h0` routed through the radius rather than the slope so it
  holds in every arrival regime.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
and the principal amplitude» (`sec:geometry`, `eq:principal-pair`), as the branch supply
consumes it.

## Tags

branch geometry, general pencil, open arc, collision
-/

namespace ForgacsTran

open Polynomial Set Real
open scoped ENNReal

/-- **`hγd` at a general pencil**, in the arc's own parametrization: `ftTauArcAt` agrees
with `ftTau` on the open arc, which is where the branch supply now asks. -/
theorem hasDerivAt_ftPrincipal_ftTauArcAt {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (x₁ aEnd : ℝ)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / r)) :
    HasDerivAt (ftPrincipal (ftTauArcAt a r (n - 1) x₁ aEnd))
      (ftGammaDeriv a r (n - 1) θ) θ := by
  have h2 : HasDerivAt (ftPrincipal (ftTau a r (n - 1))) (ftGammaDeriv a r (n - 1) θ) θ := by
    refine (hasDerivAt_ftPrincipal_ftTau hn ha hr hnr hθ).congr_deriv ?_
    rw [ftGammaDeriv]
    ring
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
  rw [ftPrincipal, ftPrincipal, ftTauArcAt_agree a r (n - 1) x₁ aEnd hs.1 hs.2]

/-- **The branch-geometry group of `exists_uniform_ftBranchSupply`, at a GENERAL pencil.**
Every clause on the open arc, which is where the supply asks for them since the branch
pins moved off the endpoints — and that is exactly why this is reachable in general while
the collar's endpoint data is not. -/
theorem ft_geometry_group {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ) (x₁ aEnd : ℝ) :
    (∀ s ∈ Ioo (0 : ℝ) (π / r),
        HasDerivAt (ftPrincipal (ftTauArcAt a r (n - 1) x₁ aEnd))
          (ftGammaDeriv a r (n - 1) s) s)
      ∧ (∀ s ∈ Ioo (0 : ℝ) (π / r),
        HasDerivAt (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1) s) s)
      ∧ ContinuousOn (ftGammaDeriv2 a r (n - 1)) (Ioo (0 : ℝ) (π / r))
      ∧ (∀ s ∈ Ioo (0 : ℝ) (π / r), ftGammaDeriv a r (n - 1) s ≠ 0) :=
  ⟨fun _ hs => hasDerivAt_ftPrincipal_ftTauArcAt hn ha hr hnr x₁ aEnd hs,
    fun _ hs => hasDerivAt_ftGammaDeriv hn ha hr hs hb,
    fun _ hs => (continuousAt_ftGammaDeriv2 hn ha hr hs hb).continuousWithinAt,
    fun s hs => ftGammaDeriv_ne_zero (hb s hs)⟩

/-- **`ftTauDeriv` is `0` at the collision, by the division convention.**  Its denominator
`ftAngleSumDerivTau` carries `sin θ`, which vanishes at `0`, so the formula returns `0`
there — a well-formed number that is **not** the branch's one-sided slope. -/
theorem ftAngleSumDerivTau_zero {n : ℕ} (a : Fin n → ℝ) (τ : ℝ) :
    ftAngleSumDerivTau a τ 0 = 0 := by
  rw [ftAngleSumDerivTau]
  simp

theorem ftTauDeriv_zero {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) : ftTauDeriv a r l 0 = 0 := by
  rw [ftTauDeriv, ftAngleSumDerivTau_zero, div_zero]

/-- **The branch's one-sided derivative at the collision, at a general pencil.**  The slope
is the cluster expansion's, `-a_i·cot(π/ρ)`, and **not** `ftTauDeriv a r l 0`, which the
division convention makes `0`. -/
theorem hasDerivWithinAt_ftTauArcAt_zero {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {j : Fin n} (hj : j ∈ S) (hji : j ≠ i)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ k ∉ S, a i * (1 + c) < a k) (aEnd : ℝ) :
    HasDerivWithinAt (ftTauArcAt a r (n - 1) (a i) aEnd)
      (-(a i * Real.cos (π / ρ) / Real.sin (π / ρ))) (Ici 0) 0 := by
  obtain ⟨C, ε, hC, hε, hbd⟩ :=
    exists_bound_ftTau_sub_linear hn2 ha hr hS hcard hρ hmin hj hji hc hgap
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hπr : (0 : ℝ) < π / r := div_pos Real.pi_pos hrpos
  have hzero : ftTauArcAt a r (n - 1) (a i) aEnd 0 = a i :=
    ftTauArcAt_zero a r (n - 1) (a i) aEnd hπr
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c' hc'
  have hη : (0 : ℝ) < min ε (min (π / r) (c' / C)) :=
    lt_min hε (lt_min hπr (div_pos hc' hC))
  filter_upwards [Ico_mem_nhdsGE hη] with δ hδ
  rcases eq_or_lt_of_le hδ.1 with h0 | h0
  · simp [← h0]
  have hδε : δ ≤ ε := le_trans hδ.2.le (min_le_left _ _)
  have hδπ : δ < π / r := lt_of_lt_of_le hδ.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδc : δ < c' / C := lt_of_lt_of_le hδ.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hagree : ftTauArcAt a r (n - 1) (a i) aEnd δ = ftTau a r (n - 1) δ :=
    ftTauArcAt_agree a r (n - 1) (a i) aEnd h0 hδπ
  have h := hbd δ h0 hδε
  rw [hzero, hagree, Real.norm_eq_abs, Real.norm_eq_abs]
  have hexpr : ftTau a r (n - 1) δ - a i - (δ - 0) • -(a i * Real.cos (π / ρ) / Real.sin (π / ρ))
      = ftTau a r (n - 1) δ - (a i - a i * Real.cos (π / ρ) / Real.sin (π / ρ) * δ) := by
    simp only [smul_eq_mul]
    ring
  rw [hexpr]
  have hCδ : C * δ ≤ c' := by
    rw [← le_div_iff₀' hC]
    exact hδc.le
  calc |ftTau a r (n - 1) δ - (a i - a i * Real.cos (π / ρ) / Real.sin (π / ρ) * δ)|
      ≤ C * δ ^ 2 := h
    _ = (C * δ) * δ := by ring
    _ ≤ c' * δ := by nlinarith [h0.le]
    _ = c' * |δ - 0| := by rw [sub_zero, abs_of_pos h0]

/-- **`ftGammaDeriv` is junk at the collision too.**  It is built from `ftTau` and
`ftTauDeriv` at `0`, and neither is the branch's value there: `ftTauDeriv` is `0` by the
division convention, and `ftTau` falls through to its own `else` branch.  So a general
collar must carry the corrected `γ'(0)` below rather than `ftGammaDeriv a r l 0`. -/
theorem ftGammaDeriv_zero_eq {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) :
    ftGammaDeriv a r l 0 = ((ftTau a r l 0 : ℝ) : ℂ) * Complex.I := by
  rw [ftGammaDeriv, ftTauDeriv_zero]
  push_cast
  simp

/-- **`γ'` at the collision, one-sided, at a general pencil.**  `γ = τe^{iθ}` and the
exponential is `1` there, so the value is `τ'(0) + iτ(0)` with `τ'(0)` the cluster
expansion's slope and `τ(0) = a_i`. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero {n r ρ : ℕ} {a : Fin n → ℝ}
    {S : Finset (Fin n)} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {j : Fin n} (hj : j ∈ S) (hji : j ≠ i)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ k ∉ S, a i * (1 + c) < a k) (aEnd : ℝ) :
    HasDerivWithinAt (ftPrincipal (ftTauArcAt a r (n - 1) (a i) aEnd))
      (((-(a i * Real.cos (π / ρ) / Real.sin (π / ρ)) : ℝ) : ℂ)
        + ((a i : ℝ) : ℂ) * Complex.I) (Ici 0) 0 := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hπr : (0 : ℝ) < π / r := div_pos Real.pi_pos hrpos
  have hzero : ftTauArcAt a r (n - 1) (a i) aEnd 0 = a i :=
    ftTauArcAt_zero a r (n - 1) (a i) aEnd hπr
  have hτ : HasDerivWithinAt (fun t : ℝ => ((ftTauArcAt a r (n - 1) (a i) aEnd t : ℝ) : ℂ))
      (((-(a i * Real.cos (π / ρ) / Real.sin (π / ρ)) : ℝ) : ℂ)) (Ici 0) 0 :=
    (hasDerivWithinAt_ftTauArcAt_zero hn2 ha hr hS hcard hρ hmin hj hji hc hgap
      aEnd).ofReal_comp
  have hE : HasDerivWithinAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * (1 * Complex.I)) (Ici 0) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp).hasDerivWithinAt
  refine (hτ.mul hE).congr_deriv ?_
  rw [hzero]
  push_cast
  simp

/-- **`γ'(0) ≠ 0` needs only the radius, never the slope.**  `γ' = (τ' + iτ)e^{iθ}` and the
exponential is `1` at the endpoint, so the value there is `τ'(0) + iτ(0)` and its imaginary
part is `τ(0)`.  Whatever the arrival slope is — and it differs by regime — the value is
nonzero as soon as the radius is positive.

That is what makes `h0` survive the corners.  At `ρ = 2` the linear coefficient vanishes,
since `cot(π/2) = 0`; at `ρ = 1` the branch arrives at an interior critical point with slope
`0` and a *different* endpoint radius entirely.  An argument routed through `τ'(0) ≠ 0`
would fail at both; this one does not see the slope. -/
theorem gammaDerivValue_ne_zero {s t : ℝ} (ht : 0 < t) :
    ((s : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have him : (((s : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re]
    ring
  rw [h] at him
  exact absurd him.symm (ne_of_gt ht)

/-- **`h0` at the `ρ ≥ 2` collision**, as an instance: the radius there is `a_i`. -/
theorem ftGammaDeriv_zero_corrected_ne_zero {n : ℕ} {a : Fin n → ℝ} {i : Fin n} {ρ : ℕ}
    (ha : ∀ k, 0 < a k) :
    (((-(a i * Real.cos (π / ρ) / Real.sin (π / ρ)) : ℝ) : ℂ)
      + ((a i : ℝ) : ℂ) * Complex.I) ≠ 0 :=
  gammaDerivValue_ne_zero (ha i)

/-- **`ftTauDeriv2` is `0` at the collision as well**, by the same division convention:
its denominator is `ftAngleSumDerivTau ^ 2`, and that vanishes there.  So a second-order
statement written against `ftTauDeriv2 a r l 0` would assert the same false thing the
first-order one did. -/
theorem ftTauDeriv2_zero {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) : ftTauDeriv2 a r l 0 = 0 := by
  rw [ftTauDeriv2, ftAngleSumDerivTau_zero]
  simp

section Lipschitz

open Filter Topology

/-- **`hlip` from a bound and a limit, with no derivative at the endpoint.**
`exists_lipschitz_of_continuousOn_deriv2` asks for `f'` at `0`, which at a collision means
knowing `τ''` there.  This asks only that `f` reach its endpoint value continuously and
that `f'` be **bounded** on the punctured collar — the mean value theorem on `[ε, θ]` and
`ε → 0⁺`.  Strictly weaker, and it is what the general collar can actually be given. -/
theorem exists_lipschitz_of_bound_of_continuousWithinAt {f f' : ℝ → ℂ} {b C : ℝ}
    (hcont : ContinuousWithinAt f (Ici 0) 0)
    (hd : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt f (f' x) x)
    (hbd : ∀ x ∈ Ioo (0 : ℝ) b, ‖f' x‖ ≤ C) :
    ∀ θ ∈ Ico (0 : ℝ) b, ‖f θ - f 0‖ ≤ C * θ := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]; simp
  -- on every `[ε, θ]` inside the punctured collar the mean value theorem applies
  have hseg : ∀ ε ∈ Ioo (0 : ℝ) θ, ‖f θ - f ε‖ ≤ C * (θ - ε) := by
    intro ε hε
    have hsub : Icc ε θ ⊆ Ioo (0 : ℝ) b := fun x hx =>
      ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hcontOn : ContinuousOn f (Icc ε θ) :=
      fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt
    have hd' : ∀ x ∈ Ico ε θ, HasDerivWithinAt f (f' x) (Ici x) x :=
      fun x hx => (hd x (hsub (Ico_subset_Icc_self hx))).hasDerivWithinAt
    exact norm_image_sub_le_of_norm_deriv_right_le_segment hcontOn hd'
      (fun x hx => hbd x (hsub (Ico_subset_Icc_self hx))) θ ⟨hε.2.le, le_rfl⟩
  -- and the endpoint value is the limit
  have htend : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    hcont.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have h1 : Tendsto (fun ε : ℝ => ‖f θ - f ε‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖f θ - f 0‖) :=
    (continuous_const.sub continuous_id).continuousAt.tendsto.comp htend |>.norm
  have h2 : Tendsto (fun ε : ℝ => C * (θ - ε)) (𝓝[>] (0 : ℝ)) (𝓝 (C * (θ - 0))) :=
    ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖f θ - f ε‖ ≤ C * (θ - ε) := by
    filter_upwards [Ioo_mem_nhdsGT h0] with ε hε
    exact hseg ε hε
  have := le_of_tendsto_of_tendsto h1 h2 hev
  rwa [sub_zero] at this

end Lipschitz

open scoped Classical in
/-- **`γ'` with the collision's value supplied**, exactly as `ftTauArcAt` supplies the far
endpoint's: `ftGammaDeriv a r l 0` is the division convention's junk, so a collar carrying
it as `dγ 0` would be stating something false, and the value has to come in as a
parameter. -/
noncomputable def ftGammaDerivAt {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (v : ℂ) : ℝ → ℂ :=
  Function.update (ftGammaDeriv a r l) 0 v

open scoped Classical in
@[simp] theorem ftGammaDerivAt_zero {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (v : ℂ) :
    ftGammaDerivAt a r l v 0 = v := by
  simp [ftGammaDerivAt]

open scoped Classical in
theorem ftGammaDerivAt_of_ne {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (v : ℂ) {θ : ℝ}
    (hθ : θ ≠ 0) : ftGammaDerivAt a r l v θ = ftGammaDeriv a r l θ := by
  simp [ftGammaDerivAt, hθ]

/-! ### What `hWL` can and cannot be repaired by

At the `2 ≤ r` upper endpoint the branch runs into the origin, and there the paper's
amplitude **vanishes** — `eq:W-on-g` gives `W = B(γ)·γ/(rQ(γ) − γQ′(γ))`, whose numerator
carries an explicit `γ` — while Lean's `ftAmp` evaluates to `-B(0)/Q'(0)`, finite and
nonzero.  The two differ because the spectral parameter diverges there, so the paper's `W`
is the limit of an `∞·0` that cancels the numerator and the pointwise evaluation is not.
It is `x/0`'s mirror: at the **lower** endpoint Lean's amplitude is `0` while the true one
diverges, and here it is finite while the true one vanishes — worse to spot, because the
value is unremarkable.

**The correction cannot sit on the spectral parameter.**  `(ftCofactor Q r z 0).eval 0` is
`(ftDen Q r z).coeff 1`, and by `ftDen_coeff_one_of_two_le` that is `Q.coeff 1` for every
`z` once `2 ≤ r`: the endpoint value of the amplitude does not depend on `z` at all, so no
endpoint value for it changes anything.  Nor can it sit on the radius — a nonzero endpoint
radius evaluates the amplitude at a different point rather than at its limit.  What is left
is correcting the amplitude *along the arc* by an endpoint value, and that changes the
conclusion rather than a hypothesis: `AngularDiscrepancyFT.FTPhaseSupply`'s branch clause is
written with the raw `ftAmp`, and that is the seam.

**What `hWL` is used for is narrower than what it says.**  In `exists_ftBranchSupply` it
appears twice — passed to `ArcPhaseBound.exists_phase_family_of_regions_of_open`, and in the
step showing a nondegenerate block lies in the open arc — and that theorem's own docstring
says the same of its copy: `hW0` and `hWL` "push every admissible block into the open arc".
It is a means, not an end.  And the consumer that actually calls `hbranch` never needs the means:
`PhaseSupplyProducer` supplies blocks from `eq:retained-range`, collared to
`[h/M, π/r − h/M]`, which is strictly inside the arc for reasons having nothing to do with
the amplitude.
-/

/-- **For `2 ≤ r` the pencil's linear coefficient does not see the spectral parameter.**
`ftDen = Q + C z X^r`, and `X^r` reaches `coeff 1` only at `r = 1`.  This is what rules out
repairing `hWL` with an endpoint value for `z`. -/
theorem ftDen_coeff_one_of_two_le (Q : Polynomial ℂ) {r : ℕ} (hr : 2 ≤ r) (z : ℂ) :
    (ftDen Q r z).coeff 1 = Q.coeff 1 := by
  rw [ftDen, coeff_add, coeff_C_mul, coeff_X_pow, if_neg (by omega)]
  ring

/-! ### `hKvar` at a general pencil

The curvature bound and the supply's binder want different shapes, and the gap is a
transfer rather than an estimate.  `eVariationOn_polarAngle_tangent_ftBranch` bounds the
tangent's angle on a **compact** `Icc u v` at base `u`; `exists_uniform_ftBranchSupply`
asks on the **open** arc at an **arbitrary** base.

Both halves are cheap once seen.  The base moves by a constant — `polarAngle_base_shift`,
applied on an interval carrying *both* base points, since `c` need not lie in `[u,v]` — and
a constant is invisible to `eVariationOn`.  The compacts reach the open arc because
`eVariationOn` is a supremum over finite monotone tuples and a finite tuple lies in the
compact interval its own endpoints span: nothing happens at the open ends, so the constant
never has to be attained there.  That the tangent bound `π/r + π` is already free of `u`
and `v` is what makes the second half say anything.
-/

/-! **A variation bound on every compact subinterval is a variation bound on the set.**
`eVariationOn` is a supremum over finite monotone tuples, and a finite tuple lies in the
compact interval spanned by its own endpoints — so nothing is lost at the open ends, and
the constant does not have to be attained there. -/

export Shields (eVariationOn_le_of_forall_Icc)

/-- **`hKvar` at a general pencil, in the shape the branch supply asks for it.**
`eVariationOn_polarAngle_tangent_ftBranch` bounds the tangent's angle on a compact
`Icc u v` at base `u`; the supply wants the open arc at an arbitrary base.
`polarAngle_base_shift` moves the base — two branches differ by a constant, which
the variation cannot see — and `eVariationOn_le_of_forall_Icc` moves the compacts to the
arc, which is the definition of `eVariationOn` and needs the constant at no endpoint. -/
theorem ft_hKvar {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    ∀ c ∈ Ioo (0 : ℝ) (π / r),
      eVariationOn (polarAngle (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 c)
        (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal (π / r + π) := by
  intro c hc
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
    fun s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs
  refine eVariationOn_le_of_forall_Icc Set.ordConnected_Ioo ?_
  intro u hu v hv huv
  -- the shift needs one interval carrying both base points
  set p : ℝ := min c u with hp
  set q : ℝ := max c v with hq
  have hpq : Icc p q ⊆ Ioo (0 : ℝ) (π / r) := by
    refine Set.ordConnected_Ioo.out ?_ ?_
    · rcases min_cases c u with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hp, h] <;> assumption
    · rcases max_cases c v with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hq, h] <;> assumption
  have hcp : c ∈ Icc p q := ⟨min_le_left _ _, le_max_left _ _⟩
  have hup : u ∈ Icc p q := ⟨min_le_right _ _, le_trans huv (le_max_right _ _)⟩
  have hsubuv : Icc u v ⊆ Icc p q :=
    Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
  have hγc : ContinuousOn (ftGammaDeriv a r (n - 1)) (Icc p q) := fun s hs =>
    (continuousAt_ftGammaDeriv hn ha hr (hpq hs) hb).continuousWithinAt
  have hdc : ContinuousOn (ftGammaDeriv2 a r (n - 1)) (Icc p q) := fun s hs =>
    (continuousAt_ftGammaDeriv2 hn ha hr (hpq hs) hb).continuousWithinAt
  have hne : ∀ s ∈ Icc p q, ftGammaDeriv a r (n - 1) s ≠ (0 : ℂ) := fun s hs =>
    ftGammaDeriv_ne_zero (hb s (hpq hs))
  obtain ⟨k, hk⟩ := polarAngle_base_shift (γ := ftGammaDeriv a r (n - 1))
    (dγ := ftGammaDeriv2 a r (n - 1)) (β := 0) hγc hdc hne hcp hup
  have hcongr : eVariationOn
      (polarAngle (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 c) (Icc u v)
      = eVariationOn (fun x =>
          polarAngle (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 u x + k)
        (Icc u v) :=
    eVariationOn.congr (fun x hx => hk x (hsubuv hx))
  rw [hcongr, eVariationOn_add_const]
  exact eVariationOn_polarAngle_tangent_ftBranch hn ha hr hnr huv
    (fun x hx => hpq (hsubuv hx))

/-- **The curvature group of `exists_uniform_ftBranchSupply`, at a general pencil.**  Both
clauses it asks for, in the shape it asks for them: `Kγ = π/r + π` from
`eVariationOn_polarAngle_tangent_ftBranch`, carried to the open arc at an arbitrary
base. -/
theorem ft_curvature_group {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    (0 : ℝ) ≤ π / r + π
      ∧ ∀ c ∈ Ioo (0 : ℝ) (π / r),
        eVariationOn (polarAngle (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 c)
          (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal (π / r + π) := by
  exact ⟨by positivity, ft_hKvar hn ha hr hnr⟩

section Bridge

open Filter Topology

theorem tendsto_ftGammaDeriv_of_tendsto {n r l : ℕ} {a : Fin n → ℝ} {T D : ℝ}
    (hτ : Tendsto (ftTau a r l) (𝓝[>] (0 : ℝ)) (𝓝 T))
    (hτ1 : Tendsto (ftTauDeriv a r l) (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    Tendsto (ftGammaDeriv a r l) (𝓝[>] (0 : ℝ)) (𝓝 ((D : ℂ) + (T : ℂ) * Complex.I)) := by
  have hexp : Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : ContinuousAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) 0 := by fun_prop
    simpa using h.continuousWithinAt.tendsto
  have h1 : Tendsto (fun θ : ℝ => ((ftTau a r l θ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 ((T : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto T).comp hτ
  have h2 : Tendsto (fun θ : ℝ => ((ftTauDeriv a r l θ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 ((D : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto D).comp hτ1
  have hI : Tendsto (fun _ : ℝ => Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 Complex.I) :=
    tendsto_const_nhds
  have hfun : ftGammaDeriv a r l = fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)
      * (((ftTauDeriv a r l x : ℝ) : ℂ) + ((ftTau a r l x : ℝ) : ℂ) * Complex.I) := rfl
  rw [hfun]
  simpa using hexp.mul (h2.add (h1.mul hI))

/-- **The collar's `hlip` at a general pencil, from one hypothesis.**  Everything the
general collar still wanted collapses to `τ''` converging at the collision: the tree turns
that into limits for `τ` and `τ'` (`exists_tau_limits_of_tendsto_ftTauDeriv2`) and for `γ''`
(`tendsto_ftGammaDeriv2_of_tendsto`), a convergent `γ''` is bounded near the endpoint, and
`exists_lipschitz_of_bound_of_continuousWithinAt` asks for nothing more. -/
theorem exists_lipschitz_ftGammaDerivAt_of_tendsto_ftTauDeriv2 {n r l : ℕ} {a : Fin n → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hπr : (0 : ℝ) < π / r)
    (hbranch : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r l θ)
    {D2 : ℝ} (hτ2 : Tendsto (ftTauDeriv2 a r l) (𝓝[>] (0 : ℝ)) (𝓝 D2)) :
    ∃ (v : ℂ) (L b : ℝ), 0 < b ∧ 0 ≤ L ∧
      ∀ θ ∈ Icc (0 : ℝ) b,
        ‖ftGammaDerivAt a r l v θ - ftGammaDerivAt a r l v 0‖ ≤ L * θ := by
  obtain ⟨T, D, hT, hD⟩ :=
    exists_tau_limits_of_tendsto_ftTauDeriv2 hn ha hr hbranch hπr hτ2
  set v : ℂ := (D : ℂ) + (T : ℂ) * Complex.I with hv
  have hγ1 : Tendsto (ftGammaDeriv a r l) (𝓝[>] (0 : ℝ)) (𝓝 v) :=
    tendsto_ftGammaDeriv_of_tendsto hT hD
  have hγ2 := tendsto_ftGammaDeriv2_of_tendsto hT hD hτ2
  set w : ℂ := (D2 : ℂ) + 2 * (D : ℂ) * Complex.I - (T : ℂ) with hw
  -- a convergent `γ''` is bounded just to the right of the collision
  have hbdd : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ‖ftGammaDeriv2 a r l θ‖ ≤ ‖w‖ + 1 := by
    have h0 : Tendsto (fun θ : ℝ => ‖ftGammaDeriv2 a r l θ - w‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Tendsto (fun _ : ℝ => w) (𝓝[>] (0 : ℝ)) (𝓝 w) := tendsto_const_nhds
      simpa using (hγ2.sub hc).norm
    filter_upwards [h0.eventually (gt_mem_nhds one_pos)] with θ hθ
    calc ‖ftGammaDeriv2 a r l θ‖ ≤ ‖w‖ + ‖ftGammaDeriv2 a r l θ - w‖ := by
          simpa using norm_add_le w (ftGammaDeriv2 a r l θ - w)
      _ ≤ ‖w‖ + 1 := by linarith [hθ.le]
  obtain ⟨b₀, hb₀mem, hb₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hbdd
  have hb₀0 : (0 : ℝ) < b₀ := hb₀mem
  set b : ℝ := min b₀ (π / r) with hb
  have hb0 : (0 : ℝ) < b := lt_min hb₀0 hπr
  refine ⟨v, ‖w‖ + 1, b / 2, by linarith, by positivity, ?_⟩
  have hcont : ContinuousWithinAt (ftGammaDerivAt a r l v) (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have : Tendsto (ftGammaDerivAt a r l v) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
      refine hγ1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact (ftGammaDerivAt_of_ne a r l v (ne_of_gt hθ)).symm
    simpa [ContinuousWithinAt, ftGammaDerivAt_zero] using this
  have hd : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt (ftGammaDerivAt a r l v)
      (ftGammaDeriv2 a r l x) x := by
    intro x hx
    have hxπ : x ∈ Ioo (0 : ℝ) (π / r) :=
      ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
    refine (hasDerivAt_ftGammaDeriv hn ha hr hxπ hbranch).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hxπ] with s hs
    exact ftGammaDerivAt_of_ne a r l v (ne_of_gt hs.1)
  have hbd : ∀ x ∈ Ioo (0 : ℝ) b, ‖ftGammaDeriv2 a r l x‖ ≤ ‖w‖ + 1 := fun x hx =>
    hb₀ ⟨hx.1, le_trans hx.2.le (min_le_left _ _)⟩
  intro θ hθ
  exact exists_lipschitz_of_bound_of_continuousWithinAt hcont hd hbd θ
    ⟨hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩

end Bridge

/-! ### `κ₀` past a collision: splitting `E` at the endpoint it degenerates at

`abs_im_logDeriv_ftCofactorAlong_le_of_bounds` covers every region where `E(γ)` stays away
from zero — the middle and, at `2 ≤ r`, the origin endpoint, where the branch runs into `0`
and `E(0) = -rQ(0) ≠ 0`.  It cannot cover the endpoint where the principal pair collides,
because there `E(γ(θ)) → 0` and `‖E'(γ)‖/‖E(γ)‖` has no bound.

What is bounded there is the combination.  Writing `E = (X - β)^ν Ẽ` with `Ẽ(β) ≠ 0`
(`ftCritical_eq_pow_mul_ftCriticalReduced`) gives, wherever `γ ≠ β` and `Ẽ(γ) ≠ 0`,

    logDeriv (E ∘ γ) = ν · γ'/(γ - β) + γ' · Ẽ'(γ)/Ẽ(γ),

and each term is bounded on a collar for its own reason: the first by
`ArcPhaseBound.exists_bound_im_chord_at_collision`, which is where the branch's Lipschitz
data enters, and the second by continuity, since `Ẽ` does not vanish at `β`.
-/

/-- **The logarithmic derivative of `E` along the arc, split at a collision.**  Pointwise
and exact; the collar estimates are what bound the two pieces. -/
theorem logDeriv_ftCriticalAlong_split {Q : Polynomial ℂ} {r : ℕ} {τ : ℝ → ℝ} {θ θ₀ : ℝ}
    {dγ : ℂ} (hγ : HasDerivAt (ftPrincipal τ) dγ θ)
    (hne : ftPrincipal τ θ ≠ ftPrincipal τ θ₀)
    (hEne : ftCriticalAlong Q r τ θ ≠ 0) :
    logDeriv (ftCriticalAlong Q r τ) θ
      = (ftCollisionOrder Q r τ θ₀ : ℂ) * (dγ / (ftPrincipal τ θ - ftPrincipal τ θ₀))
        + dγ * (derivative (ftCriticalReduced Q r τ θ₀)).eval (ftPrincipal τ θ)
            / (ftCriticalReduced Q r τ θ₀).eval (ftPrincipal τ θ) := by
  classical
  set β := ftPrincipal τ θ₀ with hβ
  set ν := ftCollisionOrder Q r τ θ₀ with hν
  set H := ftCriticalReduced Q r τ θ₀ with hH
  set g : ℂ := ftPrincipal τ θ - β with hgdef
  have hg : g ≠ 0 := sub_ne_zero.2 hne
  have hfac : ftCritical Q r = (X - C β) ^ ν * H :=
    ftCritical_eq_pow_mul_ftCriticalReduced Q r τ θ₀
  -- `E(γ) = g^ν · H(γ)`, and `E'(γ) = ν g^(ν-1) H(γ) + g^ν H'(γ)`
  have hEev : ftCriticalAlong Q r τ θ = g ^ ν * H.eval (ftPrincipal τ θ) := by
    rw [ftCriticalAlong, hfac]
    simp [hgdef]
  have hEd : (derivative (ftCritical Q r)).eval (ftPrincipal τ θ)
      = (ν : ℂ) * g ^ (ν - 1) * H.eval (ftPrincipal τ θ)
        + g ^ ν * (derivative H).eval (ftPrincipal τ θ) := by
    rw [hfac, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C]
    simp [hgdef]
  have hHne : H.eval (ftPrincipal τ θ) ≠ 0 := by
    intro h
    exact hEne (by rw [hEev, h, mul_zero])
  rw [logDeriv, Pi.div_apply, (hasDerivAt_ftCriticalAlong (Q := Q) (r := r) hγ).deriv,
    hEd, hEev]
  have hHev : H.eval (ftPrincipal τ θ) ≠ 0 := hHne
  rcases Nat.eq_zero_or_pos ν with hν0 | hν0
  · rw [hν0]
    simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul]
    field
  · obtain ⟨m, hm⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

/-- **The reduced factor's logarithmic derivative is bounded on a collar.**  `Ẽ` does not
vanish at the collision point, so `Ẽ'/Ẽ` is continuous there and the branch carries the
bound back along the arc.  This is the second half of `logDeriv_ftCriticalAlong_split`, and
it is continuity alone -- nothing about the collision's order enters. -/
theorem exists_bound_ftCriticalReduced_ratio {Q : Polynomial ℂ} {r : ℕ} {τ : ℝ → ℝ}
    {θ₀ : ℝ} (hE : ftCritical Q r ≠ 0)
    (hγc : ContinuousWithinAt (ftPrincipal τ) (Ioi θ₀) θ₀) :
    ∃ b K : ℝ, 0 < b ∧ 0 ≤ K ∧ ∀ θ ∈ Ioo θ₀ (θ₀ + b),
      ‖(derivative (ftCriticalReduced Q r τ θ₀)).eval (ftPrincipal τ θ)‖
          / ‖(ftCriticalReduced Q r τ θ₀).eval (ftPrincipal τ θ)‖ ≤ K := by
  classical
  set H := ftCriticalReduced Q r τ θ₀ with hH
  have hH0 : H.eval (ftPrincipal τ θ₀) ≠ 0 := eval_ftCriticalReduced_ne_zero hE θ₀
  set Ψ : ℝ → ℝ := fun s =>
    ‖(derivative H).eval (ftPrincipal τ s)‖ / ‖H.eval (ftPrincipal τ s)‖ with hΨ
  have hp : ∀ P : Polynomial ℂ,
      ContinuousWithinAt (fun s : ℝ => P.eval (ftPrincipal τ s)) (Ioi θ₀) θ₀ :=
    fun P => ((Polynomial.continuous P).continuousAt).comp_continuousWithinAt hγc
  have hΨc : ContinuousWithinAt Ψ (Ioi θ₀) θ₀ :=
    (hp _).norm.div (hp H).norm (norm_ne_zero_iff.mpr hH0)
  have hK0 : 0 ≤ Ψ θ₀ + 1 := by
    have : 0 ≤ Ψ θ₀ := by rw [hΨ]; positivity
    linarith
  have hev : ∀ᶠ s in nhdsWithin θ₀ (Ioi θ₀), Ψ s ≤ Ψ θ₀ + 1 := by
    filter_upwards [hΨc.eventually (eventually_lt_nhds (by linarith : Ψ θ₀ < Ψ θ₀ + 1))]
      with s hs using hs.le
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have huθ : θ₀ < u := hu
  refine ⟨u - θ₀, Ψ θ₀ + 1, by linarith, hK0, fun θ hθ => ?_⟩
  exact hsub ⟨hθ.1, by linarith [hθ.2]⟩

/-- **`κ₀`'s collar at the collision, joined.**  The two halves of
`logDeriv_ftCriticalAlong_split` meet here: the chord through
`ArcPhaseBound.exists_bound_im_chord_at_collision`, which is where the branch's Lipschitz
data enters, and the reduced factor through `exists_bound_ftCriticalReduced_ratio`, which
is continuity.  `abs_im_logDeriv_ftCofactorAlong_le` then pays the `+1` for the `1/γ` of
`∂_tD = E(γ)/γ`.

The collar is returned rather than taken, and that is what lets the region assembly reuse
these cut points instead of choosing its own. -/
theorem exists_bound_im_logDeriv_ftCofactorAlong_at_collision {Q : Polynomial ℂ} {r : ℕ}
    {z τ : ℝ → ℝ} {dγ dS : ℝ → ℂ} {dτ : ℝ → ℝ} {b L : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) (hL : 0 ≤ L)
    (hd0 : HasDerivWithinAt (ftPrincipal τ) (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt (ftPrincipal τ) (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0)
    (hτd : ∀ θ ∈ Ioo (0 : ℝ) b, HasDerivAt τ (dτ θ) θ)
    (hSd : ∀ θ ∈ Ioo (0 : ℝ) b, HasDerivAt (ftCofactorAlong Q r z τ) (dS θ) θ)
    (hstate : ∀ θ ∈ Ioo (0 : ℝ) b, ftPrincipal τ θ ≠ 0
      ∧ (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0
      ∧ ftCriticalAlong Q r τ θ ≠ 0)
    (hsep : ∀ θ ∈ Ioo (0 : ℝ) b, ftPrincipal τ θ ≠ ftPrincipal τ 0)
    (hγc : ContinuousWithinAt (ftPrincipal τ) (Ioi (0 : ℝ)) 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧ ∀ θ ∈ Ioo (0 : ℝ) b',
      |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ κ := by
  classical
  have hE : ftCritical Q r ≠ 0 := by
    intro h
    obtain ⟨θ, hθ⟩ : ∃ θ, θ ∈ Ioo (0 : ℝ) b := ⟨b / 2, by constructor <;> linarith⟩
    exact (hstate θ hθ).2.2 (by rw [ftCriticalAlong, h]; simp)
  set ν : ℕ := ftCollisionOrder Q r τ 0 with hν
  set H := ftCriticalReduced Q r τ 0 with hH
  -- the chord, from the branch's Lipschitz data
  obtain ⟨bc, hbc0, hbcb, hchord⟩ :=
    exists_bound_im_chord_at_collision (γ := ftPrincipal τ) (dγ := dγ)
      (β := ftPrincipal τ 0) hb hL rfl hd0 hd hlip h0
  -- the reduced factor, from continuity
  obtain ⟨bk, K, hbk0, hK0, hratio⟩ :=
    exists_bound_ftCriticalReduced_ratio (Q := Q) (r := r) (τ := τ) (θ₀ := 0) hE hγc
  set D : ℝ := ‖dγ 0‖ + L * b with hD
  have hD0 : 0 ≤ D := by positivity
  set κ : ℝ := (ν : ℝ) * (3 * L / ‖dγ 0‖) + D * K + 1 with hκ
  refine ⟨min bc bk, κ, lt_min hbc0 hbk0, le_trans (min_le_left _ _) hbcb, ?_, ?_⟩
  · have : 0 ≤ (ν : ℝ) * (3 * L / ‖dγ 0‖) := by positivity
    have : 0 ≤ D * K := mul_nonneg hD0 hK0
    rw [hκ]; positivity
  intro θ hθ
  have hθb : θ ∈ Ioo (0 : ℝ) b :=
    ⟨hθ.1, lt_of_lt_of_le hθ.2 (le_trans (min_le_left _ _) hbcb)⟩
  obtain ⟨hγ0, hroot, hEne⟩ := hstate θ hθb
  have hτ0 : τ θ ≠ 0 := fun h => hγ0 (by rw [ftPrincipal, h]; simp)
  have hγd := hd θ ⟨hθ.1, hθb.2.le⟩
  -- the two halves, bounded separately
  have hsplit := logDeriv_ftCriticalAlong_split (Q := Q) (r := r) (τ := τ) (θ₀ := 0)
    hγd (hsep θ hθb) hEne
  have hbdγ : ‖dγ θ‖ ≤ D := by
    have := hlip θ ⟨hθ.1.le, hθb.2.le⟩
    have h1 : ‖dγ θ‖ - ‖dγ 0‖ ≤ ‖dγ θ - dγ 0‖ := norm_sub_norm_le _ _
    have h2 : L * θ ≤ L * b := mul_le_mul_of_nonneg_left hθb.2.le hL
    rw [hD]; linarith
  have hchordθ : |(dγ θ / (ftPrincipal τ θ - ftPrincipal τ 0)).im| ≤ 3 * L / ‖dγ 0‖ :=
    hchord θ ⟨hθ.1.le, le_trans hθ.2.le (min_le_left _ _)⟩ hθ.1.ne'
  have hratioθ : ‖(derivative H).eval (ftPrincipal τ θ)‖ / ‖H.eval (ftPrincipal τ θ)‖ ≤ K :=
    hratio θ ⟨hθ.1, by simpa using lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩
  have hsecond : |(dγ θ * (derivative H).eval (ftPrincipal τ θ)
      / H.eval (ftPrincipal τ θ)).im| ≤ D * K := by
    refine le_trans (Complex.abs_im_le_norm _) ?_
    rw [norm_div, norm_mul, mul_div_assoc]
    exact mul_le_mul hbdγ hratioθ (by positivity) hD0
  have hbd : |(logDeriv (ftCriticalAlong Q r τ) θ).im|
      ≤ (ν : ℝ) * (3 * L / ‖dγ 0‖) + D * K := by
    rw [hsplit, Complex.add_im]
    refine le_trans (abs_add_le _ _) (add_le_add ?_ hsecond)
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left hchordθ (Nat.cast_nonneg _)
  have hnbhd : ∀ᶠ s in nhds θ, ftPrincipal τ s ≠ 0
      ∧ (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hθb] with s hs
    exact ⟨(hstate s hs).1, (hstate s hs).2.1⟩
  rw [hκ]
  exact abs_im_logDeriv_ftCofactorAlong_le hr hnbhd (hτd θ hθb) hτ0 hγd hEne
    (hSd θ hθb) hbd

/-! ### What the chart forms buy at the origin endpoint

`κ₀`'s collar at the origin endpoint needs `‖γ'‖` bounded there, and `γ' = e^{iθ}(τ' + iτ)`,
so the whole question is whether `ftTauDeriv` stays bounded as `θ → (π/r)⁻`.  It does, and
the implicit function theorem is not needed for it: `ftTauDeriv` is a quotient of two
explicit sums, and `AngleChartForm` already writes both summands over the squared chord —
`ftAngleDerivTau_chart` and `ftAngleDerivAngle_chart` — so what is left is an inequality
chain over `ftChordSq`, which is bounded away from `0` for `0 < τ < a`.

**Both sums are written over denominators that vanish at the endpoint** — the `τ`-partial
carries `τ² sin θ` and the `θ`-partial carries `sin θ` — and what keeps them finite is that
`sin²θ_k` vanishes at the matching rate, which is exactly what the chart forms record.  So
the endpoint value is a genuine `0/0` whose value comes from a numerator's rate, and Lean's
division convention would return an ordinary number there with nothing to signal it.  Every
statement here is carried on the punctured collar and none is evaluated at the endpoint.
-/

/-- The chord is at least the radial gap.  `cos s ≤ 1`, and nothing else. -/
theorem sq_sub_le_ftChordSq {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (s : ℝ) :
    (a - τ) ^ 2 ≤ ftChordSq a τ s := by
  have h := Real.cos_le_one s
  rw [ftChordSq]
  nlinarith [mul_pos ha hτ]

/-- And at most the radial sum.  `-1 ≤ cos s`, and nothing else. -/
theorem ftChordSq_le_sq_add {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (s : ℝ) :
    ftChordSq a τ s ≤ (a + τ) ^ 2 := by
  have h := Real.neg_one_le_cos s
  rw [ftChordSq]
  nlinarith [mul_pos ha hτ]

/-- **The `τ`-partial is bounded away from zero once the branch point is well inside the
smallest zero.**  Each summand is `-a_k sin s / D_k` with `D_k ≤ (2a_k)²`, so the sum is at
most `-(sin s/4) Σ 1/a_k`.  This is the denominator of `ftTauDeriv`, and it is what keeps
that quotient bounded where the naive reading of `ftAngleSumDerivTau` — a `sin²θ_k` over a
vanishing `τ² sin s` — suggests it could not be. -/
theorem ftAngleSumDerivTau_le_neg {n : ℕ} {a : Fin n → ℝ} {τ s : ℝ}
    (ha : ∀ k, 0 < a k) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) (hsmall : ∀ k, τ ≤ a k) :
    ftAngleSumDerivTau a τ s ≤ -(Real.sin s / 4 * ∑ k, 1 / a k) := by
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hterm : ∀ k : Fin n,
      -(Real.sin (ftAngle (a k) τ s) ^ 2 * a k / (τ ^ 2 * Real.sin s))
        ≤ -(Real.sin s / 4 * (1 / a k)) := by
    intro k
    have hak := ha k
    have hD : 0 < ftChordSq (a k) τ s := ftChordSq_pos hak hτ hs
    have hD4 : ftChordSq (a k) τ s ≤ 4 * a k ^ 2 := by
      have h := ftChordSq_le_sq_add hak hτ s
      nlinarith [hsmall k, hak]
    rw [ftAngleDerivTau_chart hak hτ hs, neg_div, neg_le_neg_iff, le_div_iff₀ hD]
    calc Real.sin s / 4 * (1 / a k) * ftChordSq (a k) τ s
        ≤ Real.sin s / 4 * (1 / a k) * (4 * a k ^ 2) :=
          mul_le_mul_of_nonneg_left hD4 (by positivity)
      _ = a k * Real.sin s := by field_simp
  calc ftAngleSumDerivTau a τ s
      = ∑ k, -(Real.sin (ftAngle (a k) τ s) ^ 2 * a k / (τ ^ 2 * Real.sin s)) := rfl
    _ ≤ ∑ k : Fin n, -(Real.sin s / 4 * (1 / a k)) := Finset.sum_le_sum fun k _ => hterm k
    _ = -(Real.sin s / 4 * ∑ k, 1 / a k) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]

/-- **The `θ`-partial is `O(τ)`.**  Each summand is `τ(τ - a_k cos s)/D_k` with
`|τ - a_k cos s| ≤ τ + a_k ≤ 2a_k` and `D_k ≥ (a_k - τ)²`, so the whole sum is at most
`τ` times a constant of the pencil.  It is the numerator of `ftTauDeriv` alongside `r`. -/
theorem abs_ftAngleSumDerivAngle_le {n : ℕ} {a : Fin n → ℝ} {τ s : ℝ}
    (ha : ∀ k, 0 < a k) (hτ : 0 < τ) (hs : s ∈ Ioo 0 π) (hsmall : ∀ k, 2 * τ ≤ a k) :
    |ftAngleSumDerivAngle a τ s| ≤ τ * ∑ k, 8 / a k := by
  have hterm : ∀ k : Fin n,
      |Real.sin (ftAngle (a k) τ s) * Real.cos (ftAngle (a k) τ s - s) / Real.sin s|
        ≤ τ * (8 / a k) := by
    intro k
    have hak := ha k
    have hhalf : 2 * τ ≤ a k := hsmall k
    have hD : 0 < ftChordSq (a k) τ s := ftChordSq_pos hak hτ hs
    have hDlo : (a k / 2) ^ 2 ≤ ftChordSq (a k) τ s := by
      have h := sq_sub_le_ftChordSq hak hτ s
      nlinarith [hhalf, hak]
    rw [ftAngleDerivAngle_chart hak hτ hs, abs_div, abs_of_pos hD]
    rw [div_le_iff₀ hD]
    have hnum : |τ * (τ - a k * Real.cos s)| ≤ τ * (2 * a k) := by
      rw [abs_mul, abs_of_pos hτ]
      refine mul_le_mul_of_nonneg_left ?_ hτ.le
      have h1 := Real.neg_one_le_cos s
      have h2 := Real.cos_le_one s
      rw [abs_le]
      constructor <;> nlinarith [hak, hhalf, hτ]
    calc |τ * (τ - a k * Real.cos s)| ≤ τ * (2 * a k) := hnum
      _ = τ * (8 / a k) * ((a k / 2) ^ 2) := by field
      _ ≤ τ * (8 / a k) * ftChordSq (a k) τ s :=
          mul_le_mul_of_nonneg_left hDlo (by positivity)
  calc |ftAngleSumDerivAngle a τ s|
      = |∑ k, Real.sin (ftAngle (a k) τ s) * Real.cos (ftAngle (a k) τ s - s)
          / Real.sin s| := rfl
    _ ≤ ∑ k, |Real.sin (ftAngle (a k) τ s) * Real.cos (ftAngle (a k) τ s - s)
          / Real.sin s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, τ * (8 / a k) := Finset.sum_le_sum fun k _ => hterm k
    _ = τ * ∑ k, 8 / a k := by rw [Finset.mul_sum]

/-- **`τ'` is bounded wherever the branch point is well inside the smallest zero and the
arc is off the real axis.**  `ftTauDeriv` is `-(A - r)/B` with `A` the `θ`-partial and `B`
the `τ`-partial; `|A| ≤ τ·Σ8/a_k` and `|B| ≥ (sin θ/4)·Σ1/a_k`, so the quotient is bounded
by an explicit constant of the pencil, the collar and the arc.

Both partials are written over denominators that vanish at the endpoint, so a reader of
`ftAngleSumDerivTau` alone would expect the quotient to blow up; what this records is that
the two vanishings cancel, and it does so without ever evaluating anything at the
endpoint. -/
theorem abs_ftTauDeriv_le {n r l : ℕ} {a : Fin n → ℝ} {θ c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hτ : 0 < ftTau a r l θ) (hθ : θ ∈ Ioo 0 π)
    (hsmall : ∀ k, 2 * ftTau a r l θ ≤ a k) (hc : 0 < c) (hcs : c ≤ Real.sin θ) :
    |ftTauDeriv a r l θ|
      ≤ (ftTau a r l θ * ∑ k, 8 / a k + r) / (c / 4 * ∑ k, 1 / a k) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2
    (Fin.pos_iff_nonempty.1 hn)
  have hS1 : 0 < ∑ k, 1 / a k :=
    Finset.sum_pos (fun k _ => by have := ha k; positivity) hne
  set τ := ftTau a r l θ with hτdef
  set A := ftAngleSumDerivAngle a τ θ with hA
  set B := ftAngleSumDerivTau a τ θ with hB
  have hAbd : |A| ≤ τ * ∑ k, 8 / a k :=
    abs_ftAngleSumDerivAngle_le ha hτ hθ hsmall
  have hBbd : B ≤ -(Real.sin θ / 4 * ∑ k, 1 / a k) :=
    ftAngleSumDerivTau_le_neg ha hτ hθ (fun k => le_trans (by linarith [hτ]) (hsmall k))
  have hcS : 0 < c / 4 * ∑ k, 1 / a k := by positivity
  have hBabs : c / 4 * ∑ k, 1 / a k ≤ |B| := by
    have h1 : Real.sin θ / 4 * ∑ k, 1 / a k ≤ |B| := by
      rw [abs_of_nonpos (by nlinarith [Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2])]
      linarith
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_right (by linarith) hS1.le
  have hnum : |A - r| ≤ τ * ∑ k, 8 / a k + r := by
    refine le_trans (abs_sub _ _) ?_
    have : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg (Nat.cast_nonneg r)
    rw [this]
    linarith [hAbd]
  rw [ftTauDeriv, ← hA, ← hB, abs_div, abs_neg]
  have hS8 : 0 ≤ ∑ k, 8 / a k :=
    Finset.sum_nonneg fun k _ => by have := ha k; positivity
  exact div_le_div₀ (add_nonneg (mul_nonneg hτ.le hS8) (Nat.cast_nonneg r)) hnum hcS hBabs

/-- **`‖γ'‖` bounded on the same collar**, which is what `κ₀`'s origin-endpoint region asks
for: `γ' = e^{iθ}(τ' + iτ)`, so the modulus is at most `|τ'| + τ`. -/
theorem norm_ftGammaDeriv_le {n r l : ℕ} {a : Fin n → ℝ} {θ c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hτ : 0 < ftTau a r l θ) (hθ : θ ∈ Ioo 0 π)
    (hsmall : ∀ k, 2 * ftTau a r l θ ≤ a k) (hc : 0 < c) (hcs : c ≤ Real.sin θ) :
    ‖ftGammaDeriv a r l θ‖
      ≤ (ftTau a r l θ * ∑ k, 8 / a k + r) / (c / 4 * ∑ k, 1 / a k) + ftTau a r l θ := by
  rw [ftGammaDeriv, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_ftTauDeriv_le hn ha hτ hθ hsmall hc hcs
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτ]

end ForgacsTran
