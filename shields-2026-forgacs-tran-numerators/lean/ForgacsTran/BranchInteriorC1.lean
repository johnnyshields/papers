/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchAmplitude
import ForgacsTran.FTBranchZMono
import ForgacsTran.InteriorSeparation
import ForgacsTran.FTGeometryClosure
import ForgacsTran.FTGeometryCone
import ForgacsTran.ConsequencesComposition.PhaseQuantization
import ForgacsTran.QuotientDerivBound

/-!
# Groundwork for `eq:C1-interior-remainder` at the general branch

`CubicInteriorRemainder.cubic_interior_cos_error_C1` is `eq:C1-interior-remainder`
at one pencil, and it is the only producer of the `C¹` half anywhere in the tree.
Its inputs are all closed forms of the witness — `cubicZbranchDeriv`,
`cubicTauDeriv`, `cubicAmpNormDeriv`, `cubicDenFloor`.  This module builds the
general analogue of each, so that the general assembly has the same table of
bounds to work from.

## Main statements

* `continuousAt_ftBranchZDeriv`, `exists_ftBranchZDeriv_bound` — `z'` and its
  bound on a compact subarc, from `Forgacs2017RationalDenominator` Eq. (23).
* `exists_ftTauDeriv_bound`, `exists_ftTau_bounds` — `τ'`, and `τ` between two
  positive constants.
* `exists_local_contour_data` — a contour radius, a `‖B‖` bound on the sphere,
  and a `‖D‖` floor holding on a real neighborhood of `z(θ)`, on a window around
  any angle of the arc.
* `ftBranchErr` — `eq:principal-decomposition`'s error, written down rather than
  selected.
* `exists_ft_interior_C1_on_window` — `eq:C1-interior-remainder` on a window.
* `exists_ftBranchErr_C1` — the same on a whole compact subarc.

## Implementation notes

**The radius is per-window, and that is the shape of the argument rather than a
defect.**  `interior_data_of_geometry` takes one radius for a whole interval as
*data*, and its docstring records why: Mathlib carries no continuity-of-roots
statement at the pinned revision.  What is a theorem is the radius at one angle
surviving a neighborhood — `InteriorSeparation.exists_neighborhood_separation` —
so both halves of the interior supply run on a cover.  The `C⁰` half is
`InteriorSupply.exists_interior_data_on_subinterval`; the `C¹` half is
`exists_ftBranchErr_C1`, and it glues the same way, by maxing the constants and
the ratios over a finite subcover.

**The subarc must sit strictly inside the divisor-free interval.**  The contour
identity holds on a window, so a two-sided `HasDerivAt` at a point needs the
identity on a two-sided neighborhood, which the endpoints of the divisor-free
interval do not have.  This is not an artifact: it is the manuscript's own
`𝒥 ⊂ 𝒥_0`.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Local phase
quantization and strong-clock spacing» (`subsec:strong-clock`,
`eq:C1-interior-remainder`), over `Forgacs2017RationalDenominator` Eq. (23).

## Tags

interior remainder, branch derivative, spectral parameter
-/

namespace ForgacsTran

open Real Set

section BranchZ

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {lo hi : ℝ}

/-- At `l = n - 1` the parity `Even (n + l + 1)` that `ftBranchZ_pos` asks for is
`2n`, so it costs nothing on the principal branch. -/
theorem even_add_sub_one (hn : 0 < n) : Even (n + (n - 1) + 1) := ⟨n, by omega⟩

/-- **`z > 0` on the viewing arc, on the principal branch.**  `ftBranchZ_pos` with
its parity discharged and the branch supplied. -/
theorem ftBranchZ_pos_principal (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    0 < ftBranchZ a c r (n - 1) θ :=
  ftBranchZ_pos ha hc (even_add_sub_one hn) (ftArc_subset hr hθ)
    (ftBranchAt_of_arc_principal hn ha hr hnr hθ)

/-- **`Σ` is continuous along the branch.**  `ftSigma a r t = ∑_k t/(a_k - t) + r`,
and `Im t_-(θ) < 0` keeps every denominator away from zero. -/
theorem continuousAt_ftSigma_ftBranchPoint (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ContinuousAt (fun s => ftSigma a r (ftBranchPoint a r (n - 1) s)) θ := by
  have hP : ContinuousAt (ftBranchPoint a r (n - 1)) θ :=
    (hasDerivAt_ftBranchPoint_principal hn ha hr hnr hθ).continuousAt
  have him : (ftBranchPoint a r (n - 1) θ).im < 0 :=
    ftBranchPoint_im_neg (ftArc_subset hr hθ)
      (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hne : ∀ k : Fin n, ((a k : ℂ)) - ftBranchPoint a r (n - 1) θ ≠ 0 := by
    intro k hk
    have := congrArg Complex.im hk
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im,
      neg_eq_zero] at this
    exact absurd this (ne_of_lt him)
  simp only [ftSigma]
  refine ContinuousAt.add ?_ continuousAt_const
  have : ContinuousAt (fun s => ∑ k, ftBranchPoint a r (n - 1) s
      / ((a k : ℂ) - ftBranchPoint a r (n - 1) s)) θ := by
    simpa [ContinuousAt] using tendsto_finsetSum Finset.univ
      fun k _ => (hP.div (continuousAt_const.sub hP) (hne k))
  exact this

/-- **`z'` is continuous on the viewing arc.**  Eq. (23) writes it as
`-z|Σ|²/ImΣ`, and `ImΣ < 0` is what keeps the quotient regular. -/
theorem continuousAt_ftBranchZDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ContinuousAt (ftBranchZDeriv a c r (n - 1)) θ := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
    fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs
  have hz : ContinuousAt (ftBranchZ a c r (n - 1)) θ :=
    (hasDerivAt_ftBranchZ hn ha hr hθ hb
      (ftBranchZ_pos_principal hn ha hc hr hnr hθ).ne').continuousAt
  have hS : ContinuousAt (fun s => ftSigma a r (ftBranchPoint a r (n - 1) s)) θ :=
    continuousAt_ftSigma_ftBranchPoint hn ha hr hnr hθ
  have him : (ftBranchPoint a r (n - 1) θ).im < 0 :=
    ftBranchPoint_im_neg (ftArc_subset hr hθ) (hb θ hθ)
  have hSim : (ftSigma a r (ftBranchPoint a r (n - 1) θ)).im < 0 :=
    ftSigma_im_neg hn ha him
  change ContinuousAt (fun s => ftBranchZDeriv a c r (n - 1) s) θ
  simp only [ftBranchZDeriv]
  exact ContinuousAt.div (hz.neg.mul (Complex.continuous_normSq.continuousAt.comp hS))
    (Complex.continuous_im.continuousAt.comp hS) hSim.ne

/-- **`|z'| ≤ Z` on a compact subarc**, which is the `Z` of
`PoleExpansion.norm_smul_ftContourRemDeriv_le`. -/
theorem exists_ftBranchZDeriv_bound (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (harc : Icc lo hi ⊆ Ioo 0 (π / r)) :
    ∃ Z ≥ (0 : ℝ), ∀ θ ∈ Icc lo hi, |ftBranchZDeriv a c r (n - 1) θ| ≤ Z := by
  obtain ⟨Z, hZ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := ftBranchZDeriv a c r (n - 1)) fun θ hθ =>
      (continuousAt_ftBranchZDeriv hn ha hc hr hnr (harc hθ)).continuousWithinAt
  exact ⟨max Z 0, le_max_right _ _, fun θ hθ =>
    le_trans (by simpa [Real.norm_eq_abs] using hZ θ hθ) (le_max_left _ _)⟩

/-- **`|τ'| ≤ T` on a compact subarc.** -/
theorem exists_ftTauDeriv_bound (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (harc : Icc lo hi ⊆ Ioo 0 (π / r)) :
    ∃ T ≥ (0 : ℝ), ∀ θ ∈ Icc lo hi, |ftTauDeriv a r (n - 1) θ| ≤ T := by
  obtain ⟨T, hT⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := ftTauDeriv a r (n - 1)) fun θ hθ =>
      (hasDerivAt_ftTauDeriv_principal hn ha hr hnr (harc hθ)).continuousAt.continuousWithinAt
  exact ⟨max T 0, le_max_right _ _, fun θ hθ =>
    le_trans (by simpa [Real.norm_eq_abs] using hT θ hθ) (le_max_left _ _)⟩

/-- **`τ` between two positive constants on a compact subarc**, which is the
`τ_{max}` of `norm_smul_ftContourRemDeriv_le` and the `1/2 ≤ τ` the cubic
assembly reads off its closed form. -/
theorem exists_ftTau_bounds (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hlohi : lo ≤ hi) (harc : Icc lo hi ⊆ Ioo 0 (π / r)) :
    ∃ τmin τmax : ℝ, 0 < τmin ∧ τmin ≤ τmax ∧
      (∃ θM ∈ Icc lo hi, ftTau a r (n - 1) θM = τmax) ∧
      ∀ θ ∈ Icc lo hi, τmin ≤ ftTau a r (n - 1) θ ∧ ftTau a r (n - 1) θ ≤ τmax := by
  have hcont : ContinuousOn (ftTau a r (n - 1)) (Icc lo hi) := fun θ hθ =>
    (continuousAt_ftTau_principal hn ha hr hnr (harc hθ)).continuousWithinAt
  have hne : (Icc lo hi).Nonempty := ⟨lo, le_rfl, hlohi⟩
  obtain ⟨θm, hθm, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  obtain ⟨θM, hθM, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨ftTau a r (n - 1) θm, ftTau a r (n - 1) θM,
    ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr (harc hθm)),
    le_trans (hmin hθM) le_rfl, ⟨θM, hθM, rfl⟩, fun θ hθ => ⟨hmin hθ, hmax hθ⟩⟩

end BranchZ

/-! ### The contour data on a neighborhood

`PoleExpansion.hasDerivAt_ftContourRem_comp` and
`PoleExpansion.norm_smul_ftContourRemDeriv_le` need a contour radius `R₀`, a
bound `C_Γ` on `‖B‖` over the sphere, and a floor `m` on `‖D‖` there — the last
one holding for every spectral parameter *near* `z(θ)`, not only at it.

At the general branch these come one neighborhood at a time.
`InteriorSeparation.exists_neighborhood_separation` supplies the radius and the
disk clause; the floor is then compactness on the product of the angle interval
with the sphere, and the neighborhood in `x` is the estimate
`D(t,x) - D(t,z) = (x - z)t^r`. -/

section ContourData

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}

/-- **`thm:FT-geometry`'s minimum-modulus clause at the branch, unconditionally**,
in `exists_neighborhood_separation`'s own binder shape.  The class split is the
paper's: `r = 1` needs `3 ≤ n`, `r ≥ 2` needs only `2 ≤ n`. -/
theorem ft_minModulus_at_branch_principal (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 1 ≤ r) (hcls : 3 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) :
    ∀ w : ℂ, (ftDen (ftRootPoly c a) r
        ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
      w ≠ ftPrincipal (ftTau a r (n - 1)) θ →
      w ≠ ((ftTau a r (n - 1) θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) →
      ftTau a r (n - 1) θ < ‖w‖ := by
  rcases Nat.lt_or_ge r 2 with hr1 | hr2
  · have hrone : r = 1 := by omega
    subst hrone
    have hn3 : 3 ≤ n := by rcases hcls with h | h <;> omega
    obtain ⟨za, b, -, -, hdisk⟩ := ft_geometry_at_branch_pi hn3 ha hc
    intro w hzero hwp hwm
    by_contra hcon
    push Not at hcon
    rcases hdisk θ hθ w hzero hcon with h | h
    · exact hwp h
    · exact hwm (by rw [h, conj_ftPrincipal])
  · intro w hzero hwp hwm
    exact ft_minModulus_at_branch_two_le hn2 ha hc hr2 θ hθ w hzero hwp
      (by rw [conj_ftPrincipal]; exact hwm)

/-- The pencil is a nonzero polynomial: `D(0,z) = Q(0) ≠ 0` once `r ≥ 1`. -/
theorem ftDen_ftRootPoly_ne_zero (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (w : ℂ) : ftDen (ftRootPoly c a) r w ≠ 0 := by
  intro h
  have h0 : (ftDen (ftRootPoly c a) r w).eval 0 = 0 := by rw [h, Polynomial.eval_zero]
  rw [ftDen_eval, zero_pow (by omega), mul_zero, add_zero, eval_ftRootPoly] at h0
  refine absurd h0 (mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne')
    (Finset.prod_ne_zero_iff.2 fun k _ => ?_))
  simpa using Complex.ofReal_ne_zero.2 (ha k).ne'

/-- **A floor for `‖D‖` on a sphere, uniform over a compact angle interval.**
Compactness of the product with the sphere; the hypothesis is that no zero of the
pencil sits on the sphere at any angle of the interval. -/
theorem exists_sphere_floor {Q : Polynomial ℂ} {r : ℕ} {z : ℝ → ℝ} {u v R₀ : ℝ}
    (huv : u ≤ v) (hR₀ : 0 < R₀)
    (hzc : ContinuousOn (fun θ : ℝ => ((z θ : ℝ) : ℂ)) (Icc u v))
    (hne : ∀ θ ∈ Icc u v, ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval t ≠ 0) :
    ∃ m > (0 : ℝ), ∀ θ ∈ Icc u v, ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      m ≤ ‖(ftDen Q r ((z θ : ℝ) : ℂ)).eval t‖ := by
  set S : Set (ℝ × ℂ) := Icc u v ×ˢ Metric.sphere (0 : ℂ) R₀ with hS
  have hcpt : IsCompact S := isCompact_Icc.prod (isCompact_sphere (0 : ℂ) R₀)
  have hsne : (Metric.sphere (0 : ℂ) R₀).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR₀.le
  obtain ⟨t₀, ht₀⟩ := hsne
  have hSne : S.Nonempty := ⟨(u, t₀), ⟨⟨le_rfl, huv⟩, ht₀⟩⟩
  have hcont : ContinuousOn
      (fun p : ℝ × ℂ => ‖(ftDen Q r ((z p.1 : ℝ) : ℂ)).eval p.2‖) S := by
    have h1 : ContinuousOn (fun p : ℝ × ℂ => ((z p.1 : ℝ) : ℂ)) S :=
      hzc.comp continuousOn_fst fun p hp => hp.1
    have h2 : ContinuousOn (fun p : ℝ × ℂ => p.2) S := continuousOn_snd
    simp only [ftDen_eval]
    exact (((Polynomial.continuous Q).comp_continuousOn h2).add (h1.mul (h2.pow r))).norm
  obtain ⟨p₀, hp₀, hmin⟩ := hcpt.exists_isMinOn hSne hcont
  refine ⟨‖(ftDen Q r ((z p₀.1 : ℝ) : ℂ)).eval p₀.2‖,
    norm_pos_iff.2 (hne p₀.1 hp₀.1 p₀.2 hp₀.2),
    fun θ hθ t ht => hmin (show (θ, t) ∈ S from ⟨hθ, ht⟩)⟩

/-- **The floor survives a real neighborhood of the spectral parameter.**
Moving `z` by `δ` moves `D` by at most `δR₀^r` on the sphere, so half the floor
survives half the floor's worth of motion.  This is the general form of
`CubicInteriorRemainder.cubic_den_floor_nbhd`. -/
theorem den_floor_nbhd {Q : Polynomial ℂ} {r : ℕ} {z : ℝ → ℝ} {u v R₀ m : ℝ}
    (hR₀ : 0 < R₀)
    (hm : ∀ θ ∈ Icc u v, ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      m ≤ ‖(ftDen Q r ((z θ : ℝ) : ℂ)).eval t‖) :
    ∀ θ ∈ Icc u v, ∀ x : ℝ, |x - z θ| ≤ m / (2 * R₀ ^ r) →
      ∀ t ∈ Metric.sphere (0 : ℂ) R₀, m / 2 ≤ ‖(ftDen Q r ((x : ℝ) : ℂ)).eval t‖ := by
  intro θ hθ x hx t ht
  have htn : ‖t‖ = R₀ := by simpa using Metric.mem_sphere.1 ht
  have hdiff : (ftDen Q r ((x : ℝ) : ℂ)).eval t
      = (ftDen Q r ((z θ : ℝ) : ℂ)).eval t + ((x - z θ : ℝ) : ℂ) * t ^ r := by
    simp only [ftDen_eval]
    push_cast
    ring
  have hsmall : ‖((x - z θ : ℝ) : ℂ) * t ^ r‖ ≤ m / 2 := by
    rw [norm_mul, norm_pow, htn, Complex.norm_real, Real.norm_eq_abs]
    calc |x - z θ| * R₀ ^ r ≤ m / (2 * R₀ ^ r) * R₀ ^ r :=
          mul_le_mul_of_nonneg_right hx (by positivity)
      _ = m / 2 := by field_simp
  have hlow := norm_sub_norm_le ((ftDen Q r ((z θ : ℝ) : ℂ)).eval t)
    (-(((x - z θ : ℝ) : ℂ) * t ^ r))
  rw [sub_neg_eq_add, norm_neg] at hlow
  have := hm θ hθ t ht
  rw [hdiff]
  linarith

/-- **`‖B‖` is bounded on the contour.** -/
theorem exists_sphere_bound (B : Polynomial ℂ) (R₀ : ℝ) :
    ∃ CB ≥ (0 : ℝ), ∀ t ∈ Metric.sphere (0 : ℂ) R₀, ‖B.eval t‖ ≤ CB := by
  obtain ⟨CB, hCB⟩ := (isCompact_sphere (0 : ℂ) R₀).exists_bound_of_continuousOn
    ((Polynomial.continuous B).continuousOn.norm)
  exact ⟨max CB 0, le_max_right _ _, fun t ht =>
    le_trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hCB t ht)
      (le_max_left _ _)⟩

/-- **The contour data on a neighborhood of one angle, unconditionally.**
Everything `PoleExpansion`'s two `C¹` lemmas ask for, at the general admissible
pencil, with the admissible class as the only binders.

The neighborhood is where it has to be: `interior_data_of_geometry` takes one
radius for a whole interval as *data*, because Mathlib carries no
continuity-of-roots statement at the pinned revision.  What is a theorem is the
radius at one angle surviving a neighborhood, which is
`InteriorSeparation.exists_neighborhood_separation`, and that is what this
returns.  A compact subarc is then covered by finitely many of these. -/
theorem exists_local_contour_data (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hcls : 3 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (B : Polynomial ℂ) :
    ∃ R₀ m CB w : ℝ, 0 < R₀ ∧ 0 < m ∧ 0 ≤ CB ∧ 0 < w ∧
      Icc (θ₀ - w) (θ₀ + w) ⊆ Ioo 0 (π / r) ∧
      (∀ θ ∈ Icc (θ₀ - w) (θ₀ + w), ftTau a r (n - 1) θ < R₀) ∧
      (∀ t ∈ Metric.sphere (0 : ℂ) R₀, ‖B.eval t‖ ≤ CB) ∧
      (∀ θ ∈ Icc (θ₀ - w) (θ₀ + w), ∀ x : ℝ,
        |x - ftBranchZ a c r (n - 1) θ| ≤ m / (2 * R₀ ^ r) →
        ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
          m / 2 ≤ ‖(ftDen (ftRootPoly c a) r ((x : ℝ) : ℂ)).eval t‖) ∧
      (∀ θ ∈ Icc (θ₀ - w) (θ₀ + w), ∀ t : ℂ, ‖t‖ ≤ R₀ →
        (ftDen (ftRootPoly c a) r
            ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal (ftTau a r (n - 1)) θ
            ∨ t = ((ftTau a r (n - 1) θ : ℝ) : ℂ)
                * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨hroot, hτpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  obtain ⟨-, -, -, hzcont⟩ := ft_branch_supplies (a := a) (c := c) hn ha hc hr hnr
  have hQ0 : ∀ w : ℂ, ftDen (ftRootPoly c a) r w ≠ 0 :=
    fun w => ftDen_ftRootPoly_ne_zero ha hc hr w
  have hrootm : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
        (((ftTau a r (n - 1) θ : ℝ) : ℂ)
          * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) = 0 := by
    intro θ hθ
    have h := ftPrincipal_conj_eval_eq_zero (hasRealCoeffs_ftRootPoly c a) (hroot θ hθ)
    rwa [conj_ftPrincipal] at h
  have hnepair : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftPrincipal (ftTau a r (n - 1)) θ ≠ ((ftTau a r (n - 1) θ : ℝ) : ℂ)
        * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) :=
    fun θ hθ => ftPrincipal_ne_arcPoint_of_pos (hτpos θ hθ) (ftArc_subset hr hθ)
  -- the separating radius at `θ₀`, surviving a neighborhood
  obtain ⟨ρ, hρ, hev⟩ := exists_neighborhood_separation
    (Q := ftRootPoly c a) (r := r) (z := ftBranchZ a c r (n - 1))
    (τ := ftTau a r (n - 1)) (θ₀ := θ₀)
    (Complex.continuous_ofReal.continuousAt.comp
      (hzcont.continuousAt (isOpen_Ioo.mem_nhds hθ₀)))
    (continuousAt_ftTau_principal hn ha hr hnr hθ₀) (hQ0 _) (hτpos θ₀ hθ₀)
    (hroot θ₀ hθ₀) (ft_principal_simple_at_branch hn ha hc.ne' hr hnr hθ₀).1
    (by
      have h := (ft_principal_simple_at_branch hn ha hc.ne' hr hnr hθ₀).2
      rwa [conj_ftPrincipal] at h)
    (hnepair θ₀ hθ₀) (hrootm θ₀ hθ₀)
    (ft_minModulus_at_branch_principal hn2 ha hc hr hcls hθ₀)
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.1 hev
  -- a closed window inside both the neighborhood and the arc
  set w : ℝ := min (d / 2) (min θ₀ (π / r - θ₀) / 2) with hw
  have hθ₀r : θ₀ < π / r := hθ₀.2
  have hwpos : 0 < w := by
    refine lt_min (by linarith) ?_
    have : 0 < min θ₀ (π / r - θ₀) := lt_min hθ₀.1 (by linarith)
    linarith
  have hwd : w ≤ d / 2 := min_le_left _ _
  have hwθ : w ≤ min θ₀ (π / r - θ₀) / 2 := min_le_right _ _
  have hsub : Icc (θ₀ - w) (θ₀ + w) ⊆ Ioo 0 (π / r) := by
    intro θ hθ
    have h1 : min θ₀ (π / r - θ₀) ≤ θ₀ := min_le_left _ _
    have h2 : min θ₀ (π / r - θ₀) ≤ π / r - θ₀ := min_le_right _ _
    constructor
    · have := hθ.1; linarith [hwθ, h1]
    · have := hθ.2; linarith [hwθ, h2]
  have hnear : ∀ θ ∈ Icc (θ₀ - w) (θ₀ + w), dist θ θ₀ < d := by
    intro θ hθ
    rw [Real.dist_eq, abs_lt]
    constructor <;> [linarith [hθ.1, hwd]; linarith [hθ.2, hwd]]
  have hprop : ∀ θ ∈ Icc (θ₀ - w) (θ₀ + w),
      ftTau a r (n - 1) θ < ρ ∧
      ∀ t : ℂ, ‖t‖ ≤ ρ →
        (ftDen (ftRootPoly c a) r
            ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal (ftTau a r (n - 1)) θ
            ∨ t = ((ftTau a r (n - 1) θ : ℝ) : ℂ)
                * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
    intro θ hθ
    obtain ⟨hτρ, hsep⟩ := hball (hnear θ hθ)
    exact ⟨hτρ, hsep (hQ0 _) (hroot θ (hsub hθ)) (hrootm θ (hsub hθ))
      (hτpos θ (hsub hθ)) (hnepair θ (hsub hθ))⟩
  -- no zero on the sphere: both members of the pair sit strictly inside
  have hnosphere : ∀ θ ∈ Icc (θ₀ - w) (θ₀ + w), ∀ t ∈ Metric.sphere (0 : ℂ) ρ,
      (ftDen (ftRootPoly c a) r
        ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t ≠ 0 := by
    intro θ hθ t ht hzero
    have htn : ‖t‖ = ρ := by simpa using Metric.mem_sphere.1 ht
    obtain ⟨hτρ, hsep⟩ := hprop θ hθ
    have hnp : ‖ftPrincipal (ftTau a r (n - 1)) θ‖ = ftTau a r (n - 1) θ :=
      norm_ftPrincipal_eq (hτpos θ (hsub hθ))
    rcases hsep t htn.le hzero with h | h
    · rw [h, hnp] at htn; linarith
    · rw [h, ← conj_ftPrincipal, RCLike.norm_conj, hnp] at htn; linarith
  obtain ⟨m, hm, hmfloor⟩ := exists_sphere_floor (Q := ftRootPoly c a) (r := r)
    (z := ftBranchZ a c r (n - 1)) (by linarith) hρ
    (fun θ hθ => (Complex.continuous_ofReal.continuousAt.comp
      (hzcont.continuousAt (isOpen_Ioo.mem_nhds (hsub hθ)))).continuousWithinAt)
    hnosphere
  obtain ⟨CB, hCB0, hCB⟩ := exists_sphere_bound B ρ
  exact ⟨ρ, m, CB, w, hρ, hm, hCB0, hwpos, hsub, fun θ hθ => (hprop θ hθ).1, hCB,
    den_floor_nbhd hρ hmfloor, fun θ hθ => (hprop θ hθ).2⟩

end ContourData

/-! ### The four arithmetic steps, over bare reals

Each in a scope of three or four hypotheses rather than of twenty — the same
split `CubicInteriorRemainder` makes, and for the same measured reason: assembled
inline they produced `nlinarith` heartbeat timeouts that read as separate
defects and were all the one scope.  These are the general forms; the cubic's
are `private` and specialized to `1/2 ≤ τ`. -/

section Arithmetic

theorem norm_cast_pow_real_mul' {N k : ℕ} {t d : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖((N : ℂ)) * ((t : ℝ) : ℂ) ^ k * ((d : ℝ) : ℂ) * w‖ = (N : ℝ) * t ^ k * |d| * ‖w‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Complex.norm_natCast]

theorem norm_pow_real_mul_smul' {k : ℕ} {t z' : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖((t : ℝ) : ℂ) ^ k * (z' • w)‖ = t ^ k * (|z'| * ‖w‖) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    norm_smul, Real.norm_eq_abs]

/-- Dropping one power of a factor bounded below by `τmin > 0` costs a factor
`1/τmin`.  `CubicInteriorRemainder` reads `1/2` off a closed form; in general the
floor is whatever compactness returns. -/
theorem pow_mul_le_of_floor {k : ℕ} {t v cst tmin : ℝ} (htmin : 0 < tmin)
    (ht : tmin ≤ t) (hv : 0 ≤ v) (h : t ^ (k + 1) * v ≤ cst) :
    t ^ k * v ≤ cst / tmin := by
  have ht0 : 0 < t := lt_of_lt_of_le htmin ht
  have hpk : (0 : ℝ) ≤ t ^ k := pow_nonneg ht0.le k
  have hexp : t ^ (k + 1) * v = t * (t ^ k * v) := by ring
  rw [hexp] at h
  rw [le_div_iff₀ htmin]
  nlinarith [mul_nonneg hpk hv]

theorem add_le_scaled' {mm x y s p q : ℝ} (hm : 1 ≤ mm) (hs : 0 ≤ s)
    (hq : 0 ≤ q) (hx : x ≤ mm * s * p) (hy : y ≤ s * q) :
    x + y ≤ mm * s * (p + q) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hm) (mul_nonneg hs hq)]

end Arithmetic

/-! ### The error function, and its `C¹` bound on a window

`ftBranchErr` is `eq:principal-decomposition`'s error, written down rather than
selected: the decomposition clause pins it to `LHS - cos Φ_M`, so there is
exactly one candidate at every angle.  Defining it globally is what makes the
covering argument possible — the local contour formula changes from window to
window with the radius, and this does not. -/

section Error

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}

/-- `eq:principal-decomposition`'s error at the general branch. -/
noncomputable def ftBranchErr (c : ℝ) (B : Polynomial ℂ) {n : ℕ} (a : Fin n → ℝ)
    (r l : ℕ) (base : ℝ) (M : ℕ) (θ : ℝ) : ℝ :=
  ((((ftTau a r l θ : ℝ) : ℂ)) ^ (M + 1)
        * (ftCoeffPoly (ftRootPoly c a) B r M).eval
            ((ftBranchZ a c r l θ : ℝ) : ℂ)).re
      / (2 * ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r l) (ftTau a r l) θ)
    - Real.cos (((M : ℝ) + 1) * θ
        - ftBranchPhase (ftRootPoly c a) B a r l base θ)

/-- The decomposition clause holds by construction. -/
theorem ftBranchErr_spec (c : ℝ) (B : Polynomial ℂ) {n : ℕ} (a : Fin n → ℝ)
    (r l : ℕ) (base : ℝ) (M : ℕ) (θ : ℝ) :
    ((((ftTau a r l θ : ℝ) : ℂ)) ^ (M + 1)
          * (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r l θ : ℝ) : ℂ)).re
        / (2 * ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r l) (ftTau a r l) θ)
      = Real.cos (((M : ℝ) + 1) * θ
          - ftBranchPhase (ftRootPoly c a) B a r l base θ)
        + ftBranchErr c B a r l base M θ := by
  rw [ftBranchErr]; ring

/-- **The five pole facts at one angle of the branch, at a radius the pair alone
lives inside.**  `cubic_pole_data` in general form. -/
theorem ft_pole_data (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) {R₀ : ℝ}
    (hpair : ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t = 0 →
        t = ftPrincipal (ftTau a r (n - 1)) θ
          ∨ t = ((ftTau a r (n - 1) θ : ℝ) : ℂ)
              * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) :
    (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
        (ftPrincipal (ftTau a r (n - 1)) θ) = 0
      ∧ (Polynomial.derivative (ftDen (ftRootPoly c a) r
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))).eval
          (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0
      ∧ (Polynomial.derivative (ftDen (ftRootPoly c a) r
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))).eval
          (((ftTau a r (n - 1) θ : ℝ) : ℂ)
            * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) ≠ 0
      ∧ ftPrincipal (ftTau a r (n - 1)) θ ≠ ((ftTau a r (n - 1) θ : ℝ) : ℂ)
          * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)
      ∧ ∀ t : ℂ, ‖t‖ ≤ R₀ →
          (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t = 0 →
            t = ftPrincipal (ftTau a r (n - 1)) θ
              ∨ t = ((ftTau a r (n - 1) θ : ℝ) : ℂ)
                  * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨hroot, hτpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  refine ⟨hroot θ hθ, (ft_principal_simple_at_branch hn ha hc.ne' hr hnr hθ).1, ?_,
    ftPrincipal_ne_arcPoint_of_pos (hτpos θ hθ) (ftArc_subset hr hθ), hpair⟩
  have h := (ft_principal_simple_at_branch hn ha hc.ne' hr hnr hθ).2
  rwa [conj_ftPrincipal] at h

end Error

/-! ### `eq:C1-interior-remainder` on a window, at the general branch

The core of the `C¹` half.  Every constant is produced from the pencil and the
window rather than assumed, and the `(M+1)` comes from the `τ^{M+1}` prefactor
and from nowhere else: differentiating in the spectral parameter never touches
`t^{-M-1}`, so `ftContourRemDeriv` carries the same `R₀^{-M}` as the value.

Stated about the **contour quotient** with its radius existentially bound, and
paired with the decomposition clause that identifies it with `ftBranchErr` on the
window.  The radius is per-window — `interior_data_of_geometry` takes one radius
for a whole interval as data, for the reason its docstring records — so a global
statement about `ftBranchErr` alone cannot be reached at this stage without the
covering. -/

section LocalC1

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}

theorem exists_ft_interior_C1_on_window (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 1 ≤ r) (hcls : 3 ≤ n ∨ 2 ≤ r) (hBr : HasRealCoeffs B)
    {lo hi : ℝ} (harc : Icc lo hi ⊆ Ioo 0 (π / r))
    (hBne : ∀ θ ∈ Icc lo hi, B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc lo hi) :
    ∃ u v R₀ Cst σ : ℝ, θ₀ ∈ Ioo u v ∧ 0 < R₀ ∧ 0 ≤ Cst ∧ 0 < σ ∧ σ < 1 ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (max u lo) (min v hi), ∃ dv : ℝ,
        HasDerivAt (fun s : ℝ =>
            ((((ftTau a r (n - 1) s : ℝ) : ℂ)) ^ (M + 1)
                * ftContourRem (ftRootPoly c a) B r R₀ M
                    ((ftBranchZ a c r (n - 1) s : ℝ) : ℂ)).re
              / (2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) s‖)) dv θ ∧
        |dv| ≤ ((M : ℝ) + 1) * Cst * σ ^ M ∧
        ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
              * ftContourRem (ftRootPoly c a) B r R₀ M
                  ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re
            / (2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖)
          = ftBranchErr c B a r (n - 1) lo M θ := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hlohi : lo ≤ hi := le_trans hθ₀.1 hθ₀.2
  obtain ⟨hroot, hτpos⟩ := ft_branch_root_and_pos (a := a) (r := r) c hn ha hr hnr
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := by
    rw [eval_ftRootPoly]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne')
      (Finset.prod_ne_zero_iff.2 fun k _ => by simpa using Complex.ofReal_ne_zero.2 (ha k).ne')
  -- the contour data on a neighborhood of `θ₀`
  obtain ⟨R₀, m, CB, w₀, hR₀, hm, hCB0, hw₀, hwsub, hτR, hCB, hDb, hpair⟩ :=
    exists_local_contour_data hn2 ha hc hr hcls (harc hθ₀) B
  set u : ℝ := θ₀ - w₀ with hu
  set v : ℝ := θ₀ + w₀ with hv
  have hθ₀uv : θ₀ ∈ Ioo u v := ⟨by rw [hu]; linarith, by rw [hv]; linarith⟩
  set K : Set ℝ := Icc (max u lo) (min v hi) with hK
  have hKsubuv : K ⊆ Icc u v := fun θ hθ =>
    ⟨le_trans (le_max_left _ _) hθ.1, le_trans hθ.2 (min_le_left _ _)⟩
  have hKsublh : K ⊆ Icc lo hi := fun θ hθ =>
    ⟨le_trans (le_max_right _ _) hθ.1, le_trans hθ.2 (min_le_right _ _)⟩
  have hKarc : K ⊆ Ioo 0 (π / r) := fun θ hθ => hwsub (hKsubuv hθ)
  have hθ₀K : θ₀ ∈ K :=
    ⟨max_le hθ₀uv.1.le hθ₀.1, le_min hθ₀uv.2.le hθ₀.2⟩
  have hKlohi : max u lo ≤ min v hi := le_trans hθ₀K.1 hθ₀K.2
  -- the branch bounds on `K`
  obtain ⟨τmin, τmax, hτmin, hminmax, ⟨θM, hθM, hθMeq⟩, hτb⟩ :=
    exists_ftTau_bounds (a := a) hn ha hr hnr hKlohi hKarc
  have hτmax0 : 0 < τmax := lt_of_lt_of_le hτmin hminmax
  have hτmaxR : τmax < R₀ := by
    rw [← hθMeq]; exact hτR θM (hKsubuv hθM)
  set σ : ℝ := τmax / R₀ with hσ
  have hσ0 : 0 < σ := div_pos hτmax0 hR₀
  have hσ1 : σ < 1 := (div_lt_one hR₀).2 hτmaxR
  obtain ⟨Z, hZ0, hZ⟩ := exists_ftBranchZDeriv_bound (c := c) hn ha hc hr hnr hKarc
  obtain ⟨T, hT0, hT⟩ := exists_ftTauDeriv_bound (a := a) hn ha hr hnr hKarc
  obtain ⟨Wd, hWd0, hWd⟩ :=
    exists_ftBranchAmpDeriv_norm_bound (B := B) hn ha hc.ne' hr hnr hKarc
  -- the amplitude floor on `K`
  have hWne : ∀ θ ∈ K, ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ ≠ 0 :=
    fun θ hθ => ftBranchAmp_ne_zero hn ha hc.ne' hr hnr (hKarc hθ) (hBne θ (hKsublh hθ))
  have hWc : ContinuousOn (fun θ => ftAmp (ftRootPoly c a) B r
      ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)
      (ftPrincipal (ftTau a r (n - 1)) θ)) K := by
    refine ContinuousOn.congr (continuousOn_ftBranchAmp (B := B) hn ha hc.ne' hr hnr hKarc) ?_
    exact fun θ hθ => (ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (hKarc hθ)).symm
  obtain ⟨A, hA, hfloor⟩ := exists_amplitude_floor_on_subarc (a := max u lo) (b := min v hi)
    hWc (fun θ hθ => by
      rw [← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr (hKarc hθ)]
      exact hWne θ hθ)
  -- the two numerator constants
  set cN : ℝ := τmax * (CB / (m / 2)) with hcN
  set cN' : ℝ := cN / τmin * T + τmax * Z * CB * R₀ ^ r / (m / 2) ^ 2 with hcN'
  have hm2 : 0 < m / 2 := by linarith
  have hcN0 : 0 ≤ cN := by
    rw [hcN]; positivity
  have hcN'0 : 0 ≤ cN' := by
    rw [hcN']; positivity
  set Cst : ℝ := max (cN / (2 * A)) (cN' / (2 * A) + cN * (2 * Wd) / (4 * A ^ 2)) with hCst
  have hCst1 : cN / (2 * A) ≤ Cst := le_max_left _ _
  have hCst2 : cN' / (2 * A) + cN * (2 * Wd) / (4 * A ^ 2) ≤ Cst := le_max_right _ _
  have hCst0 : 0 ≤ Cst := le_trans (by positivity) hCst1
  -- the `C⁰` contour bound, uniform on `K`
  have hCbd : ∀ θ : ℝ, max u lo ≤ θ → θ ≤ min v hi →
      ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
        ‖B.eval t / (ftDen (ftRootPoly c a) r
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t‖ ≤ CB / (m / 2) := by
    intro θ h1 h2 t ht
    have hθK : θ ∈ K := ⟨h1, h2⟩
    have hzz : |ftBranchZ a c r (n - 1) θ - ftBranchZ a c r (n - 1) θ|
        ≤ m / (2 * R₀ ^ r) := by rw [sub_self, abs_zero]; positivity
    have hD := hDb θ (hKsubuv hθK) (ftBranchZ a c r (n - 1) θ) hzz t ht
    have hDpos : 0 < ‖(ftDen (ftRootPoly c a) r
        ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t‖ := lt_of_lt_of_le hm2 hD
    rw [norm_div, div_le_div_iff₀ hDpos hm2]
    nlinarith [hCB t ht, hD, norm_nonneg (B.eval t), hCB0]
  have hrem := interior_remainder_uniform (Q := ftRootPoly c a) (B := B)
    (hasRealCoeffs_ftRootPoly c a) hBr hr hQ0
    (z := ftBranchZ a c r (n - 1)) (τ := ftTau a r (n - 1))
    (R₀ := R₀) (τmax := τmax) (C := CB / (m / 2)) (σ := σ)
    (lo := max u lo) (hi := min v hi) hR₀ le_rfl (by positivity)
    (fun θ h1 h2 => hτpos θ (hKarc ⟨h1, h2⟩))
    (fun θ h1 h2 => (hτb θ ⟨h1, h2⟩).2)
    (fun θ h1 h2 => hτR θ (hKsubuv ⟨h1, h2⟩))
    (fun θ h1 h2 => hroot θ (hKarc ⟨h1, h2⟩))
    (fun θ h1 h2 => (ft_pole_data hn2 ha hc hr (hKarc ⟨h1, h2⟩)
      (hpair θ (hKsubuv ⟨h1, h2⟩))).2.1)
    (fun θ h1 h2 => (ft_pole_data hn2 ha hc hr (hKarc ⟨h1, h2⟩)
      (hpair θ (hKsubuv ⟨h1, h2⟩))).2.2.1)
    (fun θ h1 h2 => (ft_pole_data hn2 ha hc hr (hKarc ⟨h1, h2⟩)
      (hpair θ (hKsubuv ⟨h1, h2⟩))).2.2.2.1)
    (fun θ h1 h2 => hpair θ (hKsubuv ⟨h1, h2⟩)) hCbd
  refine ⟨u, v, R₀, Cst, σ, hθ₀uv, hR₀, hCst0, hσ0, hσ1, fun M θ hθ => ?_⟩
  have hθK : θ ∈ K := hθ
  have hθarc : θ ∈ Ioo (0 : ℝ) (π / r) := hKarc hθK
  have hb' : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
    fun _s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs
  have hτ0 : 0 < ftTau a r (n - 1) θ := hτpos θ hθarc
  have hτlo := (hτb θ hθK).1
  have hτhi := (hτb θ hθK).2
  have hτRθ : ftTau a r (n - 1) θ < R₀ := hτR θ (hKsubuv hθK)
  obtain ⟨hrt, hsp, hsm, hnep, hpr⟩ :=
    ft_pole_data hn2 ha hc hr hθarc (hpair θ (hKsubuv hθK))
  have hAle : A ≤ ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖ := by
    have h := hfloor θ hθK
    rwa [ftPrincipalAmp, ← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr hθarc] at h
  have hWpos : 0 < ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖ := lt_of_lt_of_le hA hAle
  have h2W : (0 : ℝ) < 2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖ := by linarith
  have hA2 : 2 * A ≤ 2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖ := by linarith
  have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hσn : (0 : ℝ) ≤ σ ^ M := by positivity
  -- the value bound on the contour remainder
  have heqc := ftRemainder_eq_contour (Q := ftRootPoly c a) (B := B)
    (hasRealCoeffs_ftRootPoly c a) hBr hr hQ0
    (z := ftBranchZ a c r (n - 1)) (τ := ftTau a r (n - 1))
    hτ0 hR₀ hτRθ hrt hsp hsm hnep hpr M
  have hb : ftTau a r (n - 1) θ ^ (M + 1)
      * ‖ftContourRem (ftRootPoly c a) B r R₀ M
          ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖ ≤ cN * σ ^ M := by
    have h := hrem M θ hθK.1 hθK.2
    rw [heqc, abs_of_nonneg (mul_nonneg (pow_nonneg hτ0.le _) (norm_nonneg _))] at h
    rw [hcN]; exact h
  -- the contour derivative bound
  have hDbθ := hDb θ (hKsubuv hθK)
  have hCRd : ‖ftContourRemDeriv (ftRootPoly c a) B r R₀ M
      ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖
      ≤ CB * R₀ ^ r / ((m / 2) ^ 2 * R₀ ^ M) :=
    norm_ftContourRemDeriv_le hR₀ hm2 hCB
      (hDbθ (ftBranchZ a c r (n - 1) θ) (by rw [sub_self, abs_zero]; positivity))
  have hCR := hasDerivAt_ftContourRem_comp (Q := ftRootPoly c a) (B := B) (r := r)
    (M := M) (R := R₀) (CB := CB) (m := m / 2) (ε := m / (2 * R₀ ^ r))
    (z := ftBranchZ a c r (n - 1)) hR₀ hm2 (by positivity) hCB hDbθ
    (hasDerivAt_ftBranchZ hn ha hr hθarc hb'
      (ftBranchZ_pos_principal hn ha hc hr hnr hθarc).ne')
  have hpow := ((hasDerivAt_ftTau hn ha hr hθarc hb').ofReal_comp).pow (M + 1)
  have hDden : HasDerivAt (fun s => 2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) s‖)
      (2 * ftBranchAmpNormDeriv (ftRootPoly c a) B a r (n - 1) θ) θ :=
    (hasDerivAt_ftBranchAmpNorm hn ha hc.ne' hr hnr hθarc (hBne θ (hKsublh hθK))).const_mul 2
  have hquot := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hpow.mul hCR)).div hDden h2W.ne'
  refine ⟨_, hquot, ?_, ?_⟩
  · -- the derivative bound
    have hNs : |((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
        * ftContourRem (ftRootPoly c a) B r R₀ M
            ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re|
        ≤ ((M : ℝ) + 1) * σ ^ M * cN := by
      have hn0 : |((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
          * ftContourRem (ftRootPoly c a) B r R₀ M
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re| ≤ cN * σ ^ M := by
        refine le_trans (Complex.abs_re_le_norm _) ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]
        exact hb
      nlinarith [hn0, mul_nonneg (mul_nonneg (sub_nonneg.2 hM1) hσn) hcN0]
    have hN's : |(((M + 1 : ℕ) : ℂ) * ((ftTau a r (n - 1) θ : ℝ) : ℂ) ^ (M + 1 - 1)
          * ((ftTauDeriv a r (n - 1) θ : ℝ) : ℂ)
          * ftContourRem (ftRootPoly c a) B r R₀ M
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)
        + ((ftTau a r (n - 1) θ : ℝ) : ℂ) ^ (M + 1)
          * (ftBranchZDeriv a c r (n - 1) θ • ftContourRemDeriv (ftRootPoly c a) B r R₀ M
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))).re|
        ≤ ((M : ℝ) + 1) * σ ^ M * cN' := by
      refine le_trans (Complex.abs_re_le_norm _) (le_trans (norm_add_le _ _) ?_)
      rw [Nat.add_sub_cancel, norm_cast_pow_real_mul' hτ0, norm_pow_real_mul_smul' hτ0]
      have hpm : ftTau a r (n - 1) θ ^ M
          * ‖ftContourRem (ftRootPoly c a) B r R₀ M
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖ ≤ cN * σ ^ M / τmin :=
        pow_mul_le_of_floor hτmin hτlo (norm_nonneg _) hb
      have hsmul := norm_smul_ftContourRemDeriv_le (Q := ftRootPoly c a) (B := B)
        (r := r) (M := M) (w := ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))
        (R := R₀) (CB := CB) (m := m / 2) (τ := ftTau a r (n - 1) θ)
        (τmax := τmax) (Z := Z) (z' := ftBranchZDeriv a c r (n - 1) θ)
        hR₀ hm2 hτ0.le hτhi (hZ θ hθK) hCB
        (hDbθ (ftBranchZ a c r (n - 1) θ) (by rw [sub_self, abs_zero]; positivity))
      rw [norm_pow_real_mul_smul' hτ0] at hsmul
      have ht1 : ((M + 1 : ℕ) : ℝ) * ftTau a r (n - 1) θ ^ M
            * |ftTauDeriv a r (n - 1) θ|
            * ‖ftContourRem (ftRootPoly c a) B r R₀ M
                ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖
          ≤ ((M : ℝ) + 1) * σ ^ M * (cN / τmin * T) := by
        have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        have hnn : (0 : ℝ) ≤ ftTau a r (n - 1) θ ^ M
            * ‖ftContourRem (ftRootPoly c a) B r R₀ M
                ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖ := by positivity
        rw [hcast]
        calc ((M : ℝ) + 1) * ftTau a r (n - 1) θ ^ M * |ftTauDeriv a r (n - 1) θ|
              * ‖ftContourRem (ftRootPoly c a) B r R₀ M
                  ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖
            = ((M : ℝ) + 1) * ((ftTau a r (n - 1) θ ^ M
                * ‖ftContourRem (ftRootPoly c a) B r R₀ M
                    ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖) * |ftTauDeriv a r (n - 1) θ|) := by
              ring
          _ ≤ ((M : ℝ) + 1) * (cN * σ ^ M / τmin * T) := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              exact mul_le_mul hpm (hT θ hθK) (abs_nonneg _) (by positivity)
          _ = ((M : ℝ) + 1) * σ ^ M * (cN / τmin * T) := by ring
      have ht2 : ftTau a r (n - 1) θ ^ (M + 1)
            * (|ftBranchZDeriv a c r (n - 1) θ|
              * ‖ftContourRemDeriv (ftRootPoly c a) B r R₀ M
                  ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖)
          ≤ σ ^ M * (τmax * Z * CB * R₀ ^ r / (m / 2) ^ 2) := by
        rw [hσ]
        calc ftTau a r (n - 1) θ ^ (M + 1)
              * (|ftBranchZDeriv a c r (n - 1) θ|
                * ‖ftContourRemDeriv (ftRootPoly c a) B r R₀ M
                    ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)‖)
            ≤ (τmax * Z * CB * R₀ ^ r / (m / 2) ^ 2)
                * (ftTau a r (n - 1) θ / R₀) ^ M := hsmul
          _ ≤ (τmax * Z * CB * R₀ ^ r / (m / 2) ^ 2) * (τmax / R₀) ^ M := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact pow_le_pow_left₀ (by positivity) (by gcongr) M
          _ = (τmax / R₀) ^ M * (τmax * Z * CB * R₀ ^ r / (m / 2) ^ 2) := by ring
      rw [hcN']
      exact add_le_scaled' hM1 hσn (by positivity) ht1 ht2
    have hDb' : |2 * ftBranchAmpNormDeriv (ftRootPoly c a) B a r (n - 1) θ| ≤ 2 * Wd := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have h1 := abs_ftBranchAmpNormDeriv_le hn ha hc.ne' hr hnr hθarc
        (hBne θ (hKsublh hθK))
      have h2 := hWd θ hθK
      linarith
    refine le_trans (abs_div_deriv_le_of_scaled (A := A) (bD' := 2 * Wd) hA hA2
      (by positivity) hNs hN's hDb') ?_
    have hprod : ((M : ℝ) + 1) * σ ^ M
        * (cN' / (2 * A) + cN * (2 * Wd) / (4 * A ^ 2))
        ≤ ((M : ℝ) + 1) * σ ^ M * Cst :=
      mul_le_mul_of_nonneg_left hCst2 (by positivity)
    calc ((M : ℝ) + 1) * σ ^ M * (cN' / (2 * A) + cN * (2 * Wd) / (4 * A ^ 2))
        ≤ ((M : ℝ) + 1) * σ ^ M * Cst := hprod
      _ = ((M : ℝ) + 1) * Cst * σ ^ M := by ring
  · -- the decomposition: the quotient IS the error
    have hpa : ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
        (ftTau a r (n - 1)) θ = ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖ := by
      rw [ftPrincipalAmp, ← ftBranchAmp_eq_ftAmp (B := B) (c := c) hn ha hr hnr hθarc]
    have hpolar := ftAmp_eq_polar_at_branch (B := B) hn ha hc.ne' hr hnr hlohi harc hBne
      (hKsublh hθK)
    have hcos := principal_term_cos (M := M)
      (z := ftBranchZ a c r (n - 1)) (τ := ftTau a r (n - 1))
      (ψ := ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo) hτ0 hpolar
    have hcontour := ftCoeff_re_sub_principal_eq_contour_re (Q := ftRootPoly c a) (B := B)
      (hasRealCoeffs_ftRootPoly c a) hBr hr hQ0
      (z := ftBranchZ a c r (n - 1)) (τ := ftTau a r (n - 1))
      hτ0 hR₀ hτRθ hrt hsp hsm hnep hpr M
    rw [ftBranchErr, hpa]
    rw [hpa] at hcos
    have hne2 : (2 : ℝ) * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖ ≠ 0 := h2W.ne'
    have key : ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
          * (ftCoeffPoly (ftRootPoly c a) B r M).eval
              ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re
        = 2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖
            * Real.cos (((M : ℝ) + 1) * θ
              - ftBranchPhase (ftRootPoly c a) B a r (n - 1) lo θ)
          + ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
              * ftContourRem (ftRootPoly c a) B r R₀ M
                  ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re := by
      linarith [hcontour, hcos]
    rw [key, add_div, mul_div_cancel_left₀ _ hne2]
    ring

/-- **`eq:C1-interior-remainder` on a whole compact subarc, at the general
admissible pencil.**  The window statement glued: a derivative bound glues the
way a value bound does — max the constants, max the ratios over a finite
subcover — which is why the per-window radius of
`exists_local_contour_data` is an assembly cost and not an obstruction.

**The subarc must sit strictly inside the divisor-free interval**, and that is
forced rather than convenient: the contour identity holds on a window, so
`HasDerivAt` at a point needs the identity on a two-sided neighborhood of it,
which the endpoints of the divisor-free interval do not have.  The paper asks
for the same thing when it takes `𝒥` compactly inside `𝒥_0`. -/
theorem exists_ftBranchErr_C1 (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 1 ≤ r) (hcls : 3 ≤ n ∨ 2 ≤ r) (hBr : HasRealCoeffs B)
    {lo' hi' lo hi : ℝ} (harc : Icc lo' hi' ⊆ Ioo 0 (π / r))
    (hBne : ∀ θ ∈ Icc lo' hi', B.eval (ftPrincipal (ftTau a r (n - 1)) θ) ≠ 0)
    (hlo : lo' < lo) (hhi : hi < hi') (hlohi : lo ≤ hi) :
    ∃ C σ : ℝ, 0 ≤ C ∧ 0 < σ ∧ σ < 1 ∧
      ∀ M : ℕ, ∀ θ ∈ Icc lo hi,
        HasDerivAt (ftBranchErr c B a r (n - 1) lo' M)
            (deriv (ftBranchErr c B a r (n - 1) lo' M) θ) θ ∧
          |deriv (ftBranchErr c B a r (n - 1) lo' M) θ|
            ≤ ((M : ℝ) + 1) * C * σ ^ M := by
  classical
  have hsub : Icc lo hi ⊆ Icc lo' hi' := fun θ hθ =>
    ⟨le_trans hlo.le hθ.1, le_trans hθ.2 hhi.le⟩
  have key : ∀ θ₀ ∈ Icc lo hi, ∃ uu vv RR CC ss : ℝ,
      θ₀ ∈ Ioo uu vv ∧ 0 < RR ∧ 0 ≤ CC ∧ 0 < ss ∧ ss < 1 ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (max uu lo') (min vv hi'), ∃ dv : ℝ,
        HasDerivAt (fun s : ℝ =>
            ((((ftTau a r (n - 1) s : ℝ) : ℂ)) ^ (M + 1)
                * ftContourRem (ftRootPoly c a) B r RR M
                    ((ftBranchZ a c r (n - 1) s : ℝ) : ℂ)).re
              / (2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) s‖)) dv θ ∧
        |dv| ≤ ((M : ℝ) + 1) * CC * ss ^ M ∧
        ((((ftTau a r (n - 1) θ : ℝ) : ℂ)) ^ (M + 1)
              * ftContourRem (ftRootPoly c a) B r RR M
                  ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).re
            / (2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) θ‖)
          = ftBranchErr c B a r (n - 1) lo' M θ :=
    fun θ₀ hθ₀ => exists_ft_interior_C1_on_window hn2 ha hc hr hcls hBr harc hBne
      (hsub hθ₀)
  choose! uu vv RR CC ss hmem hRR hCC hss0 hss1 hmain using key
  set V : ℝ → Set ℝ := fun θ₀ => Ioo (max (uu θ₀) lo') (min (vv θ₀) hi') with hV
  have hcov : ∀ θ ∈ Icc lo hi, θ ∈ V θ := by
    intro θ hθ
    exact ⟨max_lt (hmem θ hθ).1 (lt_of_lt_of_le hlo hθ.1),
      lt_min (hmem θ hθ).2 (lt_of_le_of_lt hθ.2 hhi)⟩
  obtain ⟨t, htsub, htfin, htcover⟩ :=
    isCompact_Icc.elim_finite_subcover_image (b := Icc lo hi) (c := V)
      (fun θ _ => isOpen_Ioo) (fun θ hθ => Set.mem_biUnion hθ (hcov θ hθ))
  set F : Finset ℝ := htfin.toFinset with hF
  have hFmem : ∀ θ₀, θ₀ ∈ F ↔ θ₀ ∈ t := fun θ₀ => Set.Finite.mem_toFinset htfin
  have hFne : F.Nonempty := by
    obtain ⟨θ₀, hθ₀t, -⟩ := Set.mem_iUnion₂.1 (htcover ⟨le_rfl, hlohi⟩)
    exact ⟨θ₀, (hFmem θ₀).2 hθ₀t⟩
  -- the two constants are ATTAINED on the subcover, which is what makes `σ < 1`
  -- available: a supremum of finitely many reals each below one is below one, but
  -- reading that off `Finset.sup'` fights an instance mismatch on `ℝ`.
  obtain ⟨θc, hθcF, hCeq⟩ := Finset.exists_mem_eq_sup' hFne CC
  obtain ⟨θs, hθsF, hσeq⟩ := Finset.exists_mem_eq_sup' hFne ss
  have hCle : ∀ θ₀ ∈ F, CC θ₀ ≤ CC θc := fun θ₀ h => hCeq ▸ Finset.le_sup' CC h
  have hσle : ∀ θ₀ ∈ F, ss θ₀ ≤ ss θs := fun θ₀ h => hσeq ▸ Finset.le_sup' ss h
  have hC0 : 0 ≤ CC θc := hCC θc (htsub ((hFmem θc).1 hθcF))
  have hσ0 : 0 < ss θs := hss0 θs (htsub ((hFmem θs).1 hθsF))
  have hσ1 : ss θs < 1 := hss1 θs (htsub ((hFmem θs).1 hθsF))
  refine ⟨CC θc, ss θs, hC0, hσ0, hσ1, fun M θ hθ => ?_⟩
  obtain ⟨θ₀, hθ₀t, hθ₀V⟩ := Set.mem_iUnion₂.1 (htcover hθ)
  have hθ₀F : θ₀ ∈ F := (hFmem θ₀).2 hθ₀t
  have hθ₀K : θ₀ ∈ Icc lo hi := htsub hθ₀t
  have hθIcc : θ ∈ Icc (max (uu θ₀) lo') (min (vv θ₀) hi') := ⟨hθ₀V.1.le, hθ₀V.2.le⟩
  obtain ⟨dv, hdv, hbd, -⟩ := hmain θ₀ hθ₀K M θ hθIcc
  -- the contour quotient agrees with the error on the whole open window
  have hEq : Set.EqOn
      (fun s : ℝ => ((((ftTau a r (n - 1) s : ℝ) : ℂ)) ^ (M + 1)
            * ftContourRem (ftRootPoly c a) B r (RR θ₀) M
                ((ftBranchZ a c r (n - 1) s : ℝ) : ℂ)).re
          / (2 * ‖ftBranchAmp (ftRootPoly c a) B a r (n - 1) s‖))
      (ftBranchErr c B a r (n - 1) lo' M) (V θ₀) := by
    intro s hs
    exact (hmain θ₀ hθ₀K M s ⟨hs.1.le, hs.2.le⟩).choose_spec.2.2
  have hderiv : HasDerivAt (ftBranchErr c B a r (n - 1) lo' M) dv θ :=
    hdv.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
      (isOpen_Ioo.mem_nhds hθ₀V) hEq).symm
  refine ⟨hderiv.deriv ▸ hderiv, ?_⟩
  rw [hderiv.deriv]
  refine le_trans hbd ?_
  have hssn : (0 : ℝ) ≤ ss θ₀ ^ M := pow_nonneg (hss0 θ₀ hθ₀K).le M
  have hpow : ss θ₀ ^ M ≤ ss θs ^ M :=
    pow_le_pow_left₀ (hss0 θ₀ hθ₀K).le (hσle θ₀ hθ₀F) M
  have hM1 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have h1 : ((M : ℝ) + 1) * CC θ₀ * ss θ₀ ^ M
      ≤ ((M : ℝ) + 1) * CC θc * ss θ₀ ^ M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hCle θ₀ hθ₀F) hM1) hssn
  have h2 : ((M : ℝ) + 1) * CC θc * ss θ₀ ^ M
      ≤ ((M : ℝ) + 1) * CC θc * ss θs ^ M :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  linarith

end LocalC1

end ForgacsTran
