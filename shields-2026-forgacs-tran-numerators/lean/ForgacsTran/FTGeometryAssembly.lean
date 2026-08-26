/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.FTMinModulus
import ForgacsTran.FTGeometryExtraction
import ForgacsTran.DominanceFT
import ForgacsTran.FTBranchRegularity
import ForgacsTran.QuadraticCase
import ForgacsTran.FTBranchProp1

/-!
# `thm:FT-geometry`, assembled

The theorem's proof is a list of citations plus one sentence of our own, and this
module is that list turned into a composition.  What each part is:

## Main statements

* **ours, proved here** — `ft_compact_uniform_separation`, the theorem's
  "Compact-uniform separation follows by continuity of the roots, compactness,
  and the strict pointwise modulus gap".  Nothing else in the theorem is stated
  only in our paper.
* **ours, proved elsewhere** — `FTGeometryExtraction.ft_endpoint_fixed_gap_of_pointwise`
  and `FTMinModulus.exists_endpoint_linear_gap_of_expansion`, the two endpoint
  extractions.
* **derived here from the cited inputs** — that `z` maps the viewing arc *onto*
  the Forgács--Tran interval, in both the finite and the unbounded endpoint
  convention of `eq:ab-def`; that the conjugate `t_-` of `eq:principal-pair` is a
  denominator zero whenever `t_+` is; and that the principal pair exhausts the
  closed disk `|t| ≤ τ(θ)`.
* **cited, and carried as named hypotheses** — everything attributed to
  `Forgacs2017RationalDenominator` in the theorem's proof.  Each hypothesis of
  `ft_geometry` names the one result of theirs it stands for, so a lane landing
  that result discharges exactly one field.

## Implementation notes

The `(deg Q, r) = (2,1)` exclusion is carried explicitly: their Props. 1--2 and
Lemma 3 all exclude it, `τ` is constant there, and `rem:quadratic-case` is what
our paper says instead.  `QuadraticDefect` proves that case outright, so the
exclusion costs nothing.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `subsec:FT-geometry`,
`thm:FT-geometry`, `eq:principal-pair`, `eq:endpoint-linear-gap`,
`eq:endpoint-fixed-gap`).

## Tags

Forgacs-Tran geometry, assembly, denominator pencil
-/

namespace ForgacsTran

open Polynomial Complex Real

/-! ### Compact-uniform separation — the theorem's one sentence of our own -/

private theorem exists_ratio_single {t : ℝ → ℂ} {τ : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (ht : ContinuousOn t K) (hτ : ContinuousOn τ K) (hτpos : ∀ θ ∈ K, 0 < τ θ)
    (hgap : ∀ θ ∈ K, τ θ < ‖t θ‖) :
    ∃ c > (1 : ℝ), ∀ θ ∈ K, c * τ θ ≤ ‖t θ‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨2, by norm_num, by simp⟩
  have hf : ContinuousOn (fun θ => ‖t θ‖ / τ θ) K :=
    ht.norm.div hτ fun θ hθ => (hτpos θ hθ).ne'
  obtain ⟨θ₀, hθ₀, hmin⟩ := hK.exists_isMinOn hKne hf
  refine ⟨‖t θ₀‖ / τ θ₀, ?_, fun θ hθ => ?_⟩
  · rw [gt_iff_lt, lt_div_iff₀ (hτpos θ₀ hθ₀), one_mul]
    exact hgap θ₀ hθ₀
  · have hle : ‖t θ₀‖ / τ θ₀ ≤ ‖t θ‖ / τ θ := isMinOn_iff.1 hmin θ hθ
    have := mul_le_mul_of_nonneg_right hle (hτpos θ hθ).le
    rwa [div_mul_cancel₀ _ (hτpos θ hθ).ne'] at this

private theorem exists_ratio_finset {ι : Type*} {J : Finset ι} {t : ι → ℝ → ℂ} {τ : ℝ → ℝ}
    {K : Set ℝ} (hτpos : ∀ θ ∈ K, 0 < τ θ)
    (h : ∀ i ∈ J, ∃ c > (1 : ℝ), ∀ θ ∈ K, c * τ θ ≤ ‖t i θ‖) :
    ∃ c > (1 : ℝ), ∀ θ ∈ K, ∀ i ∈ J, c * τ θ ≤ ‖t i θ‖ := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨2, by norm_num, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c₁, hc₁, h₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨c₂, hc₂, h₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun θ hθ i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (hτpos θ hθ).le) (h₁ θ hθ)
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (hτpos θ hθ).le)
        (h₂ θ hθ i hi)

/-- **`thm:FT-geometry`, compact-uniform separation — our step.**  On a compact
set of angles, a strict pointwise modulus gap between the principal modulus `τ`
and each of finitely many continuously varying denominator zeros is one uniform
ratio.

The theorem's proof asserts this in a sentence: "Compact-uniform separation
follows by continuity of the roots, compactness, and the strict pointwise modulus
gap."  All three inputs are hypotheses here and nothing else is used — in
particular the pencil does not appear, so the statement holds of any family of
roots however they are enumerated. -/
theorem ft_compact_uniform_separation {ι : Type*} {J : Finset ι} {K : Set ℝ} (hK : IsCompact K)
    {t : ι → ℝ → ℂ} {τ : ℝ → ℝ}
    (ht : ∀ i ∈ J, ContinuousOn (t i) K) (hτ : ContinuousOn τ K)
    (hτpos : ∀ θ ∈ K, 0 < τ θ)
    (hgap : ∀ θ ∈ K, ∀ i ∈ J, τ θ < ‖t i θ‖) :
    ∃ ratio > (1 : ℝ), ∀ θ ∈ K, ∀ i ∈ J, ratio * τ θ ≤ ‖t i θ‖ :=
  exists_ratio_finset hτpos fun i hi =>
    exists_ratio_single hK (ht i hi) hτ hτpos fun θ hθ => hgap θ hθ i hi

/-! ### The principal pair -/

/-- `eq:principal-pair` — `|t_+(θ)| = τ(θ)`. -/
theorem norm_ftPrincipal_eq {τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ) : ‖ftPrincipal τ θ‖ = τ θ := by
  rw [ftPrincipal, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hτ]

/-- `eq:principal-pair` — the second member `t_-(θ) = τ(θ)e^{-iθ}` is the
conjugate of the first, so it has the same modulus. -/
theorem conj_ftPrincipal {τ : ℝ → ℝ} (θ : ℝ) :
    (starRingEnd ℂ) (ftPrincipal τ θ)
      = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  rw [ftPrincipal, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-- **The principal pair is a genuine pair.**  `t_+` has positive imaginary part on
the open arc, so it is distinct from `t_-`.  This is the conjugate spelling, which
is the one `thm:FT-geometry` and `ft_minModulus_at_branch` state the pair in. -/
theorem ftPrincipal_ne_conj_of_pos {τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ)
    (hθ : θ ∈ Set.Ioo 0 π) : ftPrincipal τ θ ≠ (starRingEnd ℂ) (ftPrincipal τ θ) := by
  intro h
  have him := congrArg Complex.im h
  rw [Complex.conj_im] at him
  have hi : (ftPrincipal τ θ).im = τ θ * Real.sin θ := by
    simp [ftPrincipal, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
  rw [hi] at him
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  nlinarith

/-- The same in the arc-point spelling `t_- = τ(θ)e^{-iθ}`, which is what the
contour and dominance statements write.  `conj_ftPrincipal` is the only step
between the two, so neither spelling should be reproved. -/
theorem ftPrincipal_ne_arcPoint_of_pos {τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ)
    (hθ : θ ∈ Set.Ioo 0 π) :
    ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
  rw [← conj_ftPrincipal]
  exact ftPrincipal_ne_conj_of_pos hτ hθ


theorem norm_conj_ftPrincipal_eq {τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ) :
    ‖(starRingEnd ℂ) (ftPrincipal τ θ)‖ = τ θ := by
  rw [RCLike.norm_conj, norm_ftPrincipal_eq hτ]

/-- **`eq:principal-pair`, the half that is not cited.**  `Q` has real
coefficients and `z(θ)` is real, so `t_-` is a denominator zero as soon as `t_+`
is.  `Forgacs2017RationalDenominator` Lemma 2 supplies one member of the pair;
this supplies the other. -/
theorem ftPrincipal_conj_eval_eq_zero {Q : Polynomial ℂ} (hQ : HasRealCoeffs Q) {r : ℕ}
    {z τ : ℝ → ℝ} {θ : ℝ} (hroot : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) :
    (ftDen Q r ((z θ : ℝ) : ℂ)).eval ((starRingEnd ℂ) (ftPrincipal τ θ)) = 0 :=
  ftDen_eval_conj_eq_zero hQ hroot

/-- **`thm:FT-geometry`, "they are the only denominator zeros in the closed disk
`|t| ≤ τ(θ)`".**  Their Props. 1--2 give the strict gap at every other zero;
this is the disk statement that gap is equivalent to, which is the form the
theorem asserts and the contour arguments of `subsec:contour-residues` use. -/
theorem ft_principal_pair_of_norm_le {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {θ : ℝ}
    (hmin : ∀ w : ℂ, (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
      w ≠ ftPrincipal τ θ → w ≠ (starRingEnd ℂ) (ftPrincipal τ θ) → τ θ < ‖w‖)
    {w : ℂ} (hw : (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0) (hnorm : ‖w‖ ≤ τ θ) :
    w = ftPrincipal τ θ ∨ w = (starRingEnd ℂ) (ftPrincipal τ θ) := by
  by_contra hcon
  push Not at hcon
  exact absurd (hmin w hw hcon.1 hcon.2) (not_lt.2 hnorm)

/-! ### `z` maps the viewing arc onto the Forgács--Tran interval -/

private theorem nhdsWithin_Ioo_neBot_left {p q : ℝ} (h : p < q) :
    (nhdsWithin p (Set.Ioo p q)).NeBot :=
  Filter.neBot_of_le (f := nhdsWithin p (Set.Ioi p)) (nhdsWithin_le_iff.2 (Ioo_mem_nhdsGT h))

private theorem nhdsWithin_Ioo_neBot_right {p q : ℝ} (h : p < q) :
    (nhdsWithin q (Set.Ioo p q)).NeBot :=
  Filter.neBot_of_le (f := nhdsWithin q (Set.Iio q)) (nhdsWithin_le_iff.2 (Ioo_mem_nhdsLT h))

private theorem pi_div_pos {r : ℕ} (hr : 1 ≤ r) : (0 : ℝ) < π / r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  exact div_pos Real.pi_pos hr0

/-- **`thm:FT-geometry`, "`z(θ) → a` as `θ↓0`, `z(θ) → b` as `θ↑π/r`" turned into
the surjection `eq:ab-def` asks for**, in the finite upper-endpoint convention
(`r = 1`, where `b = g(t_b)`).  Monotonicity, continuity and the two limits are
`Forgacs2017RationalDenominator`'s; that they force the image to be exactly
`I_{Q,r}` is `FTMinModulus.image_Ioo_eq_Ioo_of_tendsto`. -/
theorem ft_geometry_image_Ioo {r : ℕ} (hr : 1 ≤ r) {a b : ℝ} {z : ℝ → ℝ}
    (hzcont : ContinuousOn z (Set.Ioo 0 (π / r)))
    (hzmono : StrictMonoOn z (Set.Ioo 0 (π / r)))
    (hza : Filter.Tendsto z (nhdsWithin 0 (Set.Ioo 0 (π / r))) (nhds a))
    (hzb : Filter.Tendsto z (nhdsWithin (π / r) (Set.Ioo 0 (π / r))) (nhds b)) :
    z '' Set.Ioo 0 (π / r) = Set.Ioo a b := by
  haveI := nhdsWithin_Ioo_neBot_left (pi_div_pos hr)
  haveI := nhdsWithin_Ioo_neBot_right (pi_div_pos hr)
  exact image_Ioo_eq_Ioo_of_tendsto hzcont hzmono hza hzb

/-- **The same in the unbounded convention** — `eq:ab-def`'s `b = +∞` for
`r > 1`, where the upper endpoint is not a real number and the image is the ray
`(a,∞)`.  `eq:endpoint-fixed-gap` is not stated in this convention: the paper
gives it at `θ↑π` with `r = 1` only. -/
theorem ft_geometry_image_Ioi {r : ℕ} (hr : 1 ≤ r) {a : ℝ} {z : ℝ → ℝ}
    (hzcont : ContinuousOn z (Set.Ioo 0 (π / r)))
    (hzmono : StrictMonoOn z (Set.Ioo 0 (π / r)))
    (hza : Filter.Tendsto z (nhdsWithin 0 (Set.Ioo 0 (π / r))) (nhds a))
    (hzb : Filter.Tendsto z (nhdsWithin (π / r) (Set.Ioo 0 (π / r))) Filter.atTop) :
    z '' Set.Ioo 0 (π / r) = Set.Ioi a := by
  haveI := nhdsWithin_Ioo_neBot_left (pi_div_pos hr)
  haveI := nhdsWithin_Ioo_neBot_right (pi_div_pos hr)
  exact image_Ioo_eq_Ioi_of_tendsto_atTop hzcont hzmono hza hzb

/-! ### The assembly -/

/-- **`thm:FT-geometry`, in the finite upper-endpoint convention of
`eq:ab-def`.**  The theorem's parametrization claims, composed: `z` maps the
viewing arc onto `I_{Q,r}`, the principal pair `eq:principal-pair` are
denominator zeros of common modulus `τ(θ)`, and they exhaust the closed disk
`|t| ≤ τ(θ)`.

Everything the theorem's proof attributes to `Forgacs2017RationalDenominator` is
a named hypothesis, one per cited result:

* `hbranch`, `hτpos` — their Lemma 2, the angle system and its positive modulus:
  `t_+(θ) = τ(θ)e^{iθ}` is a zero of `Q + z(θ)t^r` at every angle of the arc.
  `FTBranchExistence.exists_unique_ftAngleSystem_pencil` is that lemma in their
  vocabulary; the passage to a root of the pencil is `FTBranchPencil`.
* `hzmono` — their Lemmas 3--4, `z` strictly increasing.
  `FTBranchMonotone.ftTau_strictAnti` is the `τ` half.
* `hzcont` — continuity of `z` on the arc, from their regularity;
  `FTBranchRegularity.hasDerivAt_ftBranchAngle` supplies it.
* `hza`, `hzb` — their Lemma 6, the endpoint limits of `z`.
  `FTMinModulus.tendsto_ftZ_of_tendsto_branchPoint` reduces these to the
  endpoint limits of `τ`, which are what `FTBranchEndpoint` is landing.
* `hmin` — their Props. 1--2, that every other denominator zero has modulus
  strictly above `τ(θ)`.  `FTMinModulus.one_lt_norm_zeta_iff` is the
  normalization between their two statements of it, and the three steps of
  Prop. 1 are there; its closing step is open.

**There is no `(deg Q, r) = (2,1)` exclusion here, and there must not be.**  The
composition below runs on the cited results' *conclusions*, so it consumes no
such hypothesis; and every input is available at the quadratic pencil, which
`ft_geometry_hypotheses_satisfiable` exhibits.  A binder excluding that case
would be *false* exactly there, making this theorem vacuous at a pencil it
covers — and it would put the case out of reach of every consumer, since
`¬(2 = 2 ∧ 1 = 1)` cannot be supplied.  `FTGeometryBoundary` closes `(2,1)`
through this statement; `τ` is constant there, which is what
`rem:quadratic-case` records and what `QuadraticDefect` proves, and none of that
is an obstruction to the three clauses below.

**Containment**, clause by clause, and one of the three does not pass.

* The image clause relates `z` to the whole of `(a,b)`.  `hza` and `hzb` mention
  `z` and the endpoints together, but they assert limits, and a limit is not a
  value attained; surjectivity comes from the intermediate value theorem inside
  `FTMinModulus.image_Ioo_eq_Ioo_of_tendsto`.  Not contained.
* The pair clause relates `t_+` and `t_-`.  `hbranch` gives `t_+` alone; `t_-`
  is a zero because `Q` has real coefficients, and the two moduli are computed.
  Not contained.
* The disk clause relates the principal pair to every other denominator zero,
  and `hmin` **does** mention both sides — it is that same relation stated
  pointwise at a non-principal zero.  This clause is `hmin`'s contrapositive
  together with `‖t_±‖ = τ(θ)`, and it carries no content `hmin` does not.  It
  is here because `thm:FT-geometry` states the disk form and
  `subsec:contour-residues` consumes it that way, not because anything is proved
  by stating it.  Where the pointwise gap does buy something is
  `ft_geometry_compact_separation`, which turns it into one constant. -/
theorem ft_geometry {Q : Polynomial ℂ} (hQ : HasRealCoeffs Q) {r : ℕ} (hr : 1 ≤ r)
    {a b : ℝ} {z τ : ℝ → ℝ}
    (hbranch : ∀ θ ∈ Set.Ioo 0 (π / r),
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hτpos : ∀ θ ∈ Set.Ioo 0 (π / r), 0 < τ θ)
    (hzmono : StrictMonoOn z (Set.Ioo 0 (π / r)))
    (hzcont : ContinuousOn z (Set.Ioo 0 (π / r)))
    (hza : Filter.Tendsto z (nhdsWithin 0 (Set.Ioo 0 (π / r))) (nhds a))
    (hzb : Filter.Tendsto z (nhdsWithin (π / r) (Set.Ioo 0 (π / r))) (nhds b))
    (hmin : ∀ θ ∈ Set.Ioo 0 (π / r), ∀ w : ℂ,
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal τ θ → w ≠ (starRingEnd ℂ) (ftPrincipal τ θ) → τ θ < ‖w‖) :
    z '' Set.Ioo 0 (π / r) = Set.Ioo a b
      ∧ (∀ θ ∈ Set.Ioo 0 (π / r),
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0
            ∧ (ftDen Q r ((z θ : ℝ) : ℂ)).eval ((starRingEnd ℂ) (ftPrincipal τ θ)) = 0
            ∧ ‖ftPrincipal τ θ‖ = τ θ
            ∧ ‖(starRingEnd ℂ) (ftPrincipal τ θ)‖ = τ θ)
      ∧ (∀ θ ∈ Set.Ioo 0 (π / r), ∀ w : ℂ,
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 → ‖w‖ ≤ τ θ →
            w = ftPrincipal τ θ ∨ w = (starRingEnd ℂ) (ftPrincipal τ θ)) := by
  refine ⟨ft_geometry_image_Ioo hr hzcont hzmono hza hzb, fun θ hθ => ?_,
    fun θ hθ w hw hnorm => ft_principal_pair_of_norm_le (hmin θ hθ) hw hnorm⟩
  exact ⟨hbranch θ hθ, ftPrincipal_conj_eval_eq_zero hQ (hbranch θ hθ),
    norm_ftPrincipal_eq (hτpos θ hθ), norm_conj_ftPrincipal_eq (hτpos θ hθ)⟩

/-- **`thm:FT-geometry` in the unbounded convention** — `r > 1`, where
`eq:ab-def` sets `b = +∞` and the image is the ray `(a,∞)`.  The hypothesis list
is `ft_geometry`'s with the upper limit replaced by divergence, which is what
`FTMinModulus.tendsto_norm_ftZ_atTop_of_tendsto_zero` produces when the branch
point runs into the origin.  `eq:endpoint-fixed-gap` is deliberately absent from
both statements' conclusions: the paper gives it at `θ↑π` with `r = 1`, and
`FTGeometryExtraction.ft_endpoint_fixed_gap_of_pointwise` is where it lives. -/
theorem ft_geometry_unbounded {Q : Polynomial ℂ} (hQ : HasRealCoeffs Q) {r : ℕ} (hr : 1 ≤ r)
    {a : ℝ} {z τ : ℝ → ℝ}
    (hbranch : ∀ θ ∈ Set.Ioo 0 (π / r),
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hτpos : ∀ θ ∈ Set.Ioo 0 (π / r), 0 < τ θ)
    (hzmono : StrictMonoOn z (Set.Ioo 0 (π / r)))
    (hzcont : ContinuousOn z (Set.Ioo 0 (π / r)))
    (hza : Filter.Tendsto z (nhdsWithin 0 (Set.Ioo 0 (π / r))) (nhds a))
    (hzb : Filter.Tendsto z (nhdsWithin (π / r) (Set.Ioo 0 (π / r))) Filter.atTop)
    (hmin : ∀ θ ∈ Set.Ioo 0 (π / r), ∀ w : ℂ,
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal τ θ → w ≠ (starRingEnd ℂ) (ftPrincipal τ θ) → τ θ < ‖w‖) :
    z '' Set.Ioo 0 (π / r) = Set.Ioi a
      ∧ (∀ θ ∈ Set.Ioo 0 (π / r),
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0
            ∧ (ftDen Q r ((z θ : ℝ) : ℂ)).eval ((starRingEnd ℂ) (ftPrincipal τ θ)) = 0
            ∧ ‖ftPrincipal τ θ‖ = τ θ
            ∧ ‖(starRingEnd ℂ) (ftPrincipal τ θ)‖ = τ θ)
      ∧ (∀ θ ∈ Set.Ioo 0 (π / r), ∀ w : ℂ,
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 → ‖w‖ ≤ τ θ →
            w = ftPrincipal τ θ ∨ w = (starRingEnd ℂ) (ftPrincipal τ θ)) := by
  refine ⟨ft_geometry_image_Ioi hr hzcont hzmono hza hzb, fun θ hθ => ?_,
    fun θ hθ w hw hnorm => ft_principal_pair_of_norm_le (hmin θ hθ) hw hnorm⟩
  exact ⟨hbranch θ hθ, ftPrincipal_conj_eval_eq_zero hQ (hbranch θ hθ),
    norm_ftPrincipal_eq (hτpos θ hθ), norm_conj_ftPrincipal_eq (hτpos θ hθ)⟩

/-! ### The separation clauses, in the pencil's own vocabulary -/

/-- **`thm:FT-geometry`, "On every compact subinterval of `(0,π/r)`, the
remaining denominator zeros are separated from the principal pair by a uniform
modulus ratio".**  `ft_compact_uniform_separation` with the pointwise gap
supplied by their Props. 1--2 (`hmin`) at each non-principal zero, and the
enumeration `t` of those zeros supplied as continuous functions of the angle —
which is the theorem's "continuity of the roots". -/
theorem ft_geometry_compact_separation {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Set.Ioo 0 (π / r))
    {ι : Type*} {J : Finset ι} {t : ι → ℝ → ℂ}
    (ht : ∀ i ∈ J, ContinuousOn (t i) K) (hτcont : ContinuousOn τ K)
    (hτpos : ∀ θ ∈ Set.Ioo 0 (π / r), 0 < τ θ)
    (hroot : ∀ θ ∈ K, ∀ i ∈ J, (ftDen Q r ((z θ : ℝ) : ℂ)).eval (t i θ) = 0)
    (hnp : ∀ θ ∈ K, ∀ i ∈ J, t i θ ≠ ftPrincipal τ θ)
    (hnp' : ∀ θ ∈ K, ∀ i ∈ J, t i θ ≠ (starRingEnd ℂ) (ftPrincipal τ θ))
    (hmin : ∀ θ ∈ Set.Ioo 0 (π / r), ∀ w : ℂ,
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal τ θ → w ≠ (starRingEnd ℂ) (ftPrincipal τ θ) → τ θ < ‖w‖) :
    ∃ ratio > (1 : ℝ), ∀ θ ∈ K, ∀ i ∈ J, ratio * τ θ ≤ ‖t i θ‖ :=
  ft_compact_uniform_separation hK ht hτcont (fun θ hθ => hτpos θ (hKsub hθ))
    fun θ hθ i hi =>
      hmin θ (hKsub hθ) (t i θ) (hroot θ hθ i hi) (hnp θ hθ i hi) (hnp' θ hθ i hi)

/-- **`thm:FT-geometry`'s two endpoint clauses on one constant.**  The theorem
states them separately — "`|ζ_j(θ)| ≥ 1 + cδ` for some `c > 0`" for the
nonprincipal cluster members, "`|ζ_j(θ)| ≥ 1 + c_*` for a fixed `c_* > 0`" for
the zeros outside it — and `subsec:weighted-dominance` then uses them together.
Reconciling the two constants and the threshold is what this does: one `c` and
one `δ₀` serve both.

The cluster half rests on `FTMinModulus.exists_endpoint_linear_gap_of_expansion`,
hence on their Prop. 3 expansion, which is `hexp`; the outside half on
`FTGeometryExtraction.ft_endpoint_fixed_gap_of_pointwise`, hence on the strict
pointwise gap `hm`, which is their Props. 1--2 again at the endpoint.

**The expansion coefficient is complex, and `hexp` has to say so.**  Prop. 3
gives `ζ_j(δ) = 1 + c_jδ + O(δ²)` with `c_j = (cos(π/ρ) - ω_j)/sin(π/ρ)` and
`ω_j^ρ = -1`, so `Im c_j = -Im(ω_j)/sin(π/ρ)`, which vanishes only where `ω_j`
is real.  Among the nonprincipal members that happens at `ρ ≤ 3` and nowhere
else: `|Im c_j|` runs `1`, `1.618`, `2`, `2.247` at `ρ = 4,5,6,7`.  Comparing
the complex `ζ_j` against the *real* target `1 + (Re c_j)δ` therefore leaves a
residual of order `δ`, not `δ²`, and no finite `Cexp` exists — the hypothesis
would be well-typed, unsatisfiable at the actual roots, and the theorem
vacuously true from `ρ = 4` on.  Only the modulus expansion carries the real
coefficient, and `endpoint_expansion_coeff_re` is where the two meet: it takes
the real part of `c_j` back to `Geometry.endpoint_linear_coeff_pos`. -/
theorem ft_geometry_endpoint_gaps {ρ n : ℕ} (hρ : 2 ≤ ρ) {idx : Fin n → ℕ}
    {ζ : Fin n → ℝ → ℂ} {Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (hωne : ∀ i : Fin n, clusterOmega ρ (idx i)
      ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * I))
    (hωne' : ∀ i : Fin n, clusterOmega ρ (idx i)
      ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * I))
    (hexp : ∀ i : Fin n, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖ζ i δ - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx i))
        / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ Cexp * δ ^ 2)
    {ι : Type*} {J : Finset ι} {m : ι → ℝ} (hm : ∀ j ∈ J, 1 < m j) :
    ∃ c > (0 : ℝ), ∃ δ₀ > (0 : ℝ),
      (∀ i : Fin n, ∀ δ : ℝ, 0 < δ → δ < δ₀ → 1 + c * δ ≤ ‖ζ i δ‖)
        ∧ (∀ j ∈ J, 1 + c ≤ m j) := by
  obtain ⟨c₀, hc₀, δ₀, hδ₀, hlin⟩ :=
    exists_endpoint_linear_gap_of_expansion (J := (Finset.univ : Finset (Fin n))) (ζ := ζ)
      (c := fun i => (((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx i))
        / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ))
      hCexp
      (fun i _ => by
        rw [endpoint_expansion_coeff_re]
        exact endpoint_linear_coeff_pos hρ (clusterOmega_pow (by omega) _) (hωne i) (hωne' i))
      (fun i _ => hexp i)
  obtain ⟨cstar, hcstar, hfix⟩ := ft_endpoint_fixed_gap_of_pointwise hm
  refine ⟨min c₀ cstar, lt_min hc₀ hcstar, δ₀, hδ₀, fun i δ hδ hδlt => ?_, fun j hj => ?_⟩
  · exact le_trans (by nlinarith [min_le_left c₀ cstar])
      (hlin i (Finset.mem_univ i) δ hδ hδlt)
  · exact le_trans (by linarith [min_le_right c₀ cstar]) (hfix j hj)

/-! ### The principal branch is differentiable on the arc

`FTBranchRegularity` proves `τ` differentiable on `(0,π/r)` with no hypothesis
beyond a pencil with positive zeros, but states the branch *point* as
`ftBranchPoint = τ(θ)e^{-iθ}`, which is `t_-` of `eq:principal-pair`.  What
`DominanceFT`'s interior hypotheses want is `t_+ = ftPrincipal τ = τ(θ)e^{iθ}`.
Rather than conjugate, the derivative is taken directly from `τ`'s, which is
shorter and keeps the sign of the imaginary part visible — and it is that sign
that makes `γ' ≠ 0`. -/

/-- **`eq:principal-pair` differentiated**, unconditionally on the paper's
admissible class: `t_+'(θ) = (τ'(θ) + iτ(θ))e^{iθ}`.  `hnr` is
`max{deg Q, r} > 1`, which `eq:Q-hypotheses` already imposes. -/
theorem hasDerivAt_ftPrincipal_ftTau {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / r)) :
    HasDerivAt (ftPrincipal (ftTau a r (n - 1)))
      (((ftTauDeriv a r (n - 1) θ₀ : ℝ) : ℂ)
          * Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I)
        + ((ftTau a r (n - 1) θ₀ : ℝ) : ℂ)
            * (Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) * Complex.I)) θ₀ := by
  have hτ : HasDerivAt (fun θ : ℝ => ((ftTau a r (n - 1) θ : ℝ) : ℂ))
      (((ftTauDeriv a r (n - 1) θ₀ : ℝ) : ℂ)) θ₀ :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ₀
      (hasDerivAt_ftTau_principal hn ha hr hnr hθ₀)
  have hlin : HasDerivAt (fun θ : ℝ => ((θ : ℝ) : ℂ) * Complex.I) Complex.I θ₀ := by
    simpa using
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ₀ (hasDerivAt_id θ₀)).mul_const Complex.I
  exact hτ.mul hlin.cexp

/-- The same in the form `DominanceFT`'s interior hypotheses take it: a nonzero
derivative at every angle of the arc.  Nonvanishing is the sign of the imaginary
part — `τ(θ) > 0`, so `τ' + iτ ≠ 0` however `τ'` behaves. -/
theorem exists_hasDerivAt_ftPrincipal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / r)) :
    ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal (ftTau a r (n - 1))) γ' θ₀ := by
  refine ⟨_, ?_, hasDerivAt_ftPrincipal_ftTau hn ha hr hnr hθ₀⟩
  have hτpos : 0 < ftTau a r (n - 1) θ₀ :=
    ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ₀)
  have hfac : ((ftTauDeriv a r (n - 1) θ₀ : ℝ) : ℂ)
        * Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I)
      + ((ftTau a r (n - 1) θ₀ : ℝ) : ℂ)
          * (Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) * Complex.I)
      = (((ftTauDeriv a r (n - 1) θ₀ : ℝ) : ℂ) + ((ftTau a r (n - 1) θ₀ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I) := by ring
  rw [hfac]
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  intro hzero
  have him : (((ftTauDeriv a r (n - 1) θ₀ : ℝ) : ℂ)
      + ((ftTau a r (n - 1) θ₀ : ℝ) : ℂ) * Complex.I).im = ftTau a r (n - 1) θ₀ := by
    simp
  rw [hzero] at him
  simp only [Complex.zero_im] at him
  exact hτpos.ne him

/-- **Exactly the interior hypothesis `DominanceFT` carries**, discharged:
`∀ θ ∈ K, ∃ γ' ≠ 0, HasDerivAt (ftPrincipal τ) γ' θ` for any `K` inside the arc.

This covers the *interior* amplitude hypotheses only.  The two endpoint
derivatives `hγd₀`, `hγd₁` of `weighted_dominance_of_branch` are taken at
`δ = 0`, off the open arc, and are not instances of this: they assert that the
branch extends regularly to the closed interval, which is
`eq:principal-finite-endpoint-regularity` of `lem:principal-endpoint-regularity`
and a different theorem from differentiability inside. -/
theorem ftPrincipal_hasDerivAt_of_subset {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {K : Set ℝ}
    (hK : K ⊆ Set.Ioo 0 (π / r)) :
    ∀ θ ∈ K, ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal (ftTau a r (n - 1))) γ' θ :=
  fun _θ hθ => exists_hasDerivAt_ftPrincipal hn ha hr hnr (hK hθ)

/-! ### The hypothesis set is inhabited

`ft_geometry` is conditional on seven statements of
`Forgacs2017RationalDenominator`, and a conditional theorem is worth what its
hypotheses are worth: if they cannot be met together, it says nothing.  Nothing
in the tree instantiates them, so the witness below certifies that they are
jointly satisfiable — and that the conclusion is not degenerate at the witness,
since `z` really does surject onto an interval and the disk clause really does
constrain a root set.

The witness is the quadratic pencil, and it certifies `ft_geometry` itself:
every hypothesis below is met at `(deg Q, r) = (2,1)`, which is why that case is
not excluded and why `FTGeometryBoundary.ft_geometry_at_branch_quadratic` reaches
it through the general statement rather than around it. -/

private theorem hasRealCoeffs_quadPoly (q0 q1 q2 : ℝ) :
    HasRealCoeffs (quadPoly q0 q1 q2) := by
  intro k
  simp only [quadPoly, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, map_add, map_mul,
    Complex.conj_ofReal]
  split <;> split <;> simp

private theorem natDegree_quadPoly {q0 q1 q2 : ℝ} (hq2 : 0 < q2) :
    (quadPoly q0 q1 q2).natDegree = 2 := by
  have hq2c : ((q2 : ℝ) : ℂ) ≠ 0 := by simpa using hq2.ne'
  have heq : quadPoly q0 q1 q2
      = C ((q2 : ℝ) : ℂ) * X ^ 2 + C ((q1 : ℝ) : ℂ) * X + C ((q0 : ℝ) : ℂ) := by
    rw [quadPoly]; ring
  rw [heq, Polynomial.natDegree_quadratic hq2c]

/-- **The seven cited hypotheses of `ft_geometry` are jointly satisfiable**, and
the conclusion is not degenerate where they hold.  Witnessed on the quadratic
pencil, where `rem:quadratic-case` writes every one of them down: `τ` is the
constant `√(q₀/q₂)`, `z(θ) = -q₁ - 2√(q₀q₂)cos θ` is strictly increasing with the
right endpoint limits, and the minimum-modulus hypothesis holds because the
pencil has degree two — a third zero would give three distinct roots. -/
theorem ft_geometry_hypotheses_satisfiable {q0 q1 q2 : ℝ} (hq0 : 0 < q0) (hq2 : 0 < q2) :
    ∃ (Q : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (a b : ℝ),
      HasRealCoeffs Q ∧ 1 ≤ r ∧ a < b ∧
      (∀ θ ∈ Set.Ioo 0 (π / r),
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
      (∀ θ ∈ Set.Ioo 0 (π / r), 0 < τ θ) ∧
      StrictMonoOn z (Set.Ioo 0 (π / r)) ∧
      ContinuousOn z (Set.Ioo 0 (π / r)) ∧
      Filter.Tendsto z (nhdsWithin 0 (Set.Ioo 0 (π / r))) (nhds a) ∧
      Filter.Tendsto z (nhdsWithin (π / r) (Set.Ioo 0 (π / r))) (nhds b) ∧
      (∀ θ ∈ Set.Ioo 0 (π / r), ∀ w : ℂ,
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
          w ≠ ftPrincipal τ θ → w ≠ (starRingEnd ℂ) (ftPrincipal τ θ) → τ θ < ‖w‖) := by
  set s : ℝ := Real.sqrt (q0 * q2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set τc : ℝ := Real.sqrt (q0 / q2) with hτc
  have hτ0 : 0 < τc := Real.sqrt_pos.mpr (by positivity)
  set zf : ℝ → ℝ := fun θ => -q1 - 2 * s * Real.cos θ with hzf
  have hπr : π / ((1 : ℕ) : ℝ) = π := by norm_num
  have hzcont : Continuous zf := by rw [hzf]; fun_prop
  refine ⟨quadPoly q0 q1 q2, 1, zf, fun _ => τc, -q1 - 2 * s, -q1 + 2 * s,
    hasRealCoeffs_quadPoly q0 q1 q2, le_rfl, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ _
    exact quadDen_eval_principal hq0 hq2 θ
  · intro θ _; exact hτ0
  · rw [hπr]
    exact (quadratic_z_strictMonoOn hq0 hq2 q1).mono
      (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  · exact hzcont.continuousOn
  · refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    simpa [hzf] using hzcont.tendsto 0
  · refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    rw [hπr]
    simpa [hzf] using hzcont.tendsto π
  -- the minimum-modulus hypothesis: a degree-two pencil has no third zero
  · rw [hπr]
    intro θ hθ w hw hne hne'
    exfalso
    classical
    set P : Polynomial ℂ := ftDen (quadPoly q0 q1 q2) 1 ((zf θ : ℝ) : ℂ) with hP
    have hdeg : P.natDegree = 2 := by
      rw [hP, ftDen]
      rw [natDegree_add_eq_left_of_natDegree_lt]
      · exact natDegree_quadPoly hq2
      · refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
        rw [natDegree_quadPoly hq2, pow_one, natDegree_X]
        norm_num
    have hq2c : ((q2 : ℝ) : ℂ) ≠ 0 := by simpa using hq2.ne'
    have hPne : P ≠ 0 := by
      intro h
      rw [h] at hdeg
      simp at hdeg
    have hplus : P.eval (ftPrincipal (fun _ => τc) θ) = 0 := quadDen_eval_principal hq0 hq2 θ
    have hminus : P.eval ((starRingEnd ℂ) (ftPrincipal (fun _ => τc) θ)) = 0 :=
      ftDen_eval_conj_eq_zero (hasRealCoeffs_quadPoly q0 q1 q2) hplus
    have hpair : ftPrincipal (fun _ => τc) θ ≠ (starRingEnd ℂ) (ftPrincipal (fun _ => τc) θ) := by
      rw [conj_ftPrincipal]
      intro heq
      have hτne : ((τc : ℝ) : ℂ) ≠ 0 := by simpa using hτ0.ne'
      have hE : Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
          = Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
        simpa [ftPrincipal, hτne] using heq
      have him := congrArg Complex.im hE
      rw [show -((θ : ℝ) : ℂ) = (((-θ : ℝ)) : ℂ) by push_cast; ring] at him
      rw [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg] at him
      have : Real.sin θ = 0 := by linarith
      exact absurd this (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
    have hsub : ({ftPrincipal (fun _ => τc) θ,
        (starRingEnd ℂ) (ftPrincipal (fun _ => τc) θ), w} : Finset ℂ) ⊆ P.roots.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Multiset.mem_toFinset, mem_roots hPne, IsRoot]
      rcases hx with rfl | rfl | rfl
      · exact hplus
      · exact hminus
      · exact hw
    have hcard : ({ftPrincipal (fun _ => τc) θ,
        (starRingEnd ℂ) (ftPrincipal (fun _ => τc) θ), w} : Finset ℂ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hpair, Ne.symm hne]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hne']), Finset.card_singleton]
    have h3 : 3 ≤ P.roots.toFinset.card := hcard ▸ Finset.card_le_card hsub
    have h2 : P.roots.toFinset.card ≤ 2 :=
      le_trans (Multiset.toFinset_card_le _) (le_trans (P.card_roots') (le_of_eq hdeg))
    omega

/-! ### Discharging `ft_geometry`'s hypotheses at the Forgács--Tran branch

Two of the seven are supplied outright once `τ` and `z` are taken to be the
branch's own `ftTau` and `ftBranchZ` rather than free functions.  Nothing is
restated here: `hbranch` is `FTBranchProp1.ftBranch_ftArcPoint_eq_ftBranchZ`
read as a root of the pencil and then conjugated, and `hτpos` is
`FTBranchFunction.ftTau_pos`. -/

/-- `ftRootPoly` is a real pencil, which is what lets the conjugate of a
denominator zero be one. -/
theorem hasRealCoeffs_ftRootPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    HasRealCoeffs (ftRootPoly c a) := by
  have hmap : ftRootPoly c a = (ftRootPolyReal c a).map (algebraMap ℝ ℂ) := by
    rw [ftRootPoly, ftRootPolyReal, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    simp
  intro k
  rw [hmap, coeff_map]
  simp

/-- **`eq:principal-pair`, at the branch's own data.**  `t_-(θ) = τ(θ)e^{-iθ}` is
a zero of `Q + z(θ)t^r` because `ftBranchZ` is by construction the value of the
fiber map there; `t_+` follows because the pencil is real.  This is
`ft_geometry`'s `hbranch`, discharged. -/
theorem ftDen_eval_ftPrincipal_ftBranchZ {n r l : ℕ} {a : Fin n → ℝ} (c : ℝ)
    (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 π) (h : FTBranchAt a r l θ) :
    (ftDen (ftRootPoly c a) r ((ftBranchZ a c r l θ : ℝ) : ℂ)).eval
      (ftPrincipal (ftTau a r l) θ) = 0 := by
  have hτ0 : 0 < ftTau a r l θ := ftTau_pos h
  have harc : ftArcPoint (ftTau a r l θ) θ ≠ 0 := by
    rw [ftArcPoint]
    exact mul_ne_zero (by simpa using hτ0.ne') (Complex.exp_ne_zero _)
  have hkey := ftBranch_ftArcPoint_eq_ftBranchZ (a := a) (r := r) (l := l) c ha hθ h
  have hminus : (ftDen (ftRootPoly c a) r ((ftBranchZ a c r l θ : ℝ) : ℂ)).eval
      (ftArcPoint (ftTau a r l θ) θ) = 0 := by
    have hr0 : (ftArcPoint (ftTau a r l θ) θ) ^ r ≠ 0 := pow_ne_zero _ harc
    rw [ftDen_eval, eval_ftRootPoly, ← hkey, div_mul_cancel₀ _ hr0]
    ring
  have hconj : (starRingEnd ℂ) (ftArcPoint (ftTau a r l θ) θ)
      = ftPrincipal (ftTau a r l) θ := by
    rw [ftArcPoint, ftPrincipal, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  rw [← hconj]
  exact ftDen_eval_conj_eq_zero (hasRealCoeffs_ftRootPoly c a) hminus

/-- **`ft_geometry`'s `hbranch` and `hτpos` together**, on the whole viewing arc
at the principal index, with no hypothesis beyond the admissible class. -/
theorem ft_branch_root_and_pos {n r : ℕ} {a : Fin n → ℝ} (c : ℝ) (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    (∀ θ ∈ Set.Ioo 0 (π / r),
        (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval
          (ftPrincipal (ftTau a r (n - 1)) θ) = 0)
      ∧ (∀ θ ∈ Set.Ioo 0 (π / r), 0 < ftTau a r (n - 1) θ) := by
  refine ⟨fun θ hθ => ?_, fun θ hθ => ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)⟩
  exact ftDen_eval_ftPrincipal_ftBranchZ c ha (ftArc_subset hr hθ)
    (ftBranchAt_of_arc_principal hn ha hr hnr hθ)

end ForgacsTran
