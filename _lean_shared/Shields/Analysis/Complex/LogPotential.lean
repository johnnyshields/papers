/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.MeasureTheory.CompactIntervalMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The logarithmic potential, and the logarithmic kernel as a continuous curve in `L¹`

Mathlib carries no logarithmic potential and no subharmonic functions, so there is no object
for a potential-theoretic convergence statement to be about.  This supplies the object and the
`L¹` theory of the kernel `z ↦ log ‖z - p‖` with `p` real.

Everything rests on one inequality.  For `z` at distance at most `R` from `p`,

  `|log ‖z - p‖| ≤ |log (z.im - p.im)| + |log R|`,

valid off the horizontal line through `p` (`Shields.abs_log_norm_sub_le`).  The right-hand side
is a function of the imaginary part alone, so it is integrable on every bounded plane region by
Fubini and the interval integrability of the logarithm, and — this is what makes the whole
development work — it does not change when `p` moves along the real axis.  A single dominating
function therefore serves the entire parameter interval `[0,1]`, and dominated convergence
replaces every uniform-integrability argument.

## Main definitions

* `Shields.logPotential`: the logarithmic potential `∫ log ‖z - p‖ dμ(p)` of a measure on the
  real line, evaluated at a complex point.
* `Shields.logKernelL1`: the kernel as a map from the real line into the Bochner space
  `Lp ℝ 1 (volume.restrict Q)` for a compact `Q ⊆ ℂ`.

## Main statements

* `Shields.integrableOn_log_norm_sub`: for every `p ∈ ℂ` and every bounded `Q ⊆ ℂ`,
  `z ↦ log ‖z - p‖` is integrable on `Q`.  This is the local integrability of `log|z|` in the
  plane, obtained without polar coordinates.
* `Shields.tendsto_integral_abs_log_norm_sub`, `Shields.continuous_logKernelL1`: continuity of
  `p ↦ log ‖· - p‖` from the real line into `L¹(Q)` for compact `Q`, concretely as convergence
  of the `L¹(Q)` distance and as continuity of a map into the Bochner space.
* `Shields.isCompact_image_logKernelL1`: the image of `[0,1]` is compact.
* `Shields.tendsto_logPotential_of_tendsto`, `Shields.tendsto_integral_abs_logPotential_sub`: if
  probability measures on `[0,1]` converge weakly, their logarithmic potentials converge
  pointwise off the real axis and in `L¹(Q)` for every compact `Q ⊆ ℂ`, including the part of
  `Q` that meets `[0,1]`.  The `L¹` statement is reached by dominated convergence in `z` against
  the same slice bound, not by Bochner integration of an `L¹(Q)`-valued curve, so no
  vector-valued portmanteau theorem is needed.

## Tags

logarithmic potential, subharmonic, weak convergence, Riesz measure, Bochner space
-/

open MeasureTheory Filter Topology Set

namespace Shields

/-! ## The logarithmic potential -/

/-- The logarithmic potential of a measure on the real line, evaluated at a complex point. -/
noncomputable def logPotential (μ : Measure ℝ) (z : ℂ) : ℝ :=
  ∫ p, Real.log ‖z - (p : ℂ)‖ ∂μ

/-- The kernel of `logPotential` is measurable in the integration variable. -/
theorem measurable_logPotentialKernel (z : ℂ) :
    Measurable fun p : ℝ => Real.log ‖z - (p : ℂ)‖ :=
  Real.measurable_log.comp
    ((continuous_const.sub Complex.continuous_ofReal).norm.measurable)


/-! ## The slice bound -/

/-- The two-dimensional logarithmic singularity is dominated by a one-dimensional one.  For `z`
within distance `R` of `p`, the size of `log ‖z - p‖` is controlled by the logarithm of the
vertical offset `z.im - p.im`, which involves neither `z.re` nor `p.re`.  A horizontal motion of
`p` therefore leaves the bound unchanged. -/
theorem abs_log_norm_sub_le {z p : ℂ} {R : ℝ} (hz : ‖z - p‖ ≤ R) (him : z.im ≠ p.im) :
    |Real.log ‖z - p‖| ≤ |Real.log (z.im - p.im)| + |Real.log R| := by
  have h0 : (0 : ℝ) < |z.im - p.im| := abs_pos.mpr (sub_ne_zero.mpr him)
  have hle : |z.im - p.im| ≤ ‖z - p‖ := by simpa using Complex.abs_im_le_norm (z - p)
  have hpos : (0 : ℝ) < ‖z - p‖ := lt_of_lt_of_le h0 hle
  have hlow : Real.log (z.im - p.im) ≤ Real.log ‖z - p‖ := by
    rw [← Real.log_abs]; exact Real.log_le_log h0 hle
  have hhigh : Real.log ‖z - p‖ ≤ Real.log R := Real.log_le_log hpos hz
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith [neg_abs_le (Real.log (z.im - p.im)), abs_nonneg (Real.log R)]
  · linarith [le_abs_self (Real.log R), abs_nonneg (Real.log (z.im - p.im))]

/-- A horizontal line is Lebesgue null in the plane, so the exceptional set of the slice bound
can be ignored. -/
theorem volume_im_eq (c : ℝ) : volume {z : ℂ | z.im = c} = 0 := by
  have hset : {z : ℂ | z.im = c}
      = Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ ({c} : Set ℝ)) := by
    ext z; simp
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem ae_im_ne (c : ℝ) : ∀ᵐ z : ℂ, z.im ≠ c := by
  rw [ae_iff]
  simpa using volume_im_eq c

/-- **Off the real axis the kernel is continuous in its real parameter.**  The evaluation point
never meets the line the parameter runs along, so the logarithm is taken at a nonzero argument
throughout. -/
theorem continuous_logKernel_ofReal {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun p : ℝ => Real.log ‖z - (p : ℂ)‖ := by
  refine ((continuous_const.sub Complex.continuous_ofReal).norm).log fun p h => hz ?_
  simpa using congrArg Complex.im (sub_eq_zero.mp (norm_eq_zero.mp h))

/-! ## Integrability of the kernel -/

theorem measurable_logKernel_left (p : ℂ) : Measurable fun z : ℂ => Real.log ‖z - p‖ :=
  Real.measurable_log.comp (continuous_id.sub continuous_const).norm.measurable

theorem measurableSet_reProdIm {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (Complex.reProdIm s t) :=
  (Complex.continuous_re.measurable hs).inter (Complex.continuous_im.measurable ht)

/-- Integrability on a complex box is integrability on the corresponding rectangle of the plane;
the identification of `ℂ` with `ℝ × ℝ` preserves Lebesgue measure. -/
theorem integrableOn_reProdIm {f : ℂ → ℝ} {s t : Set ℝ}
    (hf : IntegrableOn (fun q : ℝ × ℝ => f ⟨q.1, q.2⟩) (s ×ˢ t) volume) :
    IntegrableOn f (Complex.reProdIm s t) volume :=
  (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)).mpr hf

/-- The dominating function of `abs_log_norm_sub_le` is integrable on every box.  It depends on
the imaginary part alone, so Fubini reduces the claim to interval integrability of the shifted
logarithm on the vertical edge. -/
theorem integrableOn_dominating (c C : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    IntegrableOn (fun z : ℂ => |Real.log (z.im - c)| + C)
      (Complex.reProdIm (Icc (-A) A) (Icc (-A) A)) volume := by
  refine integrableOn_reProdIm ?_
  have hAA : -A ≤ A := by linarith
  have hfin : ∀ a b : ℝ, IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc a b)) := fun a b =>
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  haveI := hfin (-A) A
  have h1 : Integrable (fun y : ℝ => |Real.log (y - c)|)
      ((volume : Measure ℝ).restrict (Icc (-A) A)) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := -A - c)
      (b := A - c)).abs.comp_sub_right c
    simp only [sub_add_cancel] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hAA).mp h
  have key : Integrable (fun q : ℝ × ℝ => |Real.log (q.2 - c)| + C)
      (((volume : Measure ℝ).restrict (Icc (-A) A)).prod
        ((volume : Measure ℝ).restrict (Icc (-A) A))) :=
    (h1.comp_snd _).add (integrable_const C)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at key
  exact key

/-- Every bounded region has a radius. -/
theorem exists_norm_le {Q : Set ℂ} (hQ : Bornology.IsBounded Q) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ Q, ‖z‖ ≤ A := by
  obtain ⟨C₀, hC₀⟩ := isBounded_iff_forall_norm_le.mp hQ
  exact ⟨max C₀ 0, le_max_right _ _, fun z hz => (hC₀ z hz).trans (le_max_left _ _)⟩

/-- A region of radius `A` sits inside the square box of half-side `A`, which is where the
dominating function is integrable. -/
theorem subset_reProdIm_of_norm_le {Q : Set ℂ} {A : ℝ} (hA : ∀ z ∈ Q, ‖z‖ ≤ A) :
    Q ⊆ Complex.reProdIm (Icc (-A) A) (Icc (-A) A) := fun z hz =>
  ⟨abs_le.mp ((Complex.abs_re_le_norm z).trans (hA z hz)),
    abs_le.mp ((Complex.abs_im_le_norm z).trans (hA z hz))⟩

/-- The dominating function is integrable on every bounded plane region. -/
theorem integrableOn_dominating_of_isBounded {Q : Set ℂ} (hQ : Bornology.IsBounded Q) (c C : ℝ) :
    IntegrableOn (fun z : ℂ => |Real.log (z.im - c)| + C) Q volume := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le hQ
  exact (integrableOn_dominating c C hA0).mono_set (subset_reProdIm_of_norm_le hA)

theorem integrableOn_logIm_add {Q : Set ℂ} (hQ : Bornology.IsBounded Q) (C : ℝ) :
    IntegrableOn (fun z : ℂ => |Real.log z.im| + C) Q volume := by
  simpa using integrableOn_dominating_of_isBounded hQ 0 C

/-- Rung 1 of this module.  For every parameter `p` and every bounded region `Q` of the
plane, `z ↦ log ‖z - p‖` is integrable on `Q`: the map `p ↦ log ‖· - p‖` lands in `L¹(Q)`. -/
theorem integrableOn_log_norm_sub (p : ℂ) {Q : Set ℂ} (hQ : Bornology.IsBounded Q) :
    IntegrableOn (fun z : ℂ => Real.log ‖z - p‖) Q volume := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le hQ
  refine IntegrableOn.mono_set ?_ (subset_reProdIm_of_norm_le hA)
  set R : ℝ := 2 * A + ‖p‖ + 1 with hR
  refine Integrable.mono' (integrableOn_dominating p.im |Real.log R| hA0)
    (measurable_logKernel_left p).aestronglyMeasurable ?_
  have hSmeas : MeasurableSet (Complex.reProdIm (Icc (-A) A) (Icc (-A) A)) :=
    measurableSet_reProdIm measurableSet_Icc measurableSet_Icc
  have hmem := ae_restrict_mem (μ := (volume : Measure ℂ)) hSmeas
  filter_upwards [hmem, ae_restrict_of_ae (ae_im_ne p.im)] with z hzS hzim
  have hzn : ‖z‖ ≤ 2 * A := by
    have h1 : |z.re| ≤ A := abs_le.mpr hzS.1
    have h2 : |z.im| ≤ A := abs_le.mpr hzS.2
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  have hzR : ‖z - p‖ ≤ R := by
    calc ‖z - p‖ ≤ ‖z‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ R := by rw [hR]; linarith
  simpa [Real.norm_eq_abs] using abs_log_norm_sub_le hzR hzim

/-! ## Continuity of the kernel in the parameter -/

/-- **One dominating function for every nearby real parameter.**  Off the real axis, and for `z`
of norm at most `A`, the difference `log ‖z - p‖ - log ‖z - p₀‖` is bounded by
`2(|log z.im| + |log (A + |p₀| + 1)|)` for every real `p` within `1` of `p₀`.

The bound sees `z` only through its imaginary part and does not see `p` at all, which is what
lets dominated convergence run with no uniform-integrability input.  A real parameter is what
makes this possible: `p.im = 0`, so moving `p` does not move the slice the bound is read on. -/
theorem abs_log_norm_sub_ofReal_sub_le {z : ℂ} (hzim : z.im ≠ 0) {A : ℝ} (hzA : ‖z‖ ≤ A)
    {p₀ p : ℝ} (hp : |p - p₀| < 1) :
    |Real.log ‖z - (p : ℂ)‖ - Real.log ‖z - (p₀ : ℂ)‖|
      ≤ 2 * (|Real.log z.im| + |Real.log (A + |p₀| + 1)|) := by
  set R : ℝ := A + |p₀| + 1 with hR
  have hbnd : ∀ s : ℝ, |s| ≤ |p₀| + 1 →
      |Real.log ‖z - (s : ℂ)‖| ≤ |Real.log z.im| + |Real.log R| := by
    intro s hs
    have hzs : ‖z - (s : ℂ)‖ ≤ R := by
      calc ‖z - (s : ℂ)‖ ≤ ‖z‖ + ‖(s : ℂ)‖ := norm_sub_le _ _
        _ ≤ R := by
            have hsn : ‖(s : ℂ)‖ = |s| := by simp
            rw [hsn, hR]; linarith
    have him : z.im ≠ ((s : ℂ)).im := by simpa using hzim
    simpa using abs_log_norm_sub_le hzs him
  have h1 := hbnd p (by linarith [abs_sub_abs_le_abs_sub p p₀])
  have h2 := hbnd p₀ (by linarith [abs_nonneg p₀])
  calc |Real.log ‖z - (p : ℂ)‖ - Real.log ‖z - (p₀ : ℂ)‖|
      ≤ |Real.log ‖z - (p : ℂ)‖| + |Real.log ‖z - (p₀ : ℂ)‖| := abs_sub _ _
    _ ≤ 2 * (|Real.log z.im| + |Real.log R|) := by linarith


/-- The kernel is continuous in the parameter, measured by the `L¹(Q)` distance.  Both the
convergence and the dominating function come from the slice bound: `|log ‖z - p‖|` is bounded by
`|log z.im| + |log R|` simultaneously for every real `p` in a bounded set, because a real `p` has
`p.im = 0`.  Dominated convergence then needs no uniform-integrability input. -/
theorem tendsto_integral_abs_log_norm_sub {Q : Set ℂ} (hQ : IsCompact Q) (p₀ : ℝ) :
    Tendsto (fun p : ℝ => ∫ z in Q, |Real.log ‖z - (p : ℂ)‖ - Real.log ‖z - (p₀ : ℂ)‖|)
      (𝓝 p₀) (𝓝 0) := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le hQ.isBounded
  set R : ℝ := A + |p₀| + 1 with hR
  have hmemQ := ae_restrict_mem (μ := (volume : Measure ℂ)) hQ.isClosed.measurableSet
  have haeim : ∀ᵐ z : ℂ ∂(volume.restrict Q), z.im ≠ 0 := ae_restrict_of_ae (ae_im_ne 0)
  have hmeas : ∀ p : ℝ, Measurable
      fun z : ℂ => |Real.log ‖z - (p : ℂ)‖ - Real.log ‖z - (p₀ : ℂ)‖| := fun p => by
    simpa [Real.norm_eq_abs] using
      ((measurable_logKernel_left (p : ℂ)).sub (measurable_logKernel_left (p₀ : ℂ))).norm
  have key := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℂ).restrict Q) (l := 𝓝 p₀)
    (F := fun (p : ℝ) (z : ℂ) => |Real.log ‖z - (p : ℂ)‖ - Real.log ‖z - (p₀ : ℂ)‖|)
    (f := fun _ : ℂ => (0 : ℝ))
    (bound := fun z : ℂ => 2 * (|Real.log z.im| + |Real.log R|))
    (Eventually.of_forall fun p => (hmeas p).aestronglyMeasurable)
    ?_ ?_ ?_
  · simpa using key
  · filter_upwards [Metric.ball_mem_nhds p₀ (zero_lt_one (α := ℝ))] with p hp
    have hpp : |p - p₀| < 1 := by simpa [Real.dist_eq] using hp
    filter_upwards [hmemQ, haeim] with z hzQ hzim
    simpa [Real.norm_eq_abs, abs_abs, hR] using
      abs_log_norm_sub_ofReal_sub_le hzim (hA z hzQ) hpp
  · exact (integrableOn_logIm_add hQ.isBounded |Real.log R|).const_mul 2
  · filter_upwards [haeim] with z hzim
    have hc : ContinuousAt
        (fun s : ℝ => |Real.log ‖z - (s : ℂ)‖ - Real.log ‖z - (p₀ : ℂ)‖|) p₀ :=
      (((continuous_logKernel_ofReal hzim).continuousAt).sub continuousAt_const).abs
    simpa [ContinuousAt] using hc

/-- The kernel at parameter `p`, viewed in the Bochner space `L¹(Q)`. -/
noncomputable def logKernelL1 {Q : Set ℂ} (hQ : IsCompact Q) (p : ℝ) :
    Lp ℝ 1 ((volume : Measure ℂ).restrict Q) :=
  MemLp.toLp _
    (memLp_one_iff_integrable.mpr (integrableOn_log_norm_sub (p : ℂ) hQ.isBounded))

theorem norm_toLp_eq {μ : Measure ℂ} {f : ℂ → ℝ} (hf : MemLp f 1 μ) :
    ‖hf.toLp f‖ = ∫ z, |f z| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hf.coeFn_toLp.mono fun z hz => by simp [hz, Real.norm_eq_abs])

theorem dist_logKernelL1 {Q : Set ℂ} (hQ : IsCompact Q) (p q : ℝ) :
    dist (logKernelL1 hQ p) (logKernelL1 hQ q)
      = ∫ z in Q, |Real.log ‖z - (p : ℂ)‖ - Real.log ‖z - (q : ℂ)‖| := by
  have hp : MemLp (fun z : ℂ => Real.log ‖z - (p : ℂ)‖) 1 ((volume : Measure ℂ).restrict Q) :=
    memLp_one_iff_integrable.mpr (integrableOn_log_norm_sub (p : ℂ) hQ.isBounded)
  have hq : MemLp (fun z : ℂ => Real.log ‖z - (q : ℂ)‖) 1 ((volume : Measure ℂ).restrict Q) :=
    memLp_one_iff_integrable.mpr (integrableOn_log_norm_sub (q : ℂ) hQ.isBounded)
  have h : logKernelL1 hQ p - logKernelL1 hQ q = (hp.sub hq).toLp _ := rfl
  rw [dist_eq_norm, h, norm_toLp_eq]
  rfl

/-- Rung 2 of this module: `p ↦ log ‖· - p‖` is a continuous curve in `L¹(Q)`. -/
theorem continuous_logKernelL1 {Q : Set ℂ} (hQ : IsCompact Q) :
    Continuous (logKernelL1 hQ) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simpa only [dist_logKernelL1] using tendsto_integral_abs_log_norm_sub hQ p₀

/-- The second assertion of this module: the image of the parameter interval is a
compact subset of `L¹(Q)`. -/
theorem isCompact_image_logKernelL1 {Q : Set ℂ} (hQ : IsCompact Q) :
    IsCompact (logKernelL1 hQ '' Icc (0 : ℝ) 1) :=
  isCompact_Icc.image (continuous_logKernelL1 hQ)

/-! ## Convergence of the potentials -/

theorem measurable_logKernel_uncurry :
    Measurable fun q : ℂ × ℝ => Real.log ‖q.1 - (q.2 : ℂ)‖ :=
  Real.measurable_log.comp
    (measurable_fst.sub ((Complex.continuous_ofReal.measurable).comp measurable_snd)).norm

/-- The potential is a measurable function of the evaluation point. -/
theorem measurable_logPotential (ν : Measure ℝ) [SFinite ν] : Measurable (logPotential ν) :=
  (measurable_logKernel_uncurry.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

/-- On a region of radius `A` the whole parameter interval is within `A + 1`, which is the radius
the slice bound is applied at throughout. -/
theorem norm_sub_le_of_mem_Icc {Q : Set ℂ} {A : ℝ} (hA : ∀ z ∈ Q, ‖z‖ ≤ A) {z : ℂ} (hz : z ∈ Q)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : ‖z - (p : ℂ)‖ ≤ A + 1 := by
  have hp1 : |p| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
  have hnp : ‖(p : ℂ)‖ = |p| := by simp
  calc ‖z - (p : ℂ)‖ ≤ ‖z‖ + ‖(p : ℂ)‖ := norm_sub_le _ _
    _ ≤ A + 1 := by rw [hnp]; linarith [hA z hz]

/-- The slice bound passes from the kernel to the potential: a probability measure on `[0,1]`
integrates the kernel against a bound that is the same for every such measure. -/
theorem abs_logPotential_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0) {z : ℂ} (hz : z.im ≠ 0) {R : ℝ}
    (hR : ∀ p ∈ Icc (0 : ℝ) 1, ‖z - (p : ℂ)‖ ≤ R) :
    |logPotential ν z| ≤ |Real.log z.im| + |Real.log R| := by
  have hint : Integrable (fun p : ℝ => Real.log ‖z - (p : ℂ)‖) ν :=
    integrable_of_measure_compl_eq_zero hν (continuous_logKernel_ofReal hz)
  have hbound := abs_integral_sub_integral_le (a := 0) (b := 1) hν hint
    (integrable_zero ℝ ℝ ν) (C := |Real.log z.im| + |Real.log R|) fun p hp => by
      simpa using abs_log_norm_sub_le (hR p hp) (by simpa using hz)
  simpa [logPotential] using hbound

/-- The potential of a probability measure on `[0,1]` is itself in `L¹(Q)` for every compact `Q`,
including a `Q` that meets the segment, where the potential is unbounded.  Without this the
convergence below would be convergence of a bare integral rather than convergence in `L¹(Q)`. -/
theorem integrableOn_logPotential {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    IntegrableOn (logPotential ν) Q volume := by
  obtain ⟨A, _, hA⟩ := exists_norm_le hQ.isBounded
  refine Integrable.mono' (integrableOn_logIm_add hQ.isBounded |Real.log (A + 1)|)
    (measurable_logPotential ν).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℂ)) hQ.isClosed.measurableSet,
    ae_restrict_of_ae (ae_im_ne 0)] with z hzQ hzim
  simpa [Real.norm_eq_abs] using
    abs_logPotential_le hν hzim fun p hp => norm_sub_le_of_mem_Icc hA hzQ hp

/-- The easy, pointwise half of the `L¹` statement.  Off the real axis the kernel is a
continuous function of the parameter on the whole line, so weak convergence of the measures gives
convergence of the potentials at that point with no integrability argument at all. -/
theorem tendsto_logPotential_of_tendsto {ι : Type*} {L : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ i, (μs i : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0) (hlim : Tendsto μs L (𝓝 μ))
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun i => logPotential (μs i) z) L (𝓝 (logPotential μ z)) := by
  exact tendsto_integral_of_tendsto zero_le_one hμs hμ hlim (continuous_logKernel_ofReal hz)

/-- **The pointwise statement off the carrying segment.**  `tendsto_logPotential_of_tendsto`
asks for `z` off the *real axis*, which is more than the kernel needs: what makes
`p ↦ log ‖z - p‖` continuous where the measures live is that `z` avoids `[0,1]`, and a real `z`
outside the segment is as good as a complex one.

The kernel is only continuous away from `p = z`, so it is composed with the retraction
`clampIcc 0 1` before the weak-convergence test function is formed.  That changes nothing the
measures see -- they are carried by `[0,1]`, where the retraction is the identity -- and it makes
the test function continuous on the whole line. -/
theorem tendsto_logPotential_of_tendsto_of_notMem {ι : Type*} {L : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ i, (μs i : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0) (hlim : Tendsto μs L (𝓝 μ))
    {z : ℂ} (hz : ∀ t ∈ Icc (0 : ℝ) 1, z ≠ (t : ℂ)) :
    Tendsto (fun i => logPotential (μs i) z) L (𝓝 (logPotential μ z)) := by
  set g : ℝ → ℝ := fun p => Real.log ‖z - ((clampIcc 0 1 p : ℝ) : ℂ)‖ with hg
  have hne : ∀ p : ℝ, ‖z - ((clampIcc 0 1 p : ℝ) : ℂ)‖ ≠ 0 := by
    intro p h
    exact hz _ (clampIcc_mem_Icc zero_le_one p) (sub_eq_zero.mp (norm_eq_zero.mp h))
  have hgc : Continuous g :=
    ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_clampIcc)).norm).log hne
  have hswap : ∀ ν : Measure ℝ, ∀ _ : IsProbabilityMeasure ν, ν (Icc (0 : ℝ) 1)ᶜ = 0 →
      ∫ p, g p ∂ν = logPotential ν z := fun ν _ hν =>
    integral_congr_of_eqOn hν fun p hp => by rw [hg]; simp only []; rw [clampIcc_eq_self hp]
  have h := tendsto_integral_of_tendsto zero_le_one hμs hμ hlim hgc
  rw [hswap (μ : Measure ℝ) inferInstance hμ] at h
  refine h.congr fun i => hswap (μs i : Measure ℝ) inferInstance (hμs i)

/-- the `L¹` statement.  Weak convergence of probability measures on `[0,1]` carries their
logarithmic potentials to the limit potential in `L¹(Q)`, for every compact `Q ⊆ ℂ` — including
the part of `Q` that meets the segment, where the potentials are unbounded.  The route is
dominated convergence in `z` against the slice bound, so no Bochner integral of an
`L¹(Q)`-valued curve and no vector-valued portmanteau theorem enters. -/
theorem tendsto_integral_abs_logPotential_sub {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ i, (μs i : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0) (hlim : Tendsto μs L (𝓝 μ))
    {Q : Set ℂ} (hQ : IsCompact Q) :
    Tendsto (fun i => ∫ z in Q, |logPotential (μs i) z - logPotential μ z|) L (𝓝 0) := by
  obtain ⟨A, _, hA⟩ := exists_norm_le hQ.isBounded
  set R : ℝ := A + 1 with hR
  have hRle : ∀ z ∈ Q, ∀ p ∈ Icc (0 : ℝ) 1, ‖z - (p : ℂ)‖ ≤ R := fun z hz p hp => by
    rw [hR]; exact norm_sub_le_of_mem_Icc hA hz hp
  have hmemQ := ae_restrict_mem (μ := (volume : Measure ℂ)) hQ.isClosed.measurableSet
  have haeim : ∀ᵐ z : ℂ ∂((volume : Measure ℂ).restrict Q), z.im ≠ 0 :=
    ae_restrict_of_ae (ae_im_ne 0)
  have hmeas : ∀ i : ι, Measurable
      fun z : ℂ => |logPotential (μs i) z - logPotential μ z| := fun i => by
    simpa [Real.norm_eq_abs] using
      ((measurable_logPotential (μs i : Measure ℝ)).sub
        (measurable_logPotential (μ : Measure ℝ))).norm
  have key := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℂ).restrict Q) (l := L)
    (F := fun (i : ι) (z : ℂ) => |logPotential (μs i) z - logPotential μ z|)
    (f := fun _ : ℂ => (0 : ℝ))
    (bound := fun z : ℂ => 2 * (|Real.log z.im| + |Real.log R|))
    (Eventually.of_forall fun i => (hmeas i).aestronglyMeasurable) ?_ ?_ ?_
  · simpa using key
  · refine Eventually.of_forall fun i => ?_
    filter_upwards [hmemQ, haeim] with z hzQ hzim
    have h1 := abs_logPotential_le (hμs i) hzim (hRle z hzQ)
    have h2 := abs_logPotential_le hμ hzim (hRle z hzQ)
    simp only [Real.norm_eq_abs, abs_abs]
    calc |logPotential (μs i) z - logPotential μ z|
        ≤ |logPotential (μs i) z| + |logPotential μ z| := abs_sub _ _
      _ ≤ 2 * (|Real.log z.im| + |Real.log R|) := by linarith
  · exact (integrableOn_logIm_add hQ.isBounded |Real.log R|).const_mul 2
  · filter_upwards [haeim] with z hzim
    simpa [Real.dist_eq] using
      tendsto_iff_dist_tendsto_zero.mp (tendsto_logPotential_of_tendsto hμs hμ hlim hzim)


/-! ### Axiom footprint -/

/-- info: 'Shields.logPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logPotential

/-- info: 'Shields.logKernelL1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logKernelL1

end Shields
