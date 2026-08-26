/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Weak convergence and moments for measures on a compact interval

The Hausdorff moment problem on a compact interval, in the form these papers' weak-limit
arguments consume.  Mathlib carries Prokhorov's theorem, the Levy--Prokhorov metric and the
Weierstrass approximation theorem, but not the statement that on a fixed compact interval weak
convergence and convergence of all moments are the same thing, nor that a measure there is
determined by its moments.

Everything is stated for probability measures on `ℝ` that charge nothing outside `[a, b]`,
rather than for measures on the subtype, because that is how the callers hold them and it keeps
the pushforwards out of the statements.

## Main definitions

* `Shields.clampIcc`: the retraction `x ↦ max a (min b x)` of the line onto `[a, b]`, used to
  turn an unbounded continuous integrand into a bounded one without changing any integral
  against a measure concentrated on the interval.

## Main statements

* `Shields.tendsto_integral_of_tendsto`: weak convergence of probability measures concentrated
  on a fixed compact interval carries convergence of the integral of every continuous function,
  bounded or not.
* `Shields.tendsto_of_tendsto_integral_pow`, `Shields.tendsto_iff_tendsto_integral_pow`:
  **moment convergence is weak convergence** on a compact interval.  The forward direction is
  Weierstrass approximation against the uniform norm; the converse is the display above.
* `Shields.eq_of_forall_integral_pow_eq`: **Hausdorff determinacy** -- two probability measures
  on a compact interval with the same moments are equal.
* `Shields.isCompact_setOf_measure_compl_eq_zero`, `Shields.exists_subseq_tendsto`: Prokhorov
  with a constant exhaustion, and the subsequence it yields.
* `Shields.exists_tendsto_of_forall_exists_tendsto_integral_pow`: if every moment sequence
  converges, the measures converge weakly to a probability measure on the same interval -- with
  no limit measure presupposed.

## Tags

weak convergence, moment problem, Hausdorff moments, Prokhorov, Weierstrass approximation
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Polynomial BoundedContinuousFunction

namespace Shields

variable {a b : ℝ}

/-! ## Measures concentrated on an interval -/

theorem ae_mem_of_measure_compl_eq_zero {ν : Measure ℝ} {s : Set ℝ} (h : ν sᶜ = 0) :
    ∀ᵐ x ∂ν, x ∈ s :=
  mem_ae_iff.mpr h

/-- The converse: the two ways of saying a measure is carried by a set agree.  `Shields.
Stability` writes its concentration hypotheses in the `∀ᵐ` form and this file in the null-set
form, and this is the translation between them. -/
theorem measure_compl_eq_zero_of_ae_mem {ν : Measure ℝ} {s : Set ℝ} (h : ∀ᵐ x ∂ν, x ∈ s) :
    ν sᶜ = 0 :=
  mem_ae_iff.mp h

/-- Every function continuous on the interval is integrable against a probability measure that
charges nothing outside it: off the interval the values are irrelevant, and the interval is
compact, so they are bounded where they matter. -/
theorem integrable_of_measure_compl_eq_zero {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc a b)ᶜ = 0) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f ν := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := f) hf.continuousOn
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  filter_upwards [ae_mem_of_measure_compl_eq_zero hν] with x hx using hC x hx

/-- Two integrals against a measure concentrated on the interval differ by at most a bound that
holds on the interval alone. -/
theorem abs_integral_sub_integral_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc a b)ᶜ = 0) {f g : ℝ → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    {C : ℝ} (h : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ C) :
    |∫ x, f x ∂ν - ∫ x, g x ∂ν| ≤ C := by
  rw [← integral_sub hf hg]
  calc |∫ x, (f x - g x) ∂ν| = ‖∫ x, (f x - g x) ∂ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ C * ν.real univ := by
        refine norm_integral_le_of_norm_le_const ?_
        filter_upwards [ae_mem_of_measure_compl_eq_zero hν] with x hx
        simpa using h x hx
    _ = C := by simp

/-- Two integrals against measures concentrated on the interval agree whenever the integrands do
so on the interval. -/
theorem integral_congr_of_eqOn {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc a b)ᶜ = 0) {f g : ℝ → ℝ} (h : ∀ x ∈ Set.Icc a b, f x = g x) :
    ∫ x, f x ∂ν = ∫ x, g x ∂ν := by
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_of_measure_compl_eq_zero hν] with x hx using h x hx

/-! ## Moments and polynomials -/

/-- The integral of a polynomial against a measure concentrated on the interval is the
corresponding combination of moments. -/
theorem integral_polynomial_eq_sum {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Set.Icc a b)ᶜ = 0) (p : ℝ[X]) :
    ∫ x, p.eval x ∂ν = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * ∫ x, x ^ k ∂ν := by
  have hint : ∀ k ∈ Finset.range (p.natDegree + 1),
      Integrable (fun x : ℝ => p.coeff k * x ^ k) ν := fun k _ =>
    integrable_of_measure_compl_eq_zero hν (by fun_prop)
  calc ∫ x, p.eval x ∂ν
      = ∫ x, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * x ^ k ∂ν := by
        simp_rw [← Polynomial.eval_eq_sum_range]
    _ = ∑ k ∈ Finset.range (p.natDegree + 1), ∫ x, p.coeff k * x ^ k ∂ν :=
        integral_finsetSum _ hint
    _ = _ := by simp_rw [integral_const_mul]

/-- Convergence of every moment carries convergence of the integral of every polynomial. -/
theorem tendsto_integral_polynomial {ι : Type*} {L : Filter ι} {νs : ι → Measure ℝ} {ν : Measure ℝ}
    [∀ i, IsProbabilityMeasure (νs i)] [IsProbabilityMeasure ν]
    (hνs : ∀ i, νs i (Set.Icc a b)ᶜ = 0) (hν : ν (Set.Icc a b)ᶜ = 0)
    (hmom : ∀ k : ℕ, Tendsto (fun i => ∫ x, x ^ k ∂(νs i)) L (𝓝 (∫ x, x ^ k ∂ν)))
    (p : ℝ[X]) :
    Tendsto (fun i => ∫ x, p.eval x ∂(νs i)) L (𝓝 (∫ x, p.eval x ∂ν)) := by
  simp_rw [fun i => integral_polynomial_eq_sum (hνs i) p, integral_polynomial_eq_sum hν p]
  exact tendsto_finsetSum _ fun k _ => (hmom k).const_mul _

/-! ## Moment convergence implies weak convergence -/

/-- Convergence of every moment implies weak convergence, for probability measures charging
nothing outside a fixed compact interval.  Weierstrass approximation on the interval turns a
bounded continuous test function into a polynomial, and `tendsto_integral_polynomial` handles
the polynomial. -/
theorem tendsto_of_tendsto_integral_pow {ι : Type*} {L : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ i, (μs i : Measure ℝ) (Set.Icc a b)ᶜ = 0)
    (hμ : (μ : Measure ℝ) (Set.Icc a b)ᶜ = 0)
    (hmom : ∀ k : ℕ, Tendsto (fun i => ∫ x, x ^ k ∂(μs i : Measure ℝ)) L
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ)))) :
    Tendsto μs L (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f f.continuous.continuousOn
    (ε / 4) (by positivity)
  have hnear : ∀ ν : Measure ℝ, ∀ _ : IsProbabilityMeasure ν, ν (Set.Icc a b)ᶜ = 0 →
      |∫ x, f x ∂ν - ∫ x, p.eval x ∂ν| ≤ ε / 4 := by
    intro ν _ hν
    refine abs_integral_sub_integral_le hν
      (integrable_of_measure_compl_eq_zero hν f.continuous)
      (integrable_of_measure_compl_eq_zero hν (by fun_prop)) fun x hx => ?_
    rw [abs_sub_comm]
    exact (hp x hx).le
  have hpoly := tendsto_integral_polynomial (νs := fun i => (μs i : Measure ℝ)) hμs hμ hmom p
  rw [Metric.tendsto_nhds] at hpoly
  filter_upwards [hpoly (ε / 4) (by positivity)] with i hi
  rw [Real.dist_eq] at hi ⊢
  have h₁ := hnear _ inferInstance (hμs i)
  have h₂ := hnear _ inferInstance hμ
  have t₁ := abs_sub_le (∫ x, f x ∂(μs i : Measure ℝ)) (∫ x, p.eval x ∂(μs i : Measure ℝ))
    (∫ x, f x ∂(μ : Measure ℝ))
  have t₂ := abs_sub_le (∫ x, p.eval x ∂(μs i : Measure ℝ)) (∫ x, p.eval x ∂(μ : Measure ℝ))
    (∫ x, f x ∂(μ : Measure ℝ))
  have t₃ : |∫ x, p.eval x ∂(μ : Measure ℝ) - ∫ x, f x ∂(μ : Measure ℝ)|
      = |∫ x, f x ∂(μ : Measure ℝ) - ∫ x, p.eval x ∂(μ : Measure ℝ)| := abs_sub_comm _ _
  linarith

/-- Two probability measures concentrated on the same compact interval with the same moments are
equal: the uniqueness half of the Hausdorff moment problem. -/
theorem eq_of_forall_integral_pow_eq {μ ν : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) (Set.Icc a b)ᶜ = 0) (hν : (ν : Measure ℝ) (Set.Icc a b)ᶜ = 0)
    (h : ∀ k : ℕ, ∫ x, x ^ k ∂(μ : Measure ℝ) = ∫ x, x ^ k ∂(ν : Measure ℝ)) : μ = ν := by
  have hlim : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) :=
    tendsto_of_tendsto_integral_pow (fun _ => hμ) hν fun k => by
      simp only [h k]
      exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-! ## Weak convergence implies moment convergence -/

/-- The clamp of the line onto `[a, b]`, used to replace a continuous function by a bounded one
without changing any integral against a measure concentrated on the interval. -/
noncomputable def clampIcc (a b x : ℝ) : ℝ := max a (min b x)

theorem continuous_clampIcc : Continuous (clampIcc a b) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampIcc_mem_Icc (hab : a ≤ b) (x : ℝ) : clampIcc a b x ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clampIcc_eq_self {x : ℝ} (hx : x ∈ Set.Icc a b) : clampIcc a b x = x := by
  rw [clampIcc, min_eq_right hx.2, max_eq_right hx.1]

/-- Weak convergence of probability measures concentrated on a fixed compact interval carries
convergence of the integral of every continuous function, bounded or not.  Off the interval the
integrand can be clamped away without changing any of the integrals. -/
theorem tendsto_integral_of_tendsto {ι : Type*} {L : Filter ι} (hab : a ≤ b)
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ i, (μs i : Measure ℝ) (Set.Icc a b)ᶜ = 0)
    (hμ : (μ : Measure ℝ) (Set.Icc a b)ᶜ = 0)
    (hlim : Tendsto μs L (𝓝 μ)) {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun i => ∫ x, g x ∂(μs i : Measure ℝ)) L (𝓝 (∫ x, g x ∂(μ : Measure ℝ))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := g) hg.continuousOn
  let G : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (g ∘ clampIcc a b)
    (hg.comp continuous_clampIcc) C fun x => hC _ (clampIcc_mem_Icc hab x)
  have hGval : ∀ x, G x = g (clampIcc a b x) := fun _ => rfl
  have hswap : ∀ ν : Measure ℝ, ∀ _ : IsProbabilityMeasure ν, ν (Set.Icc a b)ᶜ = 0 →
      ∫ x, G x ∂ν = ∫ x, g x ∂ν := fun ν _ hν =>
    integral_congr_of_eqOn hν fun x hx => by rw [hGval, clampIcc_eq_self hx]
  have hbcf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) G
  have hfun : (fun i => ∫ x, G x ∂(μs i : Measure ℝ))
      = fun i => ∫ x, g x ∂(μs i : Measure ℝ) :=
    funext fun i => hswap _ inferInstance (hμs i)
  rw [hfun, hswap _ inferInstance hμ] at hbcf
  exact hbcf

/-- On a fixed compact interval, weak convergence and convergence of all moments are the same
thing. -/
theorem tendsto_iff_tendsto_integral_pow {ι : Type*} {L : Filter ι} (hab : a ≤ b)
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ i, (μs i : Measure ℝ) (Set.Icc a b)ᶜ = 0)
    (hμ : (μ : Measure ℝ) (Set.Icc a b)ᶜ = 0) :
    Tendsto μs L (𝓝 μ) ↔ ∀ k : ℕ, Tendsto (fun i => ∫ x, x ^ k ∂(μs i : Measure ℝ)) L
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ))) :=
  ⟨fun h k => tendsto_integral_of_tendsto hab hμs hμ h (by fun_prop),
    tendsto_of_tendsto_integral_pow hμs hμ⟩

/-! ## Compactness -/

/-- The probability measures on the line charging nothing outside a fixed compact set form a
compact subset of `ProbabilityMeasure ℝ`.  Prokhorov's theorem with a constant exhaustion. -/
theorem isCompact_setOf_measure_compl_eq_zero {K : Set ℝ} (hK : IsCompact K) :
    IsCompact {ν : ProbabilityMeasure ℝ | (ν : Measure ℝ) Kᶜ = 0} := by
  have h := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (E := ℝ) (u := fun _ : ℕ => (0 : ℝ≥0)) (K := fun _ => K) tendsto_const_nhds
    (fun _ => hK) (Or.inr monotone_const)
  have hset : {ν : ProbabilityMeasure ℝ | (ν : Measure ℝ) Kᶜ = 0}
      = {ν : ProbabilityMeasure ℝ | ∀ _ : ℕ, ν Kᶜ ≤ (0 : ℝ≥0)} := by
    ext ν
    simp [← ProbabilityMeasure.null_iff_toMeasure_null]
  rw [hset]
  exact h

/-- Every sequence of probability measures charging nothing outside a fixed compact set has a
weakly convergent subsequence whose limit charges nothing outside it either. -/
theorem exists_subseq_tendsto {K : Set ℝ} (hK : IsCompact K) (μs : ℕ → ProbabilityMeasure ℝ)
    (h : ∀ n, (μs n : Measure ℝ) Kᶜ = 0) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ (μ : Measure ℝ) Kᶜ = 0 ∧
      Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  obtain ⟨μ, hmem, φ, hφ, hlim⟩ := (isCompact_setOf_measure_compl_eq_zero hK).tendsto_subseq h
  exact ⟨μ, φ, hφ, hmem, hlim⟩

/-- Existence: if every moment sequence converges, the measures converge weakly to a probability
measure on the same interval.  Compactness supplies a candidate along a subsequence, and
`eq_of_forall_integral_pow_eq` forces every subsequential limit to be that candidate. -/
theorem exists_tendsto_of_forall_exists_tendsto_integral_pow (hab : a ≤ b)
    {μs : ℕ → ProbabilityMeasure ℝ} (hμs : ∀ n, (μs n : Measure ℝ) (Set.Icc a b)ᶜ = 0)
    (hmom : ∀ k : ℕ, ∃ c : ℝ, Tendsto (fun n => ∫ x, x ^ k ∂(μs n : Measure ℝ)) atTop (𝓝 c)) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Set.Icc a b)ᶜ = 0 ∧ Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨μ, φ, hφ, hμ, hlim⟩ := exists_subseq_tendsto isCompact_Icc μs hμs
  refine ⟨μ, hμ, tendsto_of_tendsto_integral_pow hμs hμ fun k => ?_⟩
  obtain ⟨c, hc⟩ := hmom k
  have hsub : Tendsto (fun n => ∫ x, x ^ k ∂(μs (φ n) : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ))) :=
    tendsto_integral_of_tendsto hab (fun n => hμs (φ n)) hμ hlim (by fun_prop)
  have : c = ∫ x, x ^ k ∂(μ : Measure ℝ) :=
    tendsto_nhds_unique (hc.comp hφ.tendsto_atTop) hsub
  rwa [← this]

end Shields
