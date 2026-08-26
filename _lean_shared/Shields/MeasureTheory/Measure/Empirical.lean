/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Support
import Shields.Analysis.Complex.LogPotential

/-!
# The empirical measure of a finite family of points

The **empirical measure** of a finite family `\rho : Fin m \to \mathbb{R}` is the normalized
counting measure `m^{-1}\sum_j \delta_{\rho j}`.  It is the object that turns a statement about
`m` points into a statement about a probability measure, so that limits of point configurations
can be taken weakly.

Everything here is elementary and unconditional.  Integration against it is the normalized sum,
so no integrability hypothesis is ever needed; it is invariant under relabelling; it pushes
forward along a measurable map to the empirical measure of the transported points; and it
charges nothing outside any measurable set containing the points, hence is supported in any
closed one.

Two facts about weak limits are included because they are what the empirical measure is usually
carried into: a closed set carrying full mass along a weakly convergent sequence carries full
mass in the limit, and the support containment therefore passes to the limit.  Both are
consequences of the portmanteau theorem.

## Main results

* `Shields.empirical`, `Shields.empirical_apply`, `Shields.isProbabilityMeasure_empirical`
* `Shields.integral_empirical` — integration is the normalized sum, with no hypothesis on `f`
* `Shields.map_empirical`, `Shields.empirical_comp_perm`
* `Shields.empirical_compl_eq_zero`, `Shields.support_empirical_subset`
* `Shields.logPotential_empirical` — the normalized log-modulus of a monic product is the
  logarithmic potential of the empirical measure of its roots
* `Shields.measure_eq_one_of_tendsto`, `Shields.support_subset_of_tendsto`

## Implementation notes

The measure is defined on `\mathbb{R}` rather than on a subtype of it, so that a family whose
points happen to lie in an interval and one whose points do not are the same kind of object, and
so that pushforwards along maps of the line are available without transporting the ambient space.
Support statements then take the containing set as a hypothesis.

## References

* P. Billingsley, *Convergence of probability measures*, 2nd ed., Wiley, 1999.

## Tags

empirical measure, counting measure, portmanteau, weak convergence, logarithmic potential
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Shields

/-- The **empirical measure** of a finite family of real points, listed with multiplicity: the
normalized counting measure `m^{-1}\sum_j\delta_{\rho j}`. -/
noncomputable def empirical {m : ℕ} (ρ : Fin m → ℝ) : Measure ℝ :=
  (m : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (ρ j)

theorem empirical_apply {m : ℕ} (ρ : Fin m → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    empirical ρ s = (m : ℝ≥0∞)⁻¹ * ∑ j, s.indicator (1 : ℝ → ℝ≥0∞) (ρ j) := by
  simp only [empirical, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs]

theorem isProbabilityMeasure_empirical {m : ℕ} (hm : m ≠ 0) (ρ : Fin m → ℝ) :
    IsProbabilityMeasure (empirical ρ) := by
  constructor
  rw [empirical_apply _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hm) (by simp)

/-- Integration against an empirical measure is the normalized sum over the roots.  No
hypothesis on `f`: every function is integrable against a Dirac measure on a space whose
singletons are measurable. -/
theorem integral_empirical {m : ℕ} (ρ : Fin m → ℝ) (f : ℝ → ℝ) :
    ∫ p, f p ∂(empirical ρ) = (m : ℝ)⁻¹ * ∑ j, f (ρ j) := by
  rw [empirical, integral_smul_measure,
    integral_finsetSum_measure (fun j _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- Pushing an empirical measure forward along a measurable map is the empirical measure of the
transported roots. -/
theorem map_empirical {m : ℕ} (ρ : Fin m → ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    (empirical ρ).map g = empirical (g ∘ ρ) := by
  ext s hs
  rw [Measure.map_apply hg hs, empirical_apply _ (hg hs), empirical_apply _ hs]
  have hind : ∀ j : Fin m, (g ⁻¹' s).indicator (1 : ℝ → ℝ≥0∞) (ρ j)
      = s.indicator (1 : ℝ → ℝ≥0∞) (g (ρ j)) := fun j => by
    by_cases hj : g (ρ j) ∈ s <;> simp [hj]
  simp only [Function.comp_apply, hind]

/-- Relabelling the points leaves the empirical measure unchanged, so it depends only on the
multiset of points. -/
theorem empirical_comp_perm {m : ℕ} (ρ : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    empirical (ρ ∘ σ) = empirical ρ := by
  simp only [empirical]
  congr 1
  exact Fintype.sum_equiv σ _ _ fun j => rfl

/-- For a monic product over a finite family of real roots, the normalized logarithm of its
modulus is exactly the logarithmic potential of the empirical measure of those roots, away from
them. -/
theorem logPotential_empirical {m : ℕ} (ρ : Fin m → ℝ) {z : ℂ} (hz : ∀ j, z ≠ (ρ j : ℂ)) :
    logPotential (empirical ρ) z = (m : ℝ)⁻¹ * Real.log ‖∏ j, (z - (ρ j : ℂ))‖ := by
  rw [logPotential, integral_empirical ρ _, norm_prod,
    Real.log_prod fun j _ => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz j))]

/-- An empirical measure charges nothing outside a measurable set containing its roots. -/
theorem empirical_compl_eq_zero {m : ℕ} {ρ : Fin m → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ j, ρ j ∈ s) : empirical ρ sᶜ = 0 := by
  rw [empirical_apply _ hs.compl]
  have hz : ∀ j : Fin m, (sᶜ).indicator (1 : ℝ → ℝ≥0∞) (ρ j) = 0 := fun j => by
    simp [h j]
  simp [hz]

/-- Points in a closed set give an empirical measure supported there. -/
theorem support_empirical_subset {m : ℕ} {ρ : Fin m → ℝ} {s : Set ℝ} (hs : IsClosed s)
    (h : ∀ j, ρ j ∈ s) : (empirical ρ).support ⊆ s :=
  Measure.support_subset_of_isClosed hs
    (mem_ae_iff.mpr (empirical_compl_eq_zero hs.measurableSet h))

/-- Points in an open interval give an empirical measure supported in its closure. -/
theorem support_empirical_subset_Icc {m : ℕ} {ρ : Fin m → ℝ} {a b : ℝ}
    (h : ∀ j, ρ j ∈ Set.Ioo a b) : (empirical ρ).support ⊆ Set.Icc a b :=
  support_empirical_subset isClosed_Icc fun j => Set.Ioo_subset_Icc_self (h j)

/-- A closed set carrying full mass along a weakly convergent sequence carries full mass in the
limit.  One implication of the portmanteau theorem. -/
theorem measure_eq_one_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} (hlim : Tendsto μs L (𝓝 μ))
    {F : Set ℝ} (hF : IsClosed F) (hone : ∀ i, (μs i : Measure ℝ) F = 1) :
    (μ : Measure ℝ) F = 1 := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  simp only [hone, limsup_const] at h
  exact le_antisymm prob_le_one h

/-- Support containment passes to a weak limit: if every member of a weakly convergent sequence
sits on a closed set, so does the limit. -/
theorem support_subset_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} (hlim : Tendsto μs L (𝓝 μ))
    {F : Set ℝ} (hF : IsClosed F) (hone : ∀ i, (μs i : Measure ℝ) F = 1) :
    (μ : Measure ℝ).support ⊆ F := by
  refine Measure.support_subset_of_isClosed hF (mem_ae_iff.mpr ?_)
  rw [measure_compl hF.measurableSet (measure_ne_top _ _), measure_univ,
    measure_eq_one_of_tendsto hlim hF hone, tsub_self]

end Shields
