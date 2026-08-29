/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral

/-!
# The complex polar chart on an annulus

`Complex.integral_comp_polarCoord_symm` carries an integral over the whole plane into polar
coordinates.  Three things separate it from the form an annulus integral is read in, and each is
supplied here.

* **The chart is centered at the origin**, and an annulus about `a` is not.  Translation is
  volume-preserving, so the recentering costs nothing.
* **The radius is unrestricted.**  Cutting it to `(ε, R)` with `ε > 0` makes the polar region the
  product set `(ε, R) × (-π, π)`, which is what lets Fubini separate the radius from the angle.
* **The chart's angular range is `(-π, π)`**, while a circle integral runs over `(0, 2π)`.  The
  integrand is `2π`-periodic in the angle, so the two ranges give the same value.

The positive inner radius is what keeps the origin — the one point where the chart degenerates —
out of the region, and it is also what makes the Jacobian `r` bounded away from zero there.

## Main results

* `polarCoord_symm_eq_circleMap`, `add_polarCoord_symm_eq_circleMap` — the chart is `circleMap`.
* `norm_polarCoord_symm_of_pos` — on a positive radius the chart has norm exactly that radius.
* `continuous_polarCoord_symm_complex` — the chart's inverse is continuous.
* `setIntegral_annulus_polarCoord_symm` — **the change of variables on an annulus**, centered and
  cut.
* `integral_Ioo_polarCoord_symm_eq_circleMap` — **the angular range moved** from the chart's to
  the circle's.

## Tags

polar coordinates, annulus, change of variables, circle map, periodic
-/

open scoped Real
open Complex MeasureTheory Set

namespace Shields

/-! ### The chart -/

theorem polarCoord_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  simp [circleMap, Complex.exp_mul_I]

theorem add_polarCoord_symm_eq_circleMap (a : ℂ) (r θ : ℝ) :
    a + Complex.polarCoord.symm (r, θ) = circleMap a r θ := by
  simp [circleMap, Complex.exp_mul_I]

/-- On a positive radius the polar chart has norm exactly that radius. -/
theorem norm_polarCoord_symm_of_pos {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖Complex.polarCoord.symm ((r, θ) : ℝ × ℝ)‖ = r := by
  rw [Complex.norm_polarCoord_symm]
  exact abs_of_pos hr

theorem continuous_polarCoord_symm_complex :
    Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

/-! ### The change of variables -/

/-- **The polar change of variables on an annulus.**  `Complex.integral_comp_polarCoord_symm`
integrates over the whole plane from the origin; what is added is the center `a` and the cut
`ε < r < R`, which turns the polar region into a product set. -/
theorem setIntegral_annulus_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (a : ℂ) {ε R : ℝ} (hε : 0 < ε) :
    (∫ z in {z : ℂ | ε < ‖z - a‖ ∧ ‖z - a‖ < R}, f z)
      = ∫ p in (Set.Ioo ε R) ×ˢ (Set.Ioo (-π) π), p.1 • f (a + Complex.polarCoord.symm p) := by
  set A₀ : Set ℂ := {z : ℂ | ε < ‖z‖ ∧ ‖z‖ < R} with hA₀def
  have hA₀ : MeasurableSet A₀ :=
    (((isOpen_lt continuous_const continuous_norm).and
      (isOpen_lt continuous_norm continuous_const))).measurableSet
  -- Center the annulus; translation preserves volume.
  have step1 : (∫ z in {z : ℂ | ε < ‖z - a‖ ∧ ‖z - a‖ < R}, f z) = ∫ z in A₀, f (a + z) := by
    rw [← (measurePreserving_add_left (volume : Measure ℂ) a).setIntegral_preimage_emb
      (measurableEmbedding_addLeft a) f {z : ℂ | ε < ‖z - a‖ ∧ ‖z - a‖ < R}]
    congr 1
    ext z
    simp [hA₀def]
  -- Cut the radius; the polar region factors as a product set.
  have hsub : Set.Ioo ε R ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans hε hs.1
  have hcong : ∀ p ∈ (Set.Ioi (0 : ℝ)) ×ˢ (Set.Ioo (-π) π),
      p.1 • (A₀.indicator fun z => f (a + z)) (Complex.polarCoord.symm p)
        = ((Set.Ioo ε R) ×ˢ (Set.univ : Set ℝ)).indicator
            (fun q : ℝ × ℝ => q.1 • f (a + Complex.polarCoord.symm q)) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    have hnorm : ‖Complex.polarCoord.symm ((r, θ) : ℝ × ℝ)‖ = r :=
      norm_polarCoord_symm_of_pos hr θ
    by_cases hcut : ε < r ∧ r < R
    · rw [Set.indicator_of_mem (show Complex.polarCoord.symm ((r, θ) : ℝ × ℝ) ∈ A₀ by
        rw [hA₀def, Set.mem_ofPred_eq, hnorm]; exact hcut),
        Set.indicator_of_mem (show ((r, θ) : ℝ × ℝ) ∈ (Set.Ioo ε R) ×ˢ (Set.univ : Set ℝ) from
          ⟨hcut, Set.mem_univ _⟩)]
    · rw [Set.indicator_of_notMem (show Complex.polarCoord.symm ((r, θ) : ℝ × ℝ) ∉ A₀ by
        rw [hA₀def, Set.mem_ofPred_eq, hnorm]; exact hcut),
        Set.indicator_of_notMem (show ((r, θ) : ℝ × ℝ) ∉ (Set.Ioo ε R) ×ˢ (Set.univ : Set ℝ) from
          fun hc => hcut hc.1), smul_zero]
  rw [step1, ← integral_indicator hA₀,
    ← Complex.integral_comp_polarCoord_symm (A₀.indicator fun z => f (a + z)), polarCoord_target,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcong,
    setIntegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ), Set.prod_inter_prod,
    Set.inter_eq_self_of_subset_right hsub, Set.inter_univ]

/-! ### The angular range -/

/-- **The chart's angular range against the circle's.**  The chart runs the angle over `(-π, π)`
and a circle integral over `(0, 2π)`; the integrand is `2π`-periodic, so the two agree. -/
theorem integral_Ioo_polarCoord_symm_eq_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (a : ℂ) (r : ℝ) :
    (∫ θ in Set.Ioo (-π) π, f (a + Complex.polarCoord.symm ((r, θ) : ℝ × ℝ)))
      = ∫ θ in (0 : ℝ)..(2 * π), f (circleMap a r θ) := by
  have hper : Function.Periodic (fun θ : ℝ => f (circleMap a r θ)) (2 * π) :=
    (periodic_circleMap a r).comp f
  have h1 : (∫ θ in Set.Ioo (-π) π, f (a + Complex.polarCoord.symm ((r, θ) : ℝ × ℝ)))
      = ∫ θ in (-π)..π, f (circleMap a r θ) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π),
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo
      fun θ _ => by rw [add_polarCoord_symm_eq_circleMap]
  have h3 := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π from by ring, zero_add] at h3
  rw [h1]
  exact h3


/-! ### Axiom footprint -/

/-- info: 'Shields.polarCoord_symm_eq_circleMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polarCoord_symm_eq_circleMap

/-- info: 'Shields.continuous_polarCoord_symm_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms continuous_polarCoord_symm_complex

/-- info: 'Shields.setIntegral_annulus_polarCoord_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setIntegral_annulus_polarCoord_symm

/-- info: 'Shields.integral_Ioo_polarCoord_symm_eq_circleMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_Ioo_polarCoord_symm_eq_circleMap

end Shields
