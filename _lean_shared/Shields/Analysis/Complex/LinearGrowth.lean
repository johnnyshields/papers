/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# An entire function whose real part grows linearly is linear

Borel--Carathéodory bounds `‖g‖` on a ball by the supremum of `Re g` on a larger one.  Run over
balls whose radius grows with the point, it turns a *one-sided* bound on `Re g` into a two-sided
bound on `‖g‖` of the same order, and Liouville reads that as a degree bound.

Mathlib carries the local statement (`Complex.borelCaratheodory_zero`) and Liouville
(`Differentiable.apply_eq_apply_of_bounded`), but neither the globalization nor the linearity
corollary.

Sorry-free.

## Main results

* `Shields.norm_le_of_re_le_linear` --- the globalized inequality.  `Re g z ≤ A‖z‖ + B` on the
  whole plane gives `‖g z‖ ≤ 4A‖z‖ + 2A + 2B`, from the single choice of radius `R = 2‖z‖ + 1`.
* `Shields.differentiable_dslope`, `Shields.dslope_zero_apply` --- the difference quotient of an
  entire function at a point is entire, and equals `g w / w` at every `w ≠ 0` once `g 0 = 0`.
  Mathlib's removable-singularity statement is local; this is its global form.
* `Shields.isBounded_range_dslope_zero` --- what the majorant is for: a linear bound on `‖g‖`
  with `g 0 = 0` makes the difference quotient at the origin bounded on the whole plane.
* `Shields.eq_deriv_mul_of_re_le` --- the conclusion.  An entire `g` with `g 0 = 0` and a linear
  majorant on its real part is `z ↦ g'(0) * z`, by Liouville on that quotient.

## Tags

Borel--Carathéodory, Liouville, entire function, linear growth, difference quotient
-/

open Complex Metric Set

namespace Shields

variable {g : ℂ → ℂ}

/-- **Borel--Carathéodory, globalized.**  An entire function vanishing at the origin whose real
part has a linear majorant has a linear majorant on its modulus.

The radius is `R = 2‖z‖ + 1`, which keeps `R - ‖z‖ ≥ 1` and so keeps the Borel--Carathéodory
denominator away from zero at every point at once. -/
theorem norm_le_of_re_le_linear (hg : Differentiable ℂ g) (hg0 : g 0 = 0) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hre : ∀ z, (g z).re ≤ A * ‖z‖ + B) (z : ℂ) :
    ‖g z‖ ≤ 4 * A * ‖z‖ + (2 * A + 2 * B) := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  set R : ℝ := 2 * ‖z‖ + 1 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hzR : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, hRdef]; linarith
  have hM : 0 < A * R + B := by nlinarith
  have hmaps : MapsTo g (ball (0 : ℂ) R) {w : ℂ | w.re ≤ A * R + B} := by
    intro w hw
    have hwR : ‖w‖ < R := mem_ball_zero_iff.mp hw
    have := hre w
    simp only [Set.mem_ofPred_eq]
    nlinarith [norm_nonneg w]
  have hbc := Complex.borelCaratheodory_zero hM hg.differentiableOn hmaps hR0 hzR hg0
  have hden : R - ‖z‖ = ‖z‖ + 1 := by rw [hRdef]; ring
  rw [hden] at hbc
  have hfrac : ‖z‖ / (‖z‖ + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  calc ‖g z‖ ≤ 2 * (A * R + B) * ‖z‖ / (‖z‖ + 1) := hbc
    _ = (2 * (A * R + B)) * (‖z‖ / (‖z‖ + 1)) := by ring
    _ ≤ (2 * (A * R + B)) * 1 := by
        apply mul_le_mul_of_nonneg_left hfrac (by linarith)
    _ = 4 * A * ‖z‖ + (2 * A + 2 * B) := by rw [hRdef]; ring

/-- The difference quotient of an entire function at a point is entire.  Mathlib has the
removable-singularity statement on a neighborhood (`Complex.differentiableOn_dslope`); this is
its global form. -/
theorem differentiable_dslope (hg : Differentiable ℂ g) (c : ℂ) :
    Differentiable ℂ (dslope g c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hg.differentiableOn

/-- `dslope g 0 w = g w / w` away from the origin, when `g` vanishes there. -/
theorem dslope_zero_apply (hg0 : g 0 = 0) {w : ℂ} (hw : w ≠ 0) : dslope g 0 w = g w / w := by
  rw [dslope_of_ne _ hw, slope_def_field, hg0, sub_zero, sub_zero]

/-- **A linear bound on `‖g‖` bounds the difference quotient at the origin.**  Outside the unit
disc `‖g w‖ / ‖w‖` is at most the slope plus the constant; inside it `dslope g 0` is a continuous
function on a compact set.  This is what Liouville consumes, and it is the only thing the linear
majorant is used for. -/
theorem isBounded_range_dslope_zero (hg : Differentiable ℂ g) (hg0 : g 0 = 0) {a b : ℝ}
    (hb : 0 ≤ b) (hbd : ∀ w : ℂ, ‖g w‖ ≤ a * ‖w‖ + b) :
    Bornology.IsBounded (Set.range (dslope g 0)) := by
  have hfar : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖dslope g 0 w‖ ≤ a + b := by
    intro w hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
    rw [dslope_zero_apply hg0 hw0, norm_div, div_le_iff₀ (by linarith)]
    calc ‖g w‖ ≤ a * ‖w‖ + b := hbd w
      _ ≤ (a + b) * ‖w‖ := by nlinarith
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_dslope hg 0).continuous.continuousOn
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max C (a + b), ?_⟩
  rintro _ ⟨w, rfl⟩
  rcases le_or_gt ‖w‖ 1 with h | h
  · exact le_max_of_le_left (hC w (by simpa [mem_closedBall_zero_iff] using h))
  · exact le_max_of_le_right (hfar w h.le)

/-- **An entire function with a linear majorant on its real part is linear.**

`Re g z ≤ A‖z‖ + B` bounds `‖g z‖` linearly (`Shields.norm_le_of_re_le_linear`), hence bounds the
difference quotient at the origin (`Shields.isBounded_range_dslope_zero`), and Liouville makes that
quotient constant. -/
theorem eq_deriv_mul_of_re_le (hg : Differentiable ℂ g) (hg0 : g 0 = 0) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hre : ∀ z, (g z).re ≤ A * ‖z‖ + B) (z : ℂ) :
    g z = deriv g 0 * z := by
  have hbdd := isBounded_range_dslope_zero hg hg0 (b := 2 * A + 2 * B) (by linarith)
    (norm_le_of_re_le_linear hg hg0 hA hB hre)
  have hconst : dslope g 0 z = dslope g 0 0 :=
    (differentiable_dslope hg 0).apply_eq_apply_of_bounded hbdd z 0
  rw [dslope_same] at hconst
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hg0]
  · rw [dslope_zero_apply hg0 hz] at hconst
    field_simp at hconst
    linear_combination hconst


/-! ### Axiom footprint -/

/-- info: 'Shields.eq_deriv_mul_of_re_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_deriv_mul_of_re_le

end Shields
