/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedDetectorComparison

/-!
# Inactive exposed classes in the short detector

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
An inactive label sum is regular at the exposed root. The produced cyclic pole order
therefore cannot exceed the actual prefix count. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open Polynomial PhaseInventory WithZero
open scoped BigOperators

/-- A zero anchor coefficient removes its summand, not its position in any response word.
Every other actual response is a valuation unit at the exposed root. -/
theorem inactive_labelSum_valuation_le_one {α : Type*} [Fintype α]
    (num den : α → Polynomial ℝ) (e : α → ℝ) (a : α) (r : ℝ)
    (hden : ∀ Y, eval r (den Y) ≠ 0)
    (hregular : ∀ Y, Y ≠ a → eval r (num Y) ≠ 0) (he : e a = 0) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ Y, RatFunc.C (e Y) *
          (algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
            algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y))⁻¹) ≤ 1 := by
  classical
  apply Valuation.map_sum_le
  intro Y _
  by_cases hY : Y = a
  · subst Y
    simp only [he, map_zero, zero_mul, zero_le]
  · by_cases heY : e Y = 0
    · simp only [heY, map_zero, zero_mul, zero_le]
    · rw [map_mul, exposedRoot_constant_valuation r (e Y) heY, map_inv₀,
        exposedRoot_regular_fraction r (num Y) (den Y) (hregular Y hY) (hden Y)]
      simp

/-- Vanishing of the short detector at an inactive exposed class bounds the maximum by the
literal prefix count. No label-sum valuation or cancellation certificate is assumed. -/
theorem inactive_short_detector_count_le {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α]
    (word : G → α) (step : G) (j prefixLength : ℕ) (start : G) (a : α)
    (num den : α → Polynomial ℝ) (e : α → ℝ) (r sign s m : ℝ)
    (hroot : eval r (num a) = 0) (hsimple : rootMultiplicity r (num a) = 1)
    (hden : ∀ Y, 0 < eval r (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval r (num Y))
    (he : e a = 0) (hs : s ≠ 0) (hm : m ≠ 0)
    (hzero :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        RatFunc.C m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ Y, RatFunc.C (e Y) * (response Y)⁻¹) = 0) :
    maximalClassWindowCount word step j a ≤
      windowSum (classMask word a) step prefixLength start := by
  classical
  let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
    algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
  let v := (exposedRootIdeal r).valuation (RatFunc ℝ)
  have hregular : ∀ Y, Y ≠ a → eval r (num Y) ≠ 0 := by
    intro Y hY hz
    have h := hsign Y hY
    rw [hz, mul_zero] at h
    exact (lt_irrefl 0) h
  have hF := cyclic_inverse_window_valuation word step j a num den r sign
    hroot hsimple hden hsign
  have hP := exposed_window_valuation word step prefixLength start a num den r hsimple
    (fun Y => ne_of_gt (hden Y)) hregular
  have hL := inactive_labelSum_valuation_le_one num den e a r
    (fun Y => ne_of_gt (hden Y)) hregular he
  dsimp only at hzero
  have hv := congrArg v (sub_eq_zero.mp hzero)
  rw [map_mul, exposedRoot_constant_valuation r s hs, one_mul, hF,
    map_mul, map_mul, exposedRoot_constant_valuation r m hm, one_mul,
    map_inv₀, hP, ← exp_neg, neg_neg] at hv
  have hle : exp (maximalClassWindowCount word step j a : ℤ) ≤
      exp ((windowSum (classMask word a) step prefixLength start : ℕ) : ℤ) := by
    rw [hv]
    exact mul_le_of_le_one_right zero_le hL
  exact_mod_cast exp_le_exp.mp hle

end SkewCornerDescent.CyclicWindows
