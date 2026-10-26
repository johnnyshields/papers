/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.SignedClosurePole
import SkewCornerDescent.ExposedForwardValuation

/-!
# Exposed pole comparison for the short cyclic detector

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
Vanishing of the short detector forces the actual maximal window count to equal the
specified prefix count plus one. Both pole orders are produced, including signed labels.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open Polynomial PhaseInventory WithZero
open scoped BigOperators

/-- Vanishing of the actual reciprocal-window detector equates its two produced pole orders.
The closure exponents are signed; the exposed class has a nonzero exponent. -/
theorem exposed_short_detector_count {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α]
    (word : G → α) (step : G) (j prefixLength : ℕ) (start : G) (a : α)
    (num den : α → Polynomial ℝ) (e : α → ℝ) (r sign s m : ℝ)
    (hroot : eval r (num a) = 0) (hsimple : rootMultiplicity r (num a) = 1)
    (hden : ∀ Y, 0 < eval r (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval r (num Y))
    (he : e a ≠ 0) (hs : s ≠ 0) (hm : m ≠ 0)
    (hzero :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        RatFunc.C m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ Y, RatFunc.C (e Y) * (response Y)⁻¹) = 0) :
    maximalClassWindowCount word step j a =
      windowSum (classMask word a) step prefixLength start + 1 := by
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
  have hL : v (∑ Y, RatFunc.C (e Y) * (response Y)⁻¹) = exp (1 : ℤ) := by
    simpa only [response, inv_div, mul_div_assoc] using
      signedInverseResponses_pole num den e a r hroot hsimple hregular
        (ne_of_gt (hden a)) he
  dsimp only at hzero
  have hv := congrArg v (sub_eq_zero.mp hzero)
  rw [map_mul, exposedRoot_constant_valuation r s hs, one_mul, hF,
    map_mul, map_mul, exposedRoot_constant_valuation r m hm, one_mul,
    map_inv₀, hP, hL, ← exp_neg, neg_neg, ← exp_add] at hv
  exact_mod_cast exp_injective hv

/-- The cross-multiplied full-period identity forces the least forward count to equal the
complete-period contribution, the literal prefix count and one simple closure pole. -/
theorem exposed_full_detector_count {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α]
    (word : G → α) (step : G) (fullLength periodLength prefixLength k : ℕ)
    (start : G) (a : α) (num den : α → Polynomial ℝ) (e : α → ℝ)
    (r sign scalar : ℝ)
    (hroot : eval r (num a) = 0) (hsimple : rootMultiplicity r (num a) = 1)
    (hden : ∀ Y, 0 < eval r (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval r (num Y))
    (he : e a ≠ 0) (hscalar : scalar ≠ 0)
    (hzero :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C scalar * (windowProduct (response ∘ word) step periodLength start) ^ (k - 1) *
          windowProduct (response ∘ word) step prefixLength start -
        (∑ Y, RatFunc.C (e Y) * (response Y)⁻¹) *
          (∑ i, windowProduct (response ∘ word) step fullLength i) = 0) :
    minimalClassWindowCount word step fullLength a =
      (k - 1) * windowSum (classMask word a) step periodLength start +
        windowSum (classMask word a) step prefixLength start + 1 := by
  classical
  let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
    algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
  let v := (exposedRootIdeal r).valuation (RatFunc ℝ)
  have hregular : ∀ Y, Y ≠ a → eval r (num Y) ≠ 0 := by
    intro Y hY hz
    have h := hsign Y hY
    rw [hz, mul_zero] at h
    exact (lt_irrefl 0) h
  have hperiod := exposed_window_valuation word step periodLength start a num den r hsimple
    (fun Y => ne_of_gt (hden Y)) hregular
  have hprefix := exposed_window_valuation word step prefixLength start a num den r hsimple
    (fun Y => ne_of_gt (hden Y)) hregular
  have hforward := cyclic_forward_window_valuation word step fullLength a num den r sign
    hroot hsimple hden hsign
  have hL : v (∑ Y, RatFunc.C (e Y) * (response Y)⁻¹) = exp (1 : ℤ) := by
    simpa only [response, inv_div, mul_div_assoc] using
      signedInverseResponses_pole num den e a r hroot hsimple hregular
        (ne_of_gt (hden a)) he
  dsimp only at hzero
  have hv := congrArg v (sub_eq_zero.mp hzero)
  rw [map_mul, map_mul, exposedRoot_constant_valuation r scalar hscalar, one_mul,
    map_pow, hperiod, hprefix, map_mul, hL, hforward, ← exp_nsmul,
    ← exp_add, ← exp_add] at hv
  have hh := exp_injective hv
  simp only [nsmul_eq_mul, mul_neg] at hh
  have hcount :
      (minimalClassWindowCount word step fullLength a : ℤ) =
        ((k - 1 : ℕ) : ℤ) *
          ((windowSum (classMask word a) step periodLength start : ℕ) : ℤ) +
        ((windowSum (classMask word a) step prefixLength start : ℕ) : ℤ) + 1 := by
    linarith
  exact_mod_cast hcount

end SkewCornerDescent.CyclicWindows
