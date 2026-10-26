/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedRootOrders
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Exposed root prime valuations

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
The actual coordinate slice is measured by Mathlib's height-one prime valuation at its
exposed root. Root multiplicities determine the valuation of the complete rational sum.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent

open Polynomial IsDedekindDomain.HeightOneSpectrum WithZero

/-- The height-one prime of the exposed root in the coordinate slice. -/
def exposedRootIdeal (r : ℝ) : IsDedekindDomain.HeightOneSpectrum (Polynomial ℝ) where
  asIdeal := Ideal.span {X - C r}
  isPrime := by
    rw [Ideal.span_singleton_prime]
    exacts [prime_X_sub_C r, X_sub_C_ne_zero r]
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero r

/-- Polynomial root order agrees with the height-one prime's integral valuation. -/
theorem exposedRoot_intValuation (r : ℝ) (p : Polynomial ℝ) (hp : p ≠ 0) :
    (exposedRootIdeal r).intValuation p = exp (-(p.rootMultiplicity r : ℤ)) := by
  obtain ⟨q, hfactor, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp r
  have hunit : (exposedRootIdeal r).intValuation q = 1 := by
    apply intValuation_eq_one_iff.mpr
    change q ∉ Ideal.span {X - C r}
    simpa only [Ideal.mem_span_singleton] using hq
  have hlinear : (exposedRootIdeal r).intValuation (X - C r) = exp (-1 : ℤ) :=
    intValuation_singleton _ (X_sub_C_ne_zero r) rfl
  conv_lhs => rw [hfactor, map_mul, map_pow, hlinear, hunit, mul_one]
  simp only [← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]

/-- A regular leading numerator over a denominator of root order `m` has pole order `m`.
The multiplicative valuation uses `exp m`; its additive root order is `-m`. -/
theorem exposedRoot_fraction_valuation (r : ℝ) (numerator denominator : Polynomial ℝ)
    (hn : numerator ≠ 0) (hd : denominator ≠ 0)
    (hnorder : numerator.rootMultiplicity r = 0)
    (m : ℕ) (hdorder : denominator.rootMultiplicity r = m) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (algebraMap (Polynomial ℝ) (RatFunc ℝ) numerator /
          algebraMap (Polynomial ℝ) (RatFunc ℝ) denominator) = exp (m : ℤ) := by
  rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    exposedRoot_intValuation r numerator hn, exposedRoot_intValuation r denominator hd,
    hnorder, hdorder]
  simp

/-- A coordinate response regular and nonzero at the exposed root is a valuation unit. -/
theorem exposedRoot_regular_fraction (r : ℝ) (num den : Polynomial ℝ)
    (hn : Polynomial.eval r num ≠ 0) (hd : Polynomial.eval r den ≠ 0) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (algebraMap (Polynomial ℝ) (RatFunc ℝ) num /
          algebraMap (Polynomial ℝ) (RatFunc ℝ) den) = 1 := by
  have hn0 : num ≠ 0 := by
    intro hz
    exact hn (by rw [hz, Polynomial.eval_zero])
  have hd0 : den ≠ 0 := by
    intro hz
    exact hd (by rw [hz, Polynomial.eval_zero])
  simpa using exposedRoot_fraction_valuation r num den hn0 hd0
    (Polynomial.rootMultiplicity_eq_zero hn) 0 (Polynomial.rootMultiplicity_eq_zero hd)

/-- A nonzero real scalar is a unit for every exposed-root valuation. -/
theorem exposedRoot_constant_valuation (r c : ℝ) (hc : c ≠ 0) :
    (exposedRootIdeal r).valuation (RatFunc ℝ) (RatFunc.C c) = 1 := by
  rw [← RatFunc.algebraMap_C, valuation_of_algebraMap,
    exposedRoot_intValuation r (Polynomial.C c) (Polynomial.C_ne_zero.mpr hc),
    Polynomial.rootMultiplicity_C]
  simp

namespace CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- The full cyclic reciprocal inventory has the exact maximal-window pole at an exposed
simple root. The clearing identity and its leading-term producer are both invoked. -/
theorem cyclic_inverse_window_valuation {G α : Type*}
    [AddCommGroup G] [Fintype G] [Finite α] [DecidableEq α]
    (word : G → α) (step : G) (j : ℕ) (a : α)
    (num den : α → Polynomial ℝ) (r sign : ℝ)
    (hroot : Polynomial.eval r (num a) = 0)
    (hsimple : Polynomial.rootMultiplicity r (num a) = 1)
    (hden : ∀ Y, 0 < Polynomial.eval r (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * Polynomial.eval r (num Y)) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ i, (windowProduct
          ((fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
            algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)) ∘ word) step j i)⁻¹) =
      exp (maximalClassWindowCount word step j a : ℤ) := by
  classical
  let := Fintype.ofFinite α
  have hnum : ∀ Y, num Y ≠ 0 := by
    intro Y hz
    by_cases hY : Y = a
    · subst Y
      rw [hz, Polynomial.rootMultiplicity_zero] at hsimple
      exact Nat.zero_ne_one hsimple
    · have hs := hsign Y hY
      rw [hz, Polynomial.eval_zero, mul_zero] at hs
      exact (lt_irrefl 0) hs
  have hmap : ∀ Y, algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) ≠ 0 :=
    fun Y => RatFunc.algebraMap_ne_zero (hnum Y)
  have he := cyclic_inverse_window_numerator_fraction word step j a num den
    (algebraMap (Polynomial ℝ) (RatFunc ℝ)) hmap
  have ho := cyclic_inverse_window_root_orders word step j a num den r sign
    hroot hsimple hden hsign
  dsimp only at he ho
  rw [← he]
  simpa only [map_mul, map_pow, map_prod] using
    exposedRoot_fraction_valuation r _ _ ho.1 ho.2.2.1 ho.2.1
      (maximalClassWindowCount word step j a) ho.2.2.2

/-- An individual actual window has pole order equal to its anchor-class count. Unlike the
cyclic sum, this product needs no same-sign premise. -/
theorem exposed_window_valuation {G α : Type*}
    [AddCommGroup G] [Finite α] [DecidableEq α]
    (word : G → α) (step : G) (j : ℕ) (start : G) (a : α)
    (num den : α → Polynomial ℝ) (r : ℝ)
    (hsimple : Polynomial.rootMultiplicity r (num a) = 1)
    (hden : ∀ Y, Polynomial.eval r (den Y) ≠ 0)
    (hregular : ∀ Y, Y ≠ a → Polynomial.eval r (num Y) ≠ 0) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (windowProduct
          ((fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
            algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)) ∘ word) step j start) =
      exp (-((windowSum (classMask word a) step j start : ℕ) : ℤ)) := by
  classical
  let := Fintype.ofFinite α
  let v := (exposedRootIdeal r).valuation (RatFunc ℝ)
  have hvden (Y : α) : v (algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)) = 1 := by
    have hd : den Y ≠ 0 := by
      intro hz
      exact hden Y (by rw [hz, Polynomial.eval_zero])
    rw [valuation_of_algebraMap, exposedRoot_intValuation r (den Y) hd,
      Polynomial.rootMultiplicity_eq_zero (hden Y)]
    simp
  have hva : v (algebraMap (Polynomial ℝ) (RatFunc ℝ) (num a)) = exp (-1 : ℤ) := by
    have hn : num a ≠ 0 := by
      intro hz
      rw [hz, Polynomial.rootMultiplicity_zero] at hsimple
      exact Nat.zero_ne_one hsimple
    rw [valuation_of_algebraMap, exposedRoot_intValuation r (num a) hn, hsimple]
    norm_num
  have hvoff (Y : α) (hY : Y ≠ a) :
      v (algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y)) = 1 := by
    have hn : num Y ≠ 0 := by
      intro hz
      exact hregular Y hY (by rw [hz, Polynomial.eval_zero])
    rw [valuation_of_algebraMap, exposedRoot_intValuation r (num Y) hn,
      Polynomial.rootMultiplicity_eq_zero (hregular Y hY)]
    simp
  rw [windowProduct_eq_class_product word
    (fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)), map_prod]
  rw [Finset.prod_eq_single a]
  · rw [map_pow, map_div₀, hva, hvden, div_one]
    simp only [← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  · intro Y _ hY
    rw [map_pow, map_div₀, hvoff Y hY, hvden, div_one, one_pow]
  · simp

end CyclicWindows

end SkewCornerDescent
