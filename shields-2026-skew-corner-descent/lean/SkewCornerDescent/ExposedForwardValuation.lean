/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ForwardWindowPolynomials
import SkewCornerDescent.ExposedPrimeValuation

/-!
# Exact exposed valuations of complete forward-window sums

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`).
All-start denominator clearing identifies the forward sum with its polynomial inventory;
the produced leading term gives its exact minimum-window order. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open Polynomial PhaseInventory WithZero
open scoped BigOperators

/-- The complete forward polynomial inventory is the actual dependent window sum after
clearing every denominator. -/
theorem forwardWindowNumerator_fraction {G α R F : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [CommRing R] [Field F]
    (word : G → α) (step : G) (j : ℕ) (num den : α → R) (φ : R →+* F)
    (hden : ∀ Y, φ (den Y) ≠ 0) :
    φ (forwardWindowNumerator word step j num den) /
      φ (∏ Y, den Y ^ maximalClassWindowCount word step j Y) =
      ∑ i, windowProduct ((fun Y => φ (num Y) / φ (den Y)) ∘ word) step j i := by
  classical
  unfold forwardWindowNumerator
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [windowProduct_eq_class_product word (fun Y => φ (num Y) / φ (den Y)),
    map_prod, map_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro Y _
  rw [map_mul, map_pow, map_pow, map_pow]
  have hb : windowSum (classMask word Y) step j i ≤
      maximalClassWindowCount word step j Y := Finset.le_sup (Finset.mem_univ i)
  have hp : φ (den Y) ^ maximalClassWindowCount word step j Y =
      φ (den Y) ^ windowSum (classMask word Y) step j i *
        φ (den Y) ^ (maximalClassWindowCount word step j Y -
          windowSum (classMask word Y) step j i) := by
    rw [← pow_add, Nat.add_sub_of_le hb]
  rw [hp, mul_div_mul_right _ _ (pow_ne_zero _ (hden Y)), div_pow]

/-- Same-sign leading terms make the order of the complete forward sum exactly the least
actual anchor count. The negative chamber uses the common residual length. -/
theorem cyclic_forward_window_valuation {G α : Type*}
    [AddCommGroup G] [Fintype G] [Finite α] [DecidableEq α]
    (word : G → α) (step : G) (j : ℕ) (a : α)
    (num den : α → Polynomial ℝ) (r sign : ℝ)
    (hroot : eval r (num a) = 0) (hsimple : rootMultiplicity r (num a) = 1)
    (hden : ∀ Y, 0 < eval r (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval r (num Y)) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ i, windowProduct
          ((fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
            algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)) ∘ word) step j i) =
      exp (-(minimalClassWindowCount word step j a : ℤ)) := by
  classical
  let := Fintype.ofFinite α
  let N := forwardWindowNumerator word step j num den
  let L := forwardWindowLeadingNumerator word step j a num den
  let D : Polynomial ℝ := ∏ Y, den Y ^ maximalClassWindowCount word step j Y
  have hpos := forwardWindowLeadingNumerator_eval_pos word step j a num den
    (evalRingHom r) sign hroot hden hsign
  have hLval : eval r L ≠ 0 := by
    intro hz
    change eval r (forwardWindowLeadingNumerator word step j a num den) = 0 at hz
    simp only [coe_evalRingHom] at hpos
    rw [hz, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hL : L ≠ 0 := by
    intro hz
    exact hLval (by rw [hz, eval_zero])
  have ha : num a ≠ 0 := by
    intro hz
    rw [hz, rootMultiplicity_zero] at hsimple
    exact Nat.zero_ne_one hsimple
  have hfactor : N = num a ^ minimalClassWindowCount word step j a * L :=
    forwardWindowNumerator_factor word step j a num den
  have hN : N ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (pow_ne_zero _ ha) hL
  have hNorder : rootMultiplicity r N = minimalClassWindowCount word step j a := by
    rw [hfactor, rootMultiplicity_mul (by rw [← hfactor]; exact hN),
      simpleRoot_pow_order (num a) r hsimple, rootMultiplicity_eq_zero hLval, add_zero]
  have hDval : eval r D ≠ 0 := by
    change (evalRingHom r) D ≠ 0
    dsimp only [D]
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro Y _
    rw [map_pow]
    exact pow_ne_zero _ (ne_of_gt (hden Y))
  have hD : D ≠ 0 := by
    intro hz
    exact hDval (by rw [hz, eval_zero])
  have hmapden : ∀ Y, algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y) ≠ 0 := by
    intro Y
    apply RatFunc.algebraMap_ne_zero
    intro hz
    have hh := hden Y
    rw [hz, eval_zero] at hh
    exact (lt_irrefl 0) hh
  rw [← forwardWindowNumerator_fraction word step j num den
    (algebraMap (Polynomial ℝ) (RatFunc ℝ)) hmapden,
    map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    exposedRoot_intValuation r _ hN, exposedRoot_intValuation r _ hD,
    hNorder, rootMultiplicity_eq_zero hDval]
  simp

end SkewCornerDescent.CyclicWindows
