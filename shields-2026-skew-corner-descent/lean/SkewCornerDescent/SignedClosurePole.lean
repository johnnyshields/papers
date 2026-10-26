/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedPrimeValuation

/-!
# Exact pole of a signed closure-label sum

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
A nonzero signed coefficient at one simple exposed closure root cannot be canceled by the
other, regular closure terms. Sorry-free.
-/

namespace SkewCornerDescent

open Polynomial WithZero
open scoped BigOperators

/-- Signed closure exponents need not be positive: only the exposed coefficient is nonzero.
All other summands are regular at that root, so the complete label sum has a simple pole. -/
theorem signedInverseResponses_pole {α : Type*} [Fintype α]
    (S den : α → Polynomial ℝ) (e : α → ℝ) (a : α) (r : ℝ)
    (hroot : eval r (S a) = 0) (hsimple : rootMultiplicity r (S a) = 1)
    (hregular : ∀ i, i ≠ a → eval r (S i) ≠ 0)
    (hden : eval r (den a) ≠ 0) (he : e a ≠ 0) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ i, RatFunc.C (e i) * algebraMap (Polynomial ℝ) (RatFunc ℝ) (den i) /
          algebraMap (Polynomial ℝ) (RatFunc ℝ) (S i)) = exp (1 : ℤ) := by
  classical
  let N : Polynomial ℝ := ∑ i, C (e i) * den i * ∏ l ∈ Finset.univ.erase i, S l
  let D : Polynomial ℝ := ∏ i, S i
  have hS : ∀ i, S i ≠ 0 := by
    intro i hz
    by_cases hi : i = a
    · subst i
      rw [hz, rootMultiplicity_zero] at hsimple
      exact Nat.zero_ne_one hsimple
    · exact hregular i hi (by rw [hz, eval_zero])
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hS i
  have hother : eval r (∏ l ∈ Finset.univ.erase a, S l) ≠ 0 := by
    change (evalRingHom r) (∏ l ∈ Finset.univ.erase a, S l) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun l hl => hregular l (Finset.mem_erase.mp hl).1
  have hNval : eval r N =
      e a * eval r (den a) * eval r (∏ l ∈ Finset.univ.erase a, S l) := by
    change (evalRingHom r) N = _
    dsimp only [N]
    rw [map_sum, Finset.sum_eq_single a]
    · simp only [map_mul, coe_evalRingHom, eval_C]
    · intro i _ hi
      rw [map_mul]
      have hz : (evalRingHom r) (∏ l ∈ Finset.univ.erase i, S l) = 0 := by
        rw [map_prod]
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ a⟩)
        exact hroot
      rw [hz, mul_zero]
    · simp
  have hNnonzero : eval r N ≠ 0 := by
    rw [hNval]
    exact mul_ne_zero (mul_ne_zero he hden) hother
  have hNorder : rootMultiplicity r N = 0 := rootMultiplicity_eq_zero hNnonzero
  have hN : N ≠ 0 := by
    intro hz
    exact hNnonzero (by rw [hz, eval_zero])
  have hDorder : rootMultiplicity r D = 1 := by
    have hfactor : D = S a * ∏ l ∈ Finset.univ.erase a, S l :=
      (Finset.mul_prod_erase Finset.univ S (Finset.mem_univ a)).symm
    rw [hfactor, rootMultiplicity_mul (by rw [← hfactor]; exact hD), hsimple,
      rootMultiplicity_eq_zero hother, add_zero]
  have hfrac : algebraMap (Polynomial ℝ) (RatFunc ℝ) N /
      algebraMap (Polynomial ℝ) (RatFunc ℝ) D =
        ∑ i, RatFunc.C (e i) * algebraMap (Polynomial ℝ) (RatFunc ℝ) (den i) /
          algebraMap (Polynomial ℝ) (RatFunc ℝ) (S i) := by
    dsimp only [N]
    rw [map_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have hfactor : D = S i * ∏ l ∈ Finset.univ.erase i, S l :=
      (Finset.mul_prod_erase Finset.univ S (Finset.mem_univ i)).symm
    simp only [map_mul, hfactor, RatFunc.algebraMap_C]
    have hSi := RatFunc.algebraMap_ne_zero (hS i)
    have hprod := RatFunc.algebraMap_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun l _ => hS l :
        (∏ l ∈ Finset.univ.erase i, S l) ≠ 0)
    field_simp
  rw [← hfrac]
  exact exposedRoot_fraction_valuation r N D hN hD hNorder 1 hDorder

end SkewCornerDescent
