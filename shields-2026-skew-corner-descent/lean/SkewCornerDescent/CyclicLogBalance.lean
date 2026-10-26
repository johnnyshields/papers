/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicInventoryDefects
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic balance from complete literal class counts

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`,
`lem:two-support`, `cor:one-positive-short`). The balance consumed by the signed
support inequality is derived from actual cyclic occurrences. All values use one
positive assignment; no independence among response coordinates is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- Summing a class-weighted window inventory retains each literal occurrence. -/
theorem sum_class_window_weight {G α R : Type*}
    [AddCommGroup G] [Fintype α] [DecidableEq α] [Semiring R]
    (word : G → α) (weight : α → R) (step : G) (j : ℕ) (i : G) :
    (∑ a, ((windowSum (classMask word a) step j i : ℕ) : R) * weight a) =
      windowSum (weight ∘ word) step j i := by
  classical
  simp only [windowSum, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [classMask, Function.comp_apply]

/-- Signed class balance holds for arbitrary weights, not only logarithms. -/
theorem sum_classDefect_weight {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [Ring R]
    (word : G → α) (weight : α → R) (step : G) (d s j : ℕ) (i : G) :
    (∑ a, (classDefect word step d s j i a : R) * weight a) =
      (s : R) * (∑ x, weight (word x)) -
        (d : R) * windowSum (weight ∘ word) step j i := by
  simp only [classDefect, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_class_inventory_weight, sum_class_window_weight]

/-- The logarithm of a positive literal window is its complete additive inventory. -/
theorem log_windowProduct {G : Type*} [AddCommGroup G]
    (f : G → ℝ) (hf : ∀ x, 0 < f x) (step : G) (j : ℕ) (i : G) :
    Real.log (windowProduct f step j i) = windowSum (Real.log ∘ f) step j i := by
  unfold windowProduct windowSum
  exact Real.log_prod fun _ _ => (hf _).ne'

/-- Every repeated cyclic offset contributes once to the total logarithmic sum. -/
theorem sum_log_inverse_windowProduct {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℝ) (hf : ∀ x, 0 < f x) (step : G) (j : ℕ) :
    (∑ i, Real.log ((windowProduct f step j i)⁻¹)) =
      -(j : ℝ) * ∑ i, Real.log (f i) := by
  simp_rw [Real.log_inv, log_windowProduct f hf]
  rw [Finset.sum_neg_distrib, sum_windowSum]
  simp only [nsmul_eq_mul, Function.comp_apply, neg_mul]

/-- The complete closure-product logarithms have exactly the signed balance
needed by the one-positive-support detector. The class counts produce it; it is
not a separate hypothesis about the responses. -/
theorem cyclic_signed_log_balance {α : Type*} [Fintype α] [DecidableEq α]
    {r d s k : ℕ} [NeZero (r * d)] (hr : 0 < r) (hs : 0 < s)
    (word : ZMod (r * d) → α) (response : α → ℝ) (hpos : ∀ a, 0 < response a) :
    let f := response ∘ word
    let B := k * (r * d) + r * s
    let T := windowProduct f 1 (B - 1) 0
    (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : ℝ) *
      Real.log ((T * response a)⁻¹)) =
        -(k * d + s : ℕ) * ∑ i, Real.log (f i) := by
  classical
  let f := response ∘ word
  let B := k * (r * d) + r * s
  let T := windowProduct f 1 (B - 1) 0
  have hf : ∀ i, 0 < f i := fun i => hpos (word i)
  have hT : 0 < T := Finset.prod_pos fun _ _ => hf _
  have hlen : B - 1 = k * (r * d) + (r * s - 1) := by
    have := Nat.mul_pos hr hs
    dsimp only [B]
    omega
  have hlogT : Real.log T = (k : ℝ) * (∑ i, Real.log (f i)) +
      windowSum (Real.log ∘ f) 1 (r * s - 1) 0 := by
    rw [log_windowProduct f hf, hlen, zmod_windowSum_mul_add]
    simp only [nsmul_eq_mul, Function.comp_apply]
  have he : ∑ a, (classDefect word 1 d s (r * s - 1) 0 a : ℝ) = (d : ℝ) := by
    exact_mod_cast sum_reduced_classDefect hr hs word
  have hweights := sum_classDefect_weight word (Real.log ∘ response) 1 d s (r * s - 1) 0
  simp only [Function.comp_apply] at hweights
  change (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : ℝ) *
    Real.log ((T * response a)⁻¹)) = -(k * d + s : ℕ) * ∑ i, Real.log (f i)
  have hlog (a : α) : Real.log ((T * response a)⁻¹) =
      -Real.log T - Real.log (response a) := by
    rw [Real.log_inv, Real.log_mul hT.ne' (hpos a).ne']
    ring
  simp_rw [hlog, mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, he]
  rw [hweights, hlogT]
  dsimp only [f, Function.comp_def]
  push_cast
  ring

end SkewCornerDescent.CyclicWindows
