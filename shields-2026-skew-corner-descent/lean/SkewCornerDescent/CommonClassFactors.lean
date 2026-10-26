/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedPrimeValuation

/-!
# Common class factors without deleting word positions

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
Constant class counts factor out the same power from every complete cyclic inventory.
At another exposed root, the removed actual response is a valuation unit. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- Replace one response factor by one, keeping the original class word and every position. -/
def peeledResponses {α R : Type*} [DecidableEq α] [One R] (a : α) (response : α → R) : α → R :=
  fun Y => if Y = a then 1 else response Y

/-- Each individual window factors by its actual anchor-class count. -/
theorem windowProduct_class_factor {G α R : Type*}
    [AddCommGroup G] [DecidableEq α] [CommMonoid R]
    (word : G → α) (response : α → R) (step : G) (j : ℕ) (start : G) (a : α) :
    windowProduct (response ∘ word) step j start =
      response a ^ windowSum (classMask word a) step j start *
        windowProduct (peeledResponses a response ∘ word) step j start := by
  classical
  have he (i : G) : response (word i) =
      response a ^ classMask word a i * peeledResponses a response (word i) := by
    by_cases hi : word i = a <;> simp [classMask, peeledResponses, hi]
  unfold windowProduct
  simp only [Function.comp_apply, he]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

/-- A constant class count gives a common reciprocal power, retaining all starts and wraps. -/
theorem inverseWindowSum_class_factor {G α R : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq α] [Semifield R]
    (word : G → α) (response : α → R) (step : G) (j k : ℕ) (a : α)
    (hcount : ∀ i, windowSum (classMask word a) step j i = k) :
    (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) =
      (response a)⁻¹ ^ k *
        ∑ i, (windowProduct (peeledResponses a response ∘ word) step j i)⁻¹ := by
  simp_rw [windowProduct_class_factor word response step j _ a, hcount, mul_inv, inv_pow]
  rw [Finset.mul_sum]

/-- A constant class count gives a common forward power, without deleting any word position. -/
theorem forwardWindowSum_class_factor {G α R : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq α] [CommSemiring R]
    (word : G → α) (response : α → R) (step : G) (j k : ℕ) (a : α)
    (hcount : ∀ i, windowSum (classMask word a) step j i = k) :
    (∑ i, windowProduct (response ∘ word) step j i) =
      response a ^ k * ∑ i, windowProduct (peeledResponses a response ∘ word) step j i := by
  simp_rw [windowProduct_class_factor word response step j _ a, hcount]
  rw [Finset.mul_sum]

/-- A zero signed coefficient removes its summand, not its occurrences in the word. -/
theorem signedLabelSum_peel {α R : Type*} [Fintype α] [DecidableEq α] [Field R]
    (response e : α → R) (a : α) (he : e a = 0) :
    (∑ Y, e Y * (response Y)⁻¹) =
      ∑ Y, e Y * (peeledResponses a response Y)⁻¹ := by
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hY : Y = a
  · subst Y
    simp only [he, zero_mul]
  · simp only [peeledResponses, hY, ite_false]

/-- Constant inactive counts factor the complete short detector, preserving every start. -/
theorem shortDetector_class_factor {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [Field R]
    (word : G → α) (response e : α → R) (step : G)
    (j prefixLength k : ℕ) (start : G) (a : α) (s m : R)
    (he : e a = 0)
    (hcount : ∀ i, windowSum (classMask word a) step j i = k)
    (hprefix : windowSum (classMask word a) step prefixLength start = k) :
    s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ Y, e Y * (response Y)⁻¹) =
      (response a)⁻¹ ^ k *
        (s * (∑ i, (windowProduct (peeledResponses a response ∘ word) step j i)⁻¹) -
          m * (windowProduct (peeledResponses a response ∘ word) step prefixLength start)⁻¹ *
            (∑ Y, e Y * (peeledResponses a response Y)⁻¹)) := by
  rw [inverseWindowSum_class_factor word response step j k a hcount,
    windowProduct_class_factor word response step prefixLength start a, hprefix,
    mul_inv, inv_pow, signedLabelSum_peel response e a he]
  ring

/-- A nonzero inactive response makes short-detector vanishing invariant under common-factor
peeling. This is a cancellation theorem, not an assumed vanished detector. -/
theorem shortDetector_peel_zero_iff {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [Field R]
    (word : G → α) (response e : α → R) (step : G)
    (j prefixLength k : ℕ) (start : G) (a : α) (s m : R)
    (ha : response a ≠ 0) (he : e a = 0)
    (hcount : ∀ i, windowSum (classMask word a) step j i = k)
    (hprefix : windowSum (classMask word a) step prefixLength start = k) :
    (s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
        m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
          (∑ Y, e Y * (response Y)⁻¹) = 0) ↔
      (s * (∑ i, (windowProduct (peeledResponses a response ∘ word) step j i)⁻¹) -
        m * (windowProduct (peeledResponses a response ∘ word) step prefixLength start)⁻¹ *
          (∑ Y, e Y * (peeledResponses a response Y)⁻¹) = 0) := by
  rw [shortDetector_class_factor word response e step j prefixLength k start a s m
    he hcount hprefix]
  exact mul_eq_zero_iff_left (pow_ne_zero _ (inv_ne_zero ha))

/-- The full-period detector has the same common inactive factor on both sides.
Its forward-window counts are produced from the complete cycles and constant short masks. -/
theorem fullDetector_class_factor {α R : Type*}
    [Fintype α] [DecidableEq α] [Field R] {n : ℕ} [NeZero n]
    (word : ZMod n → α) (response e : α → R)
    (m prefixLength k t : ℕ) (a : α) (scalar : R)
    (he : e a = 0)
    (hcount : ∀ i, windowSum (classMask word a) 1 m i = t)
    (hprefix : windowSum (classMask word a) 1 prefixLength 0 = t) :
    scalar * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 prefixLength 0 -
        (∑ Y, e Y * (response Y)⁻¹) *
          (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) =
      response a ^ ((k - 1) * (∑ i, classMask word a i) + t) *
        (scalar * (windowProduct (peeledResponses a response ∘ word) 1 n 0) ^ (k - 1) *
          windowProduct (peeledResponses a response ∘ word) 1 prefixLength 0 -
          (∑ Y, e Y * (peeledResponses a response Y)⁻¹) *
            (∑ i, windowProduct (peeledResponses a response ∘ word) 1
              ((k - 1) * n + m) i)) := by
  have hfull (i : ZMod n) : windowSum (classMask word a) 1 ((k - 1) * n + m) i =
      (k - 1) * (∑ x, classMask word a x) + t := by
    simp only [zmod_windowSum_mul_add, hcount, nsmul_eq_mul, Nat.cast_id]
  rw [forwardWindowSum_class_factor word response 1 ((k - 1) * n + m) _ a hfull,
    windowProduct_class_factor word response 1 n 0 a,
    windowProduct_class_factor word response 1 prefixLength 0 a,
    zmod_windowSum_cycle, hprefix, mul_pow, ← pow_mul,
    signedLabelSum_peel response e a he]
  rw [pow_add, mul_comm (k - 1)]
  ring

/-- Peeling an actual regular response factor does not change the cyclic valuation at another
exposed root. The unit property is produced from that response's coordinate slice. -/
theorem exposedRoot_peel_inverse {G α : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq α]
    (word : G → α) (step : G) (j k : ℕ) (a : α)
    (num den : α → Polynomial ℝ) (r : ℝ)
    (hnum : Polynomial.eval r (num a) ≠ 0) (hden : Polynomial.eval r (den a) ≠ 0)
    (hcount : ∀ i, windowSum (classMask word a) step j i = k) :
    let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) =
      (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ i, (windowProduct (peeledResponses a response ∘ word) step j i)⁻¹) := by
  dsimp only
  rw [inverseWindowSum_class_factor word _ step j k a hcount,
    map_mul, map_pow, map_inv₀, exposedRoot_regular_fraction r (num a) (den a) hnum hden,
    inv_one, one_pow, one_mul]

/-- The same regular response factor is a unit for complete forward inventories. -/
theorem exposedRoot_peel_forward {G α : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq α]
    (word : G → α) (step : G) (j k : ℕ) (a : α)
    (num den : α → Polynomial ℝ) (r : ℝ)
    (hnum : Polynomial.eval r (num a) ≠ 0) (hden : Polynomial.eval r (den a) ≠ 0)
    (hcount : ∀ i, windowSum (classMask word a) step j i = k) :
    let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
    (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ i, windowProduct (response ∘ word) step j i) =
      (exposedRootIdeal r).valuation (RatFunc ℝ)
        (∑ i, windowProduct (peeledResponses a response ∘ word) step j i) := by
  dsimp only
  rw [forwardWindowSum_class_factor word _ step j k a hcount,
    map_mul, map_pow, exposedRoot_regular_fraction r (num a) (den a) hnum hden,
    one_pow, one_mul]

end SkewCornerDescent.CyclicWindows
