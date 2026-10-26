/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CommonClassFactors

/-!
# Replacing inactive responses without deleting word positions

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
A constant inactive mask permits any nonzero replacement response. In particular, the
replacement can retain the chamber sign rather than introducing a positive unit in a
negative chamber. Both complete detector identities remain unchanged as zero identities.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- Replacing a class leaves its peeled response family unchanged. -/
theorem peeledResponses_update {α R : Type*} [DecidableEq α] [One R]
    (response : α → R) (a : α) (c : R) :
    peeledResponses a (Function.update response a c) = peeledResponses a response := by
  funext Y
  by_cases hY : Y = a
  · subst Y
    simp only [peeledResponses, ite_true]
  · simp only [peeledResponses, hY, ite_false, Function.update_of_ne hY]

/-- The full detector vanishes exactly when its peeled detector vanishes. -/
theorem fullDetector_peel_zero_iff {α R : Type*}
    [Fintype α] [DecidableEq α] [Field R] {n : ℕ} [NeZero n]
    (word : ZMod n → α) (response e : α → R)
    (m prefixLength k t : ℕ) (a : α) (scalar : R)
    (ha : response a ≠ 0) (he : e a = 0)
    (hcount : ∀ i, windowSum (classMask word a) 1 m i = t)
    (hprefix : windowSum (classMask word a) 1 prefixLength 0 = t) :
    (scalar * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 prefixLength 0 -
      (∑ Y, e Y * (response Y)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0) ↔
    (scalar * (windowProduct (peeledResponses a response ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (peeledResponses a response ∘ word) 1 prefixLength 0 -
      (∑ Y, e Y * (peeledResponses a response Y)⁻¹) *
        (∑ i, windowProduct (peeledResponses a response ∘ word) 1
          ((k - 1) * n + m) i) = 0) := by
  rw [fullDetector_class_factor word response e m prefixLength k t a scalar he hcount hprefix]
  exact mul_eq_zero_iff_left (pow_ne_zero _ ha)

/-- Arbitrary nonzero replacement of an inactive response preserves short-detector vanishing.
The class word and every cyclic start are unchanged. -/
theorem shortDetector_update_zero_iff {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [Field R]
    (word : G → α) (response e : α → R) (step : G)
    (j prefixLength t : ℕ) (start : G) (a : α) (c s m : R)
    (ha : response a ≠ 0) (hc : c ≠ 0) (he : e a = 0)
    (hcount : ∀ i, windowSum (classMask word a) step j i = t)
    (hprefix : windowSum (classMask word a) step prefixLength start = t) :
    (s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
      m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
        (∑ Y, e Y * (response Y)⁻¹) = 0) ↔
    (s * (∑ i, (windowProduct (Function.update response a c ∘ word) step j i)⁻¹) -
      m * (windowProduct (Function.update response a c ∘ word) step prefixLength start)⁻¹ *
        (∑ Y, e Y * (Function.update response a c Y)⁻¹) = 0) := by
  rw [shortDetector_peel_zero_iff word response e step j prefixLength t start a s m
      ha he hcount hprefix,
    shortDetector_peel_zero_iff word (Function.update response a c) e step j
      prefixLength t start a s m (by simpa only [Function.update_self] using hc)
      he hcount hprefix, peeledResponses_update]

/-- The complete forward detector also survives an arbitrary nonzero inactive replacement. -/
theorem fullDetector_update_zero_iff {α R : Type*}
    [Fintype α] [DecidableEq α] [Field R] {n : ℕ} [NeZero n]
    (word : ZMod n → α) (response e : α → R)
    (m prefixLength k t : ℕ) (a : α) (c scalar : R)
    (ha : response a ≠ 0) (hc : c ≠ 0) (he : e a = 0)
    (hcount : ∀ i, windowSum (classMask word a) 1 m i = t)
    (hprefix : windowSum (classMask word a) 1 prefixLength 0 = t) :
    (scalar * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 prefixLength 0 -
      (∑ Y, e Y * (response Y)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0) ↔
    (scalar * (windowProduct (Function.update response a c ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (Function.update response a c ∘ word) 1 prefixLength 0 -
      (∑ Y, e Y * (Function.update response a c Y)⁻¹) *
        (∑ i, windowProduct (Function.update response a c ∘ word) 1
          ((k - 1) * n + m) i) = 0) := by
  rw [fullDetector_peel_zero_iff word response e m prefixLength k t a scalar
      ha he hcount hprefix,
    fullDetector_peel_zero_iff word (Function.update response a c) e m prefixLength k t
      a scalar (by simpa only [Function.update_self] using hc) he hcount hprefix,
    peeledResponses_update]

end SkewCornerDescent.CyclicWindows
