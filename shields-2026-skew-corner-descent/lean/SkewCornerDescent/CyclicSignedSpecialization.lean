/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicSignedSupport
import SkewCornerDescent.RegularDetectorSpecialization

/-!
# Signed-support nonvanishing in the unchanged source field

Supports `shields-2026-skew-corner-descent.tex` (`lem:two-support`,
`cor:one-positive-short`). A complete zero short identity specializes through
regular finite polynomial representatives. The constructed positive last detector
contradicts its consequence. No map on the whole source fraction field is asserted.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- A single simultaneous positive regular specialization with distinct positive
and negative classes proves nonzero source short inventory. The logarithmic
balance and every window normalization come from complete literal class counts. -/
theorem specialized_one_positive_short_ne_zero {α R F : Type*}
    [Fintype α] [DecidableEq α] [CommRing R] [Field F] [CharZero F]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (ι : R →+* F) (φ : R →+* ℝ) (hι : Function.Injective ι)
    (num den : α → R) (word : ZMod (r * d) → α)
    (hnF : ∀ a, ι (num a) ≠ 0) (hdF : ∀ a, ι (den a) ≠ 0)
    (hnR : ∀ a, φ (num a) ≠ 0) (hdR : ∀ a, φ (den a) ≠ 0)
    (hpos : ∀ a, 0 < φ (num a) / φ (den a)) (p : α)
    (hothers : ∀ a, a ≠ p → classDefect word 1 d s (r * s - 1) 0 a ≤ 0)
    (hnegative : ∃ a, classDefect word 1 d s (r * s - 1) 0 a < 0 ∧
      φ (num a) / φ (den a) ≠ φ (num p) / φ (den p)) :
    let response := fun a => ι (num a) / ι (den a)
    windowDefect (response ∘ word) response (classDefect word 1 d s (r * s - 1) 0)
      (k * d + s) (k * (r * d) + r * s) (r * s) ≠ 0 := by
  classical
  let response := fun a => ι (num a) / ι (den a)
  let realResponse := fun a => φ (num a) / φ (den a)
  let e := classDefect word 1 d s (r * s - 1) 0
  let : NeZero (r * s) := ⟨Nat.ne_of_gt (Nat.mul_pos hr hs)⟩
  have he := sum_reduced_classDefect hr hs word
  change windowDefect (response ∘ word) response e
    (k * d + s) (k * (r * d) + r * s) (r * s) ≠ 0
  intro hz
  rw [windowDefect_short (response ∘ word) response e (Nat.mul_le_mul_left r hsd)
    hk rfl he] at hz
  have hsource : ι (s : R) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
      ι (r * s : R) * (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
        (∑ a, ι (e a : R) * (response a)⁻¹) = 0 := by
    simpa only [map_mul, map_natCast, map_intCast, Nat.cast_mul, inverseWindowSum, closureLabelSum,
      windowProduct, zero_add, nsmul_eq_mul, mul_one] using hz
  have hreal := shortDetector_zero_specialize ι φ hι num den word (fun a => (e a : R))
    1 (r * s) (r * s - 1) 0 (s : R) (r * s : R) hnF hdF hnR hdR hsource
  have hrealShort : windowDefect (realResponse ∘ word) realResponse e
      (k * d + s) (k * (r * d) + r * s) (r * s) = 0 := by
    rw [windowDefect_short (realResponse ∘ word) realResponse e
      (Nat.mul_le_mul_left r hsd) hk rfl he]
    simpa only [map_mul, map_natCast, map_intCast, Nat.cast_mul, inverseWindowSum, closureLabelSum,
      windowProduct, zero_add, nsmul_eq_mul, mul_one] using hreal
  have hfull := windowDefect_full_eq_short (r := r) (d := d) (s := s)
    (realResponse ∘ word) realResponse e (Nat.mul_le_mul_left r hsd) hk rfl rfl rfl
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)) he
  rw [windowDefect_eq_last, hrealShort, mul_zero] at hfull
  have hpositive := one_positive_cyclic_last_pos (k := k) hr hs word realResponse hpos
    p hothers hnegative
  rw [hfull] at hpositive
  exact (lt_irrefl 0) hpositive

end SkewCornerDescent.CyclicWindows
