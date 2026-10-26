/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.InactiveExposedPoles
import SkewCornerDescent.CyclicInventoryDefects
import SkewCornerDescent.CommonClassFactors

/-!
# Produced inactive-class masks

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
The actual signed class defect supplies the cyclic average. Vanishing of the short detector
then forces constant counts and an unoccupied omitted phase, with every word position kept.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open Polynomial PhaseInventory WithZero
open scoped BigOperators

/-- Vanishing at an inactive exposed class gives constant counts and the actual gcd period,
without any coprimality assumption. The omitted phase remains unoccupied. -/
theorem inactive_short_detector_general_mask {α : Type*} [Fintype α] [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (word : ZMod (r * d) → α) (a : α) (num den : α → Polynomial ℝ)
    (root sign : ℝ) (hroot : eval root (num a) = 0)
    (hsimple : rootMultiplicity root (num a) = 1)
    (hden : ∀ Y, 0 < eval root (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval root (num Y))
    (he : classDefect word 1 d s (r * s - 1) 0 a = 0)
    (hzero :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C (s : ℝ) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        RatFunc.C ((r * s : ℕ) : ℝ) *
          (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ Y, RatFunc.C (classDefect word 1 d s (r * s - 1) 0 Y : ℝ) *
            (response Y)⁻¹) = 0) :
    (∀ i, windowSum (classMask word a) 1 (r * s) i =
      windowSum (classMask word a) 1 (r * s - 1) 0) ∧
    Function.Periodic (classMask word a)
      ((Nat.gcd (r * s) (r * d) : ℕ) : ZMod (r * d)) ∧
    classMask word a ((r * s - 1 : ℕ) : ZMod (r * d)) = 0 := by
  classical
  have hle := inactive_short_detector_count_le word 1 (r * s) (r * s - 1) 0 a num den
    (fun Y => (classDefect word 1 d s (r * s - 1) 0 Y : ℝ)) root sign
    (s : ℝ) (r * s : ℕ) hroot hsimple hden hsign
    (by exact_mod_cast he) (by exact_mod_cast hs.ne')
    (by exact_mod_cast (Nat.mul_pos hr hs).ne') hzero
  have hbound (i : ZMod (r * d)) : windowSum (classMask word a) 1 (r * s) i ≤
      windowSum (classMask word a) 1 (r * s - 1) 0 :=
    (Finset.le_sup (Finset.mem_univ i)).trans hle
  have hconstant := windows_constant_of_maximum_eq_average (classMask word a) 1
    (r * s) (windowSum (classMask word a) 1 (r * s - 1) 0) hbound
    (inactive_class_average word a he)
  refine ⟨hconstant, ?_, ?_⟩
  · have hshort : Function.Periodic (classMask word a)
        ((r * s : ℕ) : ZMod (r * d)) := by
      simpa only [nsmul_eq_mul, mul_one] using periodic_of_constant_windows
        (classMask word a) 1 (r * s) _ hconstant
    exact zmod_periodic_gcd (classMask word a) hshort
  · have ho := omitted_phase_defect hr hs (classMask word a) _ hconstant
    change classDefect word 1 d s (r * s - 1) 0 a =
      (d : ℤ) * classMask word a ((r * s - 1 : ℕ) : ZMod (r * d)) at ho
    rw [he] at ho
    have hz : d * classMask word a ((r * s - 1 : ℕ) : ZMod (r * d)) = 0 := by
      exact_mod_cast ho.symm
    exact (mul_eq_zero.mp hz).resolve_left hd.ne'

/-- For an exposed inactive class, the short detector and actual signed inventory force
constant short-window counts, the reduced gcd period, and an unoccupied omitted phase. -/
theorem inactive_short_detector_mask {α : Type*} [Fintype α] [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (hcoprime : Nat.Coprime d s)
    (word : ZMod (r * d) → α) (a : α) (num den : α → Polynomial ℝ)
    (root sign : ℝ) (hroot : eval root (num a) = 0)
    (hsimple : rootMultiplicity root (num a) = 1)
    (hden : ∀ Y, 0 < eval root (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval root (num Y))
    (he : classDefect word 1 d s (r * s - 1) 0 a = 0)
    (hzero :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C (s : ℝ) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        RatFunc.C ((r * s : ℕ) : ℝ) *
          (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ Y, RatFunc.C (classDefect word 1 d s (r * s - 1) 0 Y : ℝ) *
            (response Y)⁻¹) = 0) :
    (∀ i, windowSum (classMask word a) 1 (r * s) i =
      windowSum (classMask word a) 1 (r * s - 1) 0) ∧
    Function.Periodic (classMask word a) (r : ZMod (r * d)) ∧
    classMask word a ((r * s - 1 : ℕ) : ZMod (r * d)) = 0 := by
  have hm := inactive_short_detector_general_mask hr hd hs word a num den root sign
    hroot hsimple hden hsign he hzero
  have hgcd : Nat.gcd (r * s) (r * d) = r := by
    rw [Nat.gcd_mul_left, hcoprime.symm.gcd_eq_one, mul_one]
  simpa only [hgcd] using hm

/-- The produced inactive mask supplies the common factor for the actual reciprocal inventory.
No class occurrence or starting position is deleted. -/
theorem inactive_short_detector_factor {α : Type*} [Fintype α] [DecidableEq α]
    {r d s : ℕ} [NeZero (r * d)] (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    (hcoprime : Nat.Coprime d s)
    (word : ZMod (r * d) → α) (a : α) (num den : α → Polynomial ℝ)
    (root sign : ℝ) (hroot : eval root (num a) = 0)
    (hsimple : rootMultiplicity root (num a) = 1)
    (hden : ∀ Y, 0 < eval root (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * eval root (num Y))
    (he : classDefect word 1 d s (r * s - 1) 0 a = 0)
    (hzero :
      let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
      RatFunc.C (s : ℝ) * (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) -
        RatFunc.C ((r * s : ℕ) : ℝ) *
          (windowProduct (response ∘ word) 1 (r * s - 1) 0)⁻¹ *
          (∑ Y, RatFunc.C (classDefect word 1 d s (r * s - 1) 0 Y : ℝ) *
            (response Y)⁻¹) = 0) :
    let response := fun Y => algebraMap (Polynomial ℝ) (RatFunc ℝ) (num Y) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (den Y)
    (∑ i, (windowProduct (response ∘ word) 1 (r * s) i)⁻¹) =
      (response a)⁻¹ ^ windowSum (classMask word a) 1 (r * s - 1) 0 *
        ∑ i, (windowProduct (peeledResponses a response ∘ word) 1 (r * s) i)⁻¹ := by
  dsimp only
  exact inverseWindowSum_class_factor word _ 1 (r * s) _ a
    (inactive_short_detector_mask hr hd hs hcoprime word a num den root sign
      hroot hsimple hden hsign he hzero).1

end SkewCornerDescent.CyclicWindows
