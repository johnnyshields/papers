/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NonzeroSupportPeriods

/-!
# Strong signed-period refinement preserving nonzero witnesses

The nontrivial-period invariant for factor-reversal reconstruction in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Actual zero endpoints make the old masked function periodic under each
frontier generator.  Its gcd period therefore vanishes on every new
multiple.  The refined mask is the same function, so an actual nonzero
witness cannot become an exceptional multiple.  Sorry-free.
-/

namespace SkewClassInflation

/-- Zero endpoints and odd propagation give the gcd period of the unchanged old mask. -/
theorem zero_frontier_masked_periods (F : ℤ → ℤ) (p : ℕ) (hp : 0 < p) (D : Finset ℕ)
    (hP : Function.Periodic (periodMask F p) (p : ℤ))
    (hzero : ∀ t ∈ D, F (-(t : ℤ)) = 0)
    (hodd : ∀ t ∈ D, ∀ z : ℤ, ¬ (p : ℤ) ∣ z → F z ≠ 0 → F (z + (t : ℤ)) = F z) :
    Function.Periodic (periodMask F p) (p.gcd (D.gcd id) : ℤ) := by
  apply periodic_gcd_frontier (periodMask F p) p D hP
  intro t ht
  exact masked_period_of_odd_shift_zero F p hp t hP (hzero t ht) (hodd t ht)

/-- The unchanged old mask vanishes on every multiple of its refined gcd period. -/
theorem zero_frontier_mask_vanishes (F : ℤ → ℤ) (p : ℕ) (hp : 0 < p) (D : Finset ℕ)
    (hP : Function.Periodic (periodMask F p) (p : ℤ))
    (hzero : ∀ t ∈ D, F (-(t : ℤ)) = 0)
    (hodd : ∀ t ∈ D, ∀ z : ℤ, ¬ (p : ℤ) ∣ z → F z ≠ 0 → F (z + (t : ℤ)) = F z)
    (z : ℤ) (hz : (p.gcd (D.gcd id) : ℤ) ∣ z) : periodMask F p z = 0 := by
  have hperiod := zero_frontier_masked_periods F p hp D hP hzero hodd
  obtain ⟨a, ha⟩ := hz
  have hh := hperiod.int_mul a 0
  simp only [Int.cast_id, zero_add] at hh
  have hcoord : a * (p.gcd (D.gcd id) : ℤ) = z := by rw [mul_comm]; exact ha.symm
  rw [hcoord] at hh
  simpa only [periodMask, dvd_zero, ite_true] using hh

/-- Refining the mask removes only values already proved zero. -/
theorem zero_frontier_masks_eq (F : ℤ → ℤ) (p : ℕ) (hp : 0 < p) (D : Finset ℕ)
    (hP : Function.Periodic (periodMask F p) (p : ℤ))
    (hzero : ∀ t ∈ D, F (-(t : ℤ)) = 0)
    (hodd : ∀ t ∈ D, ∀ z : ℤ, ¬ (p : ℤ) ∣ z → F z ≠ 0 → F (z + (t : ℤ)) = F z) :
    periodMask F p = periodMask F (p.gcd (D.gcd id)) := by
  funext z
  by_cases hz : (p.gcd (D.gcd id) : ℤ) ∣ z
  · rw [zero_frontier_mask_vanishes F p hp D hP hzero hodd z hz]
    simp only [periodMask, hz, ite_true]
  · have hzp : ¬ (p : ℤ) ∣ z := by
      intro h
      exact hz ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left p (D.gcd id))).trans h)
    simp only [periodMask, hz, hzp, ite_false]

/-- Nonzero off-period witnesses stay off the new period, so that period exceeds one. -/
theorem zero_frontier_preserves_nonzero_witness (F : ℤ → ℤ) (p : ℕ) (hp : 0 < p)
    (D : Finset ℕ) (k : ℕ) (hk : ¬ p ∣ k) (hFk : F (k : ℤ) ≠ 0)
    (hP : Function.Periodic (periodMask F p) (p : ℤ))
    (hzero : ∀ t ∈ D, F (-(t : ℤ)) = 0)
    (hodd : ∀ t ∈ D, ∀ z : ℤ, ¬ (p : ℤ) ∣ z → F z ≠ 0 → F (z + (t : ℤ)) = F z) :
    1 < p.gcd (D.gcd id) ∧ ¬ p.gcd (D.gcd id) ∣ k ∧
      Function.Periodic (periodMask F (p.gcd (D.gcd id))) (p.gcd (D.gcd id) : ℤ) := by
  have hnot : ¬ p.gcd (D.gcd id) ∣ k := by
    intro hd
    have hh := zero_frontier_mask_vanishes F p hp D hP hzero hodd (k : ℤ)
      (Int.natCast_dvd_natCast.mpr hd)
    have hki : ¬ (p : ℤ) ∣ (k : ℤ) := fun h => hk (Int.natCast_dvd_natCast.mp h)
    simp only [periodMask, hki, ite_false] at hh
    exact hFk hh
  have hpos : 0 < p.gcd (D.gcd id) := Nat.gcd_pos_of_pos_left _ hp
  have hgt : 1 < p.gcd (D.gcd id) := by
    by_contra hle
    have he : p.gcd (D.gcd id) = 1 := by omega
    exact hnot (by rw [he]; exact one_dvd k)
  refine ⟨hgt, hnot, ?_⟩
  rw [← zero_frontier_masks_eq F p hp D hP hzero hodd]
  exact zero_frontier_masked_periods F p hp D hP hzero hodd

end SkewClassInflation
