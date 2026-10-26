/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.MaskedPeriods
import Mathlib.Data.ZMod.Basic

/-!
# Period extension from nonzero support on a finite cycle

The nonvanishing-witness step in factor-reversal reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
A finite permutation cannot introduce new nonzero values while fixing
every existing nonzero value: the sum of absolute values is unchanged.
This turns one-sided odd-point propagation into a genuine period.
Sorry-free.
-/

namespace SkewClassInflation

/-- A finite permutation preserving each nonzero value preserves every value. -/
theorem nonzero_forward_perm_invariant {ι : Type*} [Finite ι]
    (σ : Equiv.Perm ι) (f : ι → ℤ)
    (hforward : ∀ x, f x ≠ 0 → f (σ x) = f x) : ∀ x, f (σ x) = f x := by
  classical
  let _ := Fintype.ofFinite ι
  have hle : ∀ x ∈ Finset.univ, (f x).natAbs ≤ (f (σ x)).natAbs := by
    intro x _
    by_cases hx : f x = 0
    · rw [hx, Int.natAbs_zero]
      exact Nat.zero_le _
    · rw [hforward x hx]
  have hsum : (∑ x, (f x).natAbs) = ∑ x, (f (σ x)).natAbs := by
    exact (Equiv.sum_comp σ (fun x => (f x).natAbs)).symm
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  intro x
  by_cases hx : f x = 0
  · have habs : (f (σ x)).natAbs = 0 := by
      rw [← he x (Finset.mem_univ x), hx, Int.natAbs_zero]
    rw [Int.natAbs_eq_zero.mp habs, hx]
  · exact hforward x hx

/-- Nonzero-value propagation extends to a genuine period on an established finite residue cycle. -/
theorem periodic_of_nonzero_forward (F : ℤ → ℤ) (p : ℕ) (hp : 0 < p) (t : ℕ)
    (hperiod : Function.Periodic F (p : ℤ))
    (hforward : ∀ z : ℤ, F z ≠ 0 → F (z + (t : ℤ)) = F z) :
    Function.Periodic F (t : ℤ) := by
  classical
  let _ : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let G : ZMod p → ℤ := fun x => F (x.val : ℤ)
  have hdescend (z : ℤ) : G (z : ZMod p) = F z := by
    have hh := periodic_int_remainder F (p : ℤ) hperiod z
    rw [← ZMod.val_intCast z] at hh
    exact hh
  let σ : Equiv.Perm (ZMod p) := Equiv.addRight (t : ZMod p)
  have hGF : ∀ x : ZMod p, G x ≠ 0 → G (σ x) = G x := by
    intro x hx
    have hh := hforward (x.val : ℤ) hx
    have hcast : (((x.val : ℤ) + (t : ℤ) : ℤ) : ZMod p) = σ x := by
      simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val,
        σ, Equiv.coe_addRight]
    rw [← hdescend ((x.val : ℤ) + t), hcast] at hh
    exact hh
  have hall := nonzero_forward_perm_invariant σ G hGF
  intro z
  rw [← hdescend (z + t), ← hdescend z]
  rw [Int.cast_add, Int.cast_natCast]
  exact hall (z : ZMod p)

/-- An even endpoint prevents odd-point propagation from entering an old-period hole. -/
theorem masked_period_of_odd_shift_zero (F : ℤ → ℤ) (p : ℕ) (hp : 0 < p) (t : ℕ)
    (hperiod : Function.Periodic (periodMask F p) (p : ℤ))
    (hzero : F (-(t : ℤ)) = 0)
    (hodd : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → F z ≠ 0 → F (z + (t : ℤ)) = F z) :
    Function.Periodic (periodMask F p) (t : ℤ) := by
  apply periodic_of_nonzero_forward (periodMask F p) p hp t hperiod
  intro z hz
  have hzp : ¬ (p : ℤ) ∣ z := by
    intro hd
    exact hz (by simp only [periodMask, hd, ite_true])
  have hFz : F z ≠ 0 := by simpa only [periodMask, hzp, ite_false] using hz
  have hneg : periodMask F p (-(t : ℤ)) = 0 := by
    simp only [periodMask, hzero, ite_self]
  have hnext : ¬ (p : ℤ) ∣ z + (t : ℤ) := by
    rintro ⟨a, ha⟩
    have hh := hperiod.int_mul a (-(t : ℤ))
    simp only [Int.cast_id] at hh
    have hcoord : -(t : ℤ) + a * (p : ℤ) = z := by
      have he : a * (p : ℤ) = z + t := by rw [mul_comm]; exact ha.symm
      omega
    rw [hcoord, hneg] at hh
    exact hz hh
  simp only [periodMask, hzp, hnext, ite_false, hodd z hzp hFz]

end SkewClassInflation
