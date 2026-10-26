/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.OverlapPeriods

/-!
# Integer periods with divisor-aligned holes

The period-assembly step in factor-reversal reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Masking exactly the exceptional multiples turns guarded translation
identities into genuine periods, which combine by the existing Bezout
period lemma.  Sorry-free.
-/

namespace SkewClassInflation

/-- Replace precisely the exceptional whole-period multiples by zero. -/
noncomputable def periodMask (F : ℤ → ℤ) (p : ℕ) (z : ℤ) : ℤ :=
  if (p : ℤ) ∣ z then 0 else F z

/-- Translating by a multiple of the divisor preserves membership in its exceptional set. -/
theorem period_divisibility_shift (d t : ℕ) (hd : d ∣ t) (z : ℤ) :
    (d : ℤ) ∣ z + (t : ℤ) ↔ (d : ℤ) ∣ z := by
  have ht : (d : ℤ) ∣ (t : ℤ) := Int.natCast_dvd_natCast.mpr hd
  exact dvd_add_left ht

/-- A guarded translation becomes a genuine period after masking exactly its divisor holes. -/
theorem periodMask_periodic (F : ℤ → ℤ) (d t : ℕ) (hd : d ∣ t)
    (hper : ∀ z : ℤ, ¬ (d : ℤ) ∣ z → F (z + (t : ℤ)) = F z) :
    Function.Periodic (periodMask F d) (t : ℤ) := by
  intro z
  have he := period_divisibility_shift d t hd z
  by_cases hz : (d : ℤ) ∣ z
  · simp only [periodMask, hz, he.mpr hz, ite_true]
  · have hzt : ¬ (d : ℤ) ∣ z + (t : ℤ) := fun h => hz (he.mp h)
    simp only [periodMask, hz, hzt, ite_false, hper z hz]

/-- A genuine masked period can be read back at every nonexceptional coordinate. -/
theorem periodMask_periodic_value (F : ℤ → ℤ) (d t : ℕ) (hd : d ∣ t)
    (hper : Function.Periodic (periodMask F d) (t : ℤ))
    (z : ℤ) (hz : ¬ (d : ℤ) ∣ z) : F (z + (t : ℤ)) = F z := by
  have hzt : ¬ (d : ℤ) ∣ z + (t : ℤ) :=
    fun h => hz ((period_divisibility_shift d t hd z).mp h)
  simpa only [periodMask, hz, hzt, ite_false] using hper z

/-- Enlarging the exceptional set only discards values, and preserves aligned genuine periods. -/
theorem periodMask_refine (F : ℤ → ℤ) (d p t : ℕ) (hdp : d ∣ p) (hdt : d ∣ t)
    (hper : Function.Periodic (periodMask F p) (t : ℤ)) :
    Function.Periodic (periodMask F d) (t : ℤ) := by
  apply periodMask_periodic F d t hdt
  intro z hz
  have hzp : ¬ (p : ℤ) ∣ z := fun h => hz ((Int.natCast_dvd_natCast.mpr hdp).trans h)
  have hzt : ¬ (p : ℤ) ∣ z + (t : ℤ) := by
    intro h
    have hh := (Int.natCast_dvd_natCast.mpr hdp).trans h
    exact hz ((period_divisibility_shift d t hdt z).mp hh)
  simpa only [periodMask, hzp, hzt, ite_false] using hper z

/-- The gcd of any finite family of genuine natural periods is itself a genuine period. -/
theorem periodic_finset_gcd {A : Type*} (F : ℤ → A) (T : Finset ℕ)
    (hper : ∀ t ∈ T, Function.Periodic F (t : ℤ)) :
    Function.Periodic F ((T.gcd id : ℕ) : ℤ) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.gcd_empty, Nat.cast_zero]
    intro z
    simp only [add_zero]
  | @insert t T ht ih =>
    rw [Finset.gcd_insert]
    apply periodic_nat_gcd F
    · exact hper t (Finset.mem_insert_self t T)
    · exact ih (fun u hu => hper u (Finset.mem_insert_of_mem hu))

/-- The old period and every actual frontier period supply their full gcd period. -/
theorem periodic_gcd_frontier {A : Type*} (F : ℤ → A) (q : ℕ) (T : Finset ℕ)
    (hq : Function.Periodic F (q : ℤ))
    (hT : ∀ t ∈ T, Function.Periodic F (t : ℤ)) :
    Function.Periodic F (q.gcd (T.gcd id) : ℤ) :=
  periodic_nat_gcd F q (T.gcd id) hq (periodic_finset_gcd F T hT)

/-- Every natural multiple of a genuine integer period remains a period. -/
theorem periodic_nat_of_dvd {A : Type*} (F : ℤ → A) (d t : ℕ) (hd : d ∣ t)
    (hper : Function.Periodic F (d : ℤ)) : Function.Periodic F (t : ℤ) := by
  obtain ⟨m, rfl⟩ := hd
  have hh := hper.int_mul (m : ℤ)
  simpa only [Nat.cast_mul, Int.cast_id, mul_comm] using hh

/-- A proposed period can be checked on one fundamental interval of an established period. -/
theorem periodic_of_residue_check {A : Type*} (F : ℤ → A) (N : ℕ) (hN : 0 < N) (t : ℤ)
    (hwhole : Function.Periodic F (N : ℤ))
    (hcheck : ∀ r : ℤ, 0 ≤ r → r < (N : ℤ) → F (r + t) = F r) :
    Function.Periodic F t := by
  intro z
  have h0 := Int.emod_nonneg z (show (N : ℤ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hN)
  have hlt := Int.emod_lt_of_pos z (show (0 : ℤ) < N by exact_mod_cast hN)
  have hvalue := periodic_int_remainder F (N : ℤ) hwhole z
  have hshift := periodic_int_remainder (fun x => F (x + t)) (N : ℤ)
    (hwhole.add_const t) z
  exact hshift.symm.trans ((hcheck (z % N) h0 hlt).trans hvalue)

end SkewClassInflation
