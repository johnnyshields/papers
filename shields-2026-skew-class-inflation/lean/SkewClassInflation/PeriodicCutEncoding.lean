/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.EvenCutClosure
import SkewClassInflation.MaskedPeriods

/-!
# Full cut encoding on the actual integer-periodic extension

The two-channel period invariant for factor-reversal reconstruction in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The signed channel alone identifies type-one cuts.  The full channel
also distinguishes zero-type from two-type coordinates.  Both are
computed from the actual composition and the same integer remainder.
Sorry-free.
-/

namespace SkewClassInflation

/-- The actual proper-weight residue of an arbitrary integer coordinate. -/
def compositionCutResidue (N : ℕ) (z : ℤ) : ℕ := (z % (N : ℤ)).toNat

/-- At a positive weight, the natural residue is the exact nonnegative integer remainder. -/
theorem compositionCutResidue_cast (N : ℕ) (hN : 0 < N) (z : ℤ) :
    (compositionCutResidue N z : ℤ) = z % (N : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by exact_mod_cast Nat.ne_of_gt hN))

/-- Every actual integer residue lies strictly below the positive whole weight. -/
theorem compositionCutResidue_lt (N : ℕ) (hN : 0 < N) (z : ℤ) :
    compositionCutResidue N z < N := by
  have hh := Int.emod_lt_of_pos z (show (0 : ℤ) < N by exact_mod_cast hN)
  rw [← compositionCutResidue_cast N hN z] at hh
  exact_mod_cast hh

/-- Proper natural coordinates retain exactly their original value. -/
theorem compositionCutResidue_nat (N x : ℕ) (hx : x < N) :
    compositionCutResidue N (x : ℤ) = x := by
  rw [compositionCutResidue, Int.emod_eq_of_lt (Int.natCast_nonneg x) (by exact_mod_cast hx),
    Int.toNat_natCast]

/-- The actual residue itself is periodic with the full whole weight. -/
theorem compositionCutResidue_periodic (N : ℕ) :
    Function.Periodic (compositionCutResidue N) (N : ℤ) := by
  intro z
  simp only [compositionCutResidue, Int.add_emod_right]

/-- Integer translation by a natural part agrees with the actual cyclic natural coordinate. -/
theorem compositionCutResidue_add_nat (N : ℕ) (hN : 0 < N) (z : ℤ) (t : ℕ) :
    compositionCutResidue N (z + (t : ℤ)) = (compositionCutResidue N z + t) % N := by
  have hh : (((compositionCutResidue N z + t) % N : ℕ) : ℤ) =
      (z + (t : ℤ)) % (N : ℤ) := by
    rw [Int.natCast_emod, Nat.cast_add, compositionCutResidue_cast N hN z,
      Int.add_emod, Int.emod_emod, ← Int.add_emod]
  have he := (compositionCutResidue_cast N hN (z + t)).trans hh.symm
  exact_mod_cast he

/-- Divisibility by a weight divisor is unchanged by the actual periodic residue. -/
theorem compositionCutResidue_dvd (N d : ℕ) (hN : 0 < N) (hd : d ∣ N) (z : ℤ) :
    d ∣ compositionCutResidue N z ↔ (d : ℤ) ∣ z := by
  rw [← Int.natCast_dvd_natCast, compositionCutResidue_cast N hN z]
  have hmul : (d : ℤ) ∣ (N : ℤ) * (z / (N : ℤ)) :=
    dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _
  have hh := (dvd_add_left hmul :
    (d : ℤ) ∣ z % (N : ℤ) + (N : ℤ) * (z / (N : ℤ)) ↔ (d : ℤ) ∣ z % (N : ℤ))
  rw [Int.emod_add_mul_ediv] at hh
  exact hh.symm

/-- The actual full code uses both the type and the signed channel. -/
noncomputable def compositionCutCodeNat {N : ℕ} (α : Composition N) (x : ℕ) : ℤ :=
  if compositionCutType α x = 1 then compositionCutSign α x else (compositionCutType α x : ℤ)

/-- The signed channel on the same actual integer-periodic extension. -/
noncomputable def compositionCutSignInt {N : ℕ} (α : Composition N) (z : ℤ) : ℤ :=
  compositionCutSign α (compositionCutResidue N z)

/-- The full cut code on the actual integer-periodic extension. -/
noncomputable def compositionCutCode {N : ℕ} (α : Composition N) (z : ℤ) : ℤ :=
  compositionCutCodeNat α (compositionCutResidue N z)

/-- Equal full codes are exactly equality of both actual underlying channels. -/
theorem compositionCutCodeNat_eq_iff {N : ℕ} (α : Composition N) (x y : ℕ) :
    compositionCutCodeNat α x = compositionCutCodeNat α y ↔
      compositionCutType α x = compositionCutType α y ∧
        compositionCutSign α x = compositionCutSign α y := by
  classical
  unfold compositionCutCodeNat compositionCutType compositionCutSign
  split_ifs <;> omega

/-- The full code identifies actual unreflected cut membership without an even-type ambiguity. -/
theorem compositionCutCodeNat_cut_iff {N : ℕ} (α : Composition N) (x : ℕ) :
    x ∈ properCuts α ↔ compositionCutCodeNat α x = 1 ∨ compositionCutCodeNat α x = 2 := by
  classical
  unfold compositionCutCodeNat compositionCutType compositionCutSign
  split_ifs <;> simp_all

/-- Equal signed channels leave only the possibility of disagreeing even types. -/
theorem compositionCutCodeNat_disagreement {N : ℕ} (α : Composition N) (x y : ℕ)
    (hsign : compositionCutSign α x = compositionCutSign α y)
    (hne : compositionCutCodeNat α x ≠ compositionCutCodeNat α y) :
    compositionCutType α x ≠ 1 ∧ compositionCutType α y ≠ 1 ∧
      compositionCutType α x ≠ compositionCutType α y := by
  classical
  unfold compositionCutCodeNat compositionCutType compositionCutSign at *
  split_ifs at * <;> omega

/-- Both actual integer channels retain their genuine full-weight period. -/
theorem compositionCutSignInt_periodic {N : ℕ} (α : Composition N) :
    Function.Periodic (compositionCutSignInt α) (N : ℤ) := by
  intro z
  simp only [compositionCutSignInt, compositionCutResidue_periodic N z]

/-- The full actual cut code retains its genuine full-weight period. -/
theorem compositionCutCode_periodic {N : ℕ} (α : Composition N) :
    Function.Periodic (compositionCutCode α) (N : ℤ) := by
  intro z
  simp only [compositionCutCode, compositionCutResidue_periodic N z]

end SkewClassInflation
