/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CutCodeFactorization

/-!
# Produced initial integer-periodic cut invariants

The initial stage of the factor-reversal reconstruction induction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The actual bounded signed period is extended through the same true
weight residues used by the full cut code.  The full-weight code period
supplies the other initial invariant.  Sorry-free.
-/

namespace SkewClassInflation

/-- A genuine bounded signed period becomes a full integer masked period at the same divisor. -/
theorem compositionCutSignInt_masked_period {N p : ℕ} (α : Composition N)
    (hN : 0 < N) (hp : 0 < p) (hd : p ∣ N)
    (hper : ∀ x, 0 < x → x + p < N → ¬ p ∣ x →
      compositionCutSign α (x + p) = compositionCutSign α x) :
    Function.Periodic (periodMask (compositionCutSignInt α) p) (p : ℤ) := by
  apply periodMask_periodic _ p p (dvd_refl p)
  intro z hz
  let x := compositionCutResidue N z
  let y := compositionCutResidue N (z + (p : ℤ))
  have hxN : x < N := compositionCutResidue_lt N hN z
  have hyN : y < N := compositionCutResidue_lt N hN (z + p)
  have hmx : x % p ≠ 0 := by
    intro hm
    exact hz ((compositionCutResidue_dvd N p hN hd z).mp (Nat.dvd_of_mod_eq_zero hm))
  have hres : y % p = x % p := by
    dsimp only [y, x]
    rw [compositionCutResidue_add_nat N hN z p]
    rw [Nat.mod_mod_of_dvd _ hd, Nat.add_mod_right]
  have hmy : y % p ≠ 0 := by rwa [hres]
  change compositionCutSign α y = compositionCutSign α x
  rw [off_multiple_period_mod (compositionCutSign α) hp hper y hyN hmy,
    off_multiple_period_mod (compositionCutSign α) hp hper x hxN hmx, hres]

/-- The actual full code has the whole-weight period after masking any aligned divisor. -/
theorem compositionCutCode_masked_whole_period {N p : ℕ} (α : Composition N)
    (hd : p ∣ N) :
    Function.Periodic (periodMask (compositionCutCode α) p) (N : ℤ) := by
  apply periodMask_periodic _ p N hd
  intro z _
  exact compositionCutCode_periodic α z

/-- A nonreconstructible source produces both initial period channels and a nonzero witness. -/
theorem nonreconstructible_initial_code_periods {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) :
    ∃ p k : ℕ, 1 < p ∧ p < N ∧ p ∣ N ∧ 0 < k ∧ k < N ∧ ¬ p ∣ k ∧
      compositionCutSign α k ≠ 0 ∧
      Function.Periodic (periodMask (compositionCutSignInt α) p) (p : ℤ) ∧
      Function.Periodic (periodMask (compositionCutCode α) p) (N : ℤ) := by
  obtain ⟨p, k, hp, hpN, hd, hk0, hkN, hpk, hnonzero, hperiod⟩ :=
    nonreconstructible_signed_period_witness α hn
  exact ⟨p, k, hp, hpN, hd, hk0, hkN, hpk, hnonzero,
    compositionCutSignInt_masked_period α (by omega) (by omega) hd hperiod,
    compositionCutCode_masked_whole_period α hd⟩

end SkewClassInflation
