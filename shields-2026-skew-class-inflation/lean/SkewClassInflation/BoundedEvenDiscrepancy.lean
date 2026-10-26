/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SignedCutArithmetic

/-!
# Produced four-part options in the actual bounded discrepancy window

The bounded counting stage of even-discrepancy reconstruction for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The actual initial gcd supplies the sign shifts and determination of
all six other subset coordinates.  No mate, subset-determination
family, or four-part coefficient is assumed.  Sorry-free.
-/

namespace SkewClassInflation

/-- An actual undetermined even discrepancy supplies both full-code options in its true window. -/
theorem undetermined_even_discrepancy_options {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (m : ℕ) (hm : m ∈ undeterminedCuts α k) (x z : ℕ)
    (hx0 : 0 < x) (hz0 : 0 < z) (htotal : m + x + z < N)
    (hx : ¬ undeterminedGcd α k ∣ x) (hz : ¬ undeterminedGcd α k ∣ z)
    (hxe : compositionCutType α x ≠ 1) (hmxe : compositionCutType α (m + x) ≠ 1)
    (hdisagree : compositionCutType α x ≠ compositionCutType α (m + x))
    (hzs : compositionCutType α z = 1) :
    (compositionCutCodeNat α (x + z) = compositionCutCodeNat α z ∧
      compositionCutCodeNat α (m + x + z) = compositionCutCodeNat α z) ∨
    (compositionCutCodeNat α (x + z) = compositionCutCodeNat α x ∧
      compositionCutCodeNat α (m + x + z) = compositionCutCodeNat α (m + x)) := by
  classical
  have hmb := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
  obtain ⟨hp, _, hpN, _, hperiod⟩ :=
    undeterminedGcd_signed_period α k hk hkr hfirst ⟨m, hm⟩
  have hmdiv := undeterminedGcd_dvd α k m hm
  have hshift := cutSign_shift_of_divisor_period α (by omega) hperiod m z hmdiv
    (by omega) (by omega) hz
  have hsignz := compositionCutSign_ne_zero_of_one α z hzs
  have hsignmz : compositionCutSign α (m + z) ≠ 0 := by rwa [hshift]
  have hmzs := compositionCutType_one_of_nonzero_sign α (m + z) hsignmz
  have hmx := actualCutBool_even_opposite α x (m + x) hxe hmxe hdisagree
  have hmz := actualCutBool_eq_of_nonzero_sign_eq α (m + z) z hshift hsignmz
  have hxz := not_dvd_even_single_sum α (by omega) hpN hperiod x z (by omega)
    hz0 (by omega) hx hxe hzs
  have hnotAdd (y : ℕ) (hy : ¬ undeterminedGcd α k ∣ y) :
      ¬ undeterminedGcd α k ∣ m + y := by
    intro hh
    exact hy ((Nat.dvd_add_iff_right hmdiv).mpr hh)
  have hdet : ∀ y ∈ ({x, z, m + x, m + z, x + z, m + x + z} : Finset ℕ),
      cutDetermined α k y := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with he | he | he | he | he | he <;> subst y
    · exact cutDetermined_of_undeterminedGcd_not_dvd α k x hx0 (by omega) hx
    · exact cutDetermined_of_undeterminedGcd_not_dvd α k z hz0 (by omega) hz
    · exact cutDetermined_of_undeterminedGcd_not_dvd α k (m + x) (by omega) (by omega)
        (hnotAdd x hx)
    · exact cutDetermined_of_undeterminedGcd_not_dvd α k (m + z) (by omega) (by omega)
        (hnotAdd z hz)
    · exact cutDetermined_of_undeterminedGcd_not_dvd α k (x + z) (by omega) (by omega) hxz
    · exact cutDetermined_of_undeterminedGcd_not_dvd α k (m + x + z) (by omega) (by omega)
        (by simpa only [Nat.add_assoc] using hnotAdd (x + z) hxz)
  have hs := cutSign_shift_of_divisor_period α (by omega) hperiod m (x + z) hmdiv
    (by omega) (by omega) hxz
  apply undetermined_fourPart_alternatives α k
    ⟨m, hmb.1⟩ ⟨x, hx0⟩ ⟨z, hz0⟩ ⟨N - (m + x + z), by omega⟩
    (by dsimp; omega) hm hxe hmxe hzs hmzs hmx hmz hdet
  change compositionCutSign α (x + z) = compositionCutSign α (m + x + z)
  simpa only [Nat.add_assoc] using hs.symm

end SkewClassInflation
