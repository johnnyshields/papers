/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.UndeterminedFourPart
import SkewClassInflation.InitialCutCodePeriods
import Mathlib.Data.Nat.ModEq

/-!
# Actual signed-period arithmetic for discrepancy propagation

The arithmetic suppliers in the even-discrepancy step for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Whole candidate-period shifts preserve the actual signed channel.
An even point cannot have residue opposite to a nonzero single point,
and off-gcd coordinates are determined by the actual mate class.
Sorry-free.
-/

namespace SkewClassInflation

/-- An off-gcd actual proper coordinate is determined by the normalized inventory class. -/
theorem cutDetermined_of_undeterminedGcd_not_dvd {N : ℕ} (α : Composition N)
    (k y : ℕ) (hy0 : 0 < y) (hyN : y < N) (hn : ¬ undeterminedGcd α k ∣ y) :
    cutDetermined α k y :=
  cutDetermined_of_prefix_divisibility α k (undeterminedGcd α k) N
    (fun j hj _ => undeterminedGcd_dvd α k j hj) y hy0 hyN le_rfl hn

/-- Every whole candidate-period shift preserves the signed channel at true off-multiple points. -/
theorem cutSign_shift_of_divisor_period {N p : ℕ} (α : Composition N) (hp : 0 < p)
    (hper : ∀ x, 0 < x → x + p < N → ¬ p ∣ x →
      compositionCutSign α (x + p) = compositionCutSign α x)
    (m z : ℕ) (hm : p ∣ m) (hzN : z < N) (hmzN : m + z < N) (hz : ¬ p ∣ z) :
    compositionCutSign α (m + z) = compositionCutSign α z := by
  have hzmod : z % p ≠ 0 := fun he => hz (Nat.dvd_of_mod_eq_zero he)
  have hmod : (m + z) % p = z % p := by
    simp only [Nat.add_mod, Nat.mod_eq_zero_of_dvd hm, zero_add, Nat.mod_mod]
  have hmzmod : (m + z) % p ≠ 0 := by rwa [hmod]
  rw [off_multiple_period_mod (compositionCutSign α) hp hper (m + z) hmzN hmzmod,
    off_multiple_period_mod (compositionCutSign α) hp hper z hzN hzmod, hmod]

/-- An actual nonzero signed value has type one. -/
theorem compositionCutType_one_of_nonzero_sign {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : compositionCutSign α x ≠ 0) : compositionCutType α x = 1 := by
  by_contra ht
  exact hx (compositionCutSign_eq_zero_of_not_one α x ht)

/-- Equal nonzero signed values identify the actual full codes, not just cut membership. -/
theorem cutCodeNat_eq_of_nonzero_sign_eq {N : ℕ} (α : Composition N) (x y : ℕ)
    (he : compositionCutSign α x = compositionCutSign α y)
    (hx : compositionCutSign α x ≠ 0) :
    compositionCutCodeNat α x = compositionCutCodeNat α y := by
  by_contra hn
  have hh := compositionCutCodeNat_disagreement α x y he hn
  exact hx (compositionCutSign_eq_zero_of_not_one α x hh.1)

/-- Equal nonzero signed values identify the actual Boolean indicators. -/
theorem actualCutBool_eq_of_nonzero_sign_eq {N : ℕ} (α : Composition N) (x y : ℕ)
    (he : compositionCutSign α x = compositionCutSign α y)
    (hx : compositionCutSign α x ≠ 0) : actualCutBool α x = actualCutBool α y := by
  classical
  have hh := cut_membership_of_nonzero_sign_eq α x y he hx
  by_cases hA : x ∈ properCuts α <;> by_cases hB : y ∈ properCuts α <;>
    simp_all [actualCutBool]

/-- An off-period even point cannot be the negative residue of an actual single-type point. -/
theorem not_dvd_even_single_sum {N p : ℕ} (α : Composition N) (hp : 0 < p) (hpN : p ∣ N)
    (hper : ∀ x, 0 < x → x + p < N → ¬ p ∣ x →
      compositionCutSign α (x + p) = compositionCutSign α x)
    (x z : ℕ) (hxN : x < N) (hz0 : 0 < z) (hzN : z < N)
    (hx : ¬ p ∣ x)
    (hxe : compositionCutType α x ≠ 1) (hzs : compositionCutType α z = 1) :
    ¬ p ∣ x + z := by
  intro hsum
  have hsumMod : x + z ≡ (N - z) + z [MOD p] := by
    change (x + z) % p = (N - z + z) % p
    rw [Nat.sub_add_cancel hzN.le, Nat.mod_eq_zero_of_dvd hsum, Nat.mod_eq_zero_of_dvd hpN]
  have hres := Nat.ModEq.add_right_cancel' z hsumMod
  have hxmod : x % p ≠ 0 := fun he => hx (Nat.dvd_of_mod_eq_zero he)
  have hrmod : (N - z) % p ≠ 0 := by
    change x % p = (N - z) % p at hres
    rwa [← hres]
  have hsx := off_multiple_period_mod (compositionCutSign α) hp hper x hxN hxmod
  have hsr := off_multiple_period_mod (compositionCutSign α) hp hper (N - z) (by omega) hrmod
  have he : compositionCutSign α x = compositionCutSign α (N - z) := by
    rw [hsx, hsr]
    exact congrArg (compositionCutSign α) hres
  rw [compositionCutSign_eq_zero_of_not_one α x hxe,
    compositionCutSign_reflect α z hzN.le] at he
  have hn := compositionCutSign_ne_zero_of_one α z hzs
  omega

end SkewClassInflation
