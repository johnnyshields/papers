/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.IntegerCutSigns
import SkewClassInflation.InitialCutCodePeriods

/-!
# The nontrivial size bounds in ribbon reconstruction

The small-weight base cases for the ribbon factor-reversal classification cited after
`thm:sharp-inflation` in `shields-2026-skew-class-inflation.tex`.
The actual signed period has size at least three.  A nonempty
undetermined set also requires at least three period copies, since
its only candidate at two copies would be a forbidden single-type
midpoint.  Every ribbon of weight at most eight is reconstructible.
Sorry-free.
-/

namespace SkewClassInflation

/-- Masking divisor multiples preserves actual odd reflection. -/
theorem periodMask_neg (F : ℤ → ℤ) (p : ℕ) (hodd : ∀ z, F (-z) = -F z) (z : ℤ) :
    periodMask F p (-z) = -periodMask F p z := by
  classical
  have hd : (p : ℤ) ∣ -z ↔ (p : ℤ) ∣ z := dvd_neg
  simp only [periodMask, hd, hodd]
  split_ifs <;> simp only [neg_zero]

/-- An odd integer-valued function with period two vanishes identically. -/
theorem odd_two_periodic_eq_zero (F : ℤ → ℤ)
    (hperiod : Function.Periodic F (2 : ℤ)) (hodd : ∀ z, F (-z) = -F z) (z : ℤ) :
    F z = 0 := by
  have h0 := hodd 0
  simp only [neg_zero] at h0
  have hz0 : F 0 = 0 := by omega
  have h1 := hperiod (-1)
  have hm1 := hodd 1
  have hz1 : F 1 = 0 := by norm_num at h1; omega
  have hr := periodic_int_remainder F 2 hperiod z
  have hnonneg := Int.emod_nonneg z (by decide : (2 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos z (by decide : (0 : ℤ) < 2)
  have hcases : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rcases hcases with he | he
  · rw [he, hz0] at hr
    exact hr.symm
  · rw [he, hz1] at hr
    exact hr.symm

/-- The genuine initial signed period has size at least three. -/
theorem undeterminedGcd_ge_three {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) : 3 ≤ undeterminedGcd α k := by
  have hkb := properCuts_bounds α k hk
  have hN : 0 < N := by omega
  obtain ⟨hp, _, hd, hnot, hperiod⟩ := undeterminedGcd_signed_period α k hk hkr hfirst hne
  have hP := compositionCutSignInt_masked_period (p := undeterminedGcd α k) α hN
    (by omega) hd hperiod
  let F := periodMask (compositionCutSignInt α) (undeterminedGcd α k)
  have hodd : ∀ z, F (-z) = -F z :=
    periodMask_neg (compositionCutSignInt α) (undeterminedGcd α k)
      (compositionCutSignInt_neg α hN)
  have hFk : F (k : ℤ) ≠ 0 := by
    have hki : ¬ (undeterminedGcd α k : ℤ) ∣ (k : ℤ) :=
      fun h => hnot (Int.natCast_dvd_natCast.mp h)
    dsimp only [F]
    simp only [periodMask, hki, ite_false, compositionCutSignInt,
      compositionCutResidue_nat N k hkb.2, compositionCutSign,
      hk, hkr, ite_true, ite_false, sub_zero]
    decide
  by_contra hlt
  have he : undeterminedGcd α k = 2 := by omega
  have hPF : Function.Periodic F (undeterminedGcd α k : ℤ) := hP
  have hP2' := (congrArg (fun q : ℕ => Function.Periodic F (q : ℤ)) he).mp hPF
  have hP2 : Function.Periodic F (2 : ℤ) := by simpa only [Nat.cast_ofNat] using hP2'
  exact hFk (odd_two_periodic_eq_zero F hP2 hodd (k : ℤ))

/-- A nonempty actual undetermined frontier needs at least three copies of its gcd period. -/
theorem three_mul_undeterminedGcd_le {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) : 3 * undeterminedGcd α k ≤ N := by
  classical
  let p := undeterminedGcd α k
  have hp : 0 < p := undeterminedGcd_pos α k hne
  have hpN : p < N := undeterminedGcd_lt_weight α k hne
  obtain ⟨q, hq⟩ := undeterminedGcd_dvd_weight α k hne
  by_contra hbound
  have hq2 : q = 2 := by nlinarith
  have hN : N = 2 * p := by rw [hq, hq2]; ring
  obtain ⟨m, hm⟩ := hne
  have hb := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
  obtain ⟨a, ha⟩ := undeterminedGcd_dvd α k m hm
  have ha1 : a = 1 := by nlinarith
  have hmp : m = p := by rw [ha, ha1, Nat.mul_one]
  have ht := undeterminedCuts_type_one α k m hm
  have href : N - m = m := by omega
  unfold compositionCutType at ht
  rw [href] at ht
  split_ifs at ht <;> omega

/-- Nonreconstructible ribbon sources have weight at least nine. -/
theorem nine_le_weight_of_not_reconstructible {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) : 9 ≤ N := by
  obtain ⟨γ, k, _, _, hnγ, _, _, _, hk, hkr, hfirst⟩ :=
    exists_normalized_first_single_cut α hn
  have hne := undeterminedCuts_nonempty γ hnγ k hk hkr
  have hp := undeterminedGcd_ge_three γ k hk hkr hfirst hne
  have hN := three_mul_undeterminedGcd_le γ k hne
  omega

/-- Every source up through weight eight is reconstructed by its actual inventory up to reversal. -/
theorem ribbonReconstructible_of_small_weight {N : ℕ} (α : Composition N) (hN : N ≤ 8) :
    ribbonReconstructible α := by
  by_contra hn
  have hh := nine_le_weight_of_not_reconstructible α hn
  omega

/-- All small-weight actual mates are generated by a whole-word reversal. -/
theorem ribbonFactorComplete_of_small_weight {N : ℕ} (α : Composition N) (hN : N ≤ 8) :
    ribbonFactorComplete α :=
  ribbonFactorComplete_of_reconstructible α (ribbonReconstructible_of_small_weight α hN)

end SkewClassInflation
