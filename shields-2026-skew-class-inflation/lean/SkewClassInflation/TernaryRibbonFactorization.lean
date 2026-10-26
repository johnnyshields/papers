/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SmallRibbonReconstruction
import SkewClassInflation.StableCutCodeFactorization

/-!
# Proper factorization at a ternary signed period

The period-three branch of factor-reversal necessity in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Odd reflection and a nonzero witness force both nonzero residue classes
to have nonzero signed code.  No even discrepancy is then possible,
so the full-code factor constructor applies without a propagation input.
Sorry-free.
-/

namespace SkewClassInflation

/-- An odd function of period three with a nonzero value has no nonmultiple zero. -/
theorem odd_three_periodic_ne_zero (F : ℤ → ℤ)
    (hperiod : Function.Periodic F (3 : ℤ)) (hodd : ∀ z, F (-z) = -F z)
    (w : ℤ) (hw : F w ≠ 0) (z : ℤ) (hz : ¬ (3 : ℤ) ∣ z) : F z ≠ 0 := by
  have h0 : F 0 = 0 := by
    have hh := hodd 0
    simp only [neg_zero] at hh
    omega
  have h12 : F 2 = -F 1 := by
    have hh := hperiod (-1)
    have hn := hodd 1
    norm_num at hh
    omega
  have hres (a : ℤ) : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
    have := Int.emod_nonneg a (by decide : (3 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos a (by decide : (0 : ℤ) < 3)
    omega
  have h1 : F 1 ≠ 0 := by
    intro he
    have hh := periodic_int_remainder F 3 hperiod w
    rcases hres w with hr | hr | hr <;> rw [hr] at hh
    · exact hw (hh.symm.trans h0)
    · exact hw (hh.symm.trans he)
    · exact hw (by rw [← hh, h12, he, neg_zero])
  have hr := periodic_int_remainder F 3 hperiod z
  rcases hres z with he | he | he
  · exact (hz (Int.dvd_of_emod_eq_zero he)).elim
  · rw [he] at hr
    exact fun hh => h1 (hr.trans hh)
  · rw [he] at hr
    intro hh
    have := hr.trans hh
    rw [h12] at this
    exact h1 (by omega)

/-- A genuine ternary initial signed period has an empty actual even-discrepancy frontier. -/
theorem undetermined_evenCutDisagreements_eq_empty_of_gcd_three {N : ℕ}
    (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hg : undeterminedGcd α k = 3) :
    evenCutDisagreements α (undeterminedGcd α k) (undeterminedCuts α k) = ∅ := by
  classical
  have hkb := properCuts_bounds α k hk
  have hN : 0 < N := by omega
  obtain ⟨_, _, hd, hnot, hperiod⟩ := undeterminedGcd_signed_period α k hk hkr hfirst hne
  have hP := compositionCutSignInt_masked_period α hN (by omega) hd hperiod
  let F := periodMask (compositionCutSignInt α) (undeterminedGcd α k)
  have hPF : Function.Periodic F (undeterminedGcd α k : ℤ) := hP
  have hP3' := (congrArg (fun q : ℕ => Function.Periodic F (q : ℤ)) hg).mp hPF
  have hP3 : Function.Periodic F (3 : ℤ) := by simpa only [Nat.cast_ofNat] using hP3'
  have hodd : ∀ z, F (-z) = -F z :=
    periodMask_neg _ _ (compositionCutSignInt_neg α hN)
  have hFk : F (k : ℤ) ≠ 0 := by
    have hki : ¬ (undeterminedGcd α k : ℤ) ∣ (k : ℤ) :=
      fun hh => hnot (Int.natCast_dvd_natCast.mp hh)
    simp only [F, periodMask, hki, ite_false, compositionCutSignInt,
      compositionCutResidue_nat N k hkb.2, compositionCutSign,
      hk, hkr, ite_true, ite_false, sub_zero]
    decide
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hb := evenCutDisagreements_bounds α _ _ x hx
  have hx3 : ¬ (3 : ℤ) ∣ (x : ℤ) := by
    intro hh
    apply hb.2.2
    rw [hg]
    exact Int.natCast_dvd_natCast.mp hh
  have hFx := odd_three_periodic_ne_zero F hP3 hodd (k : ℤ) hFk (x : ℤ) hx3
  obtain ⟨_, _, _, heven, _, _⟩ := (Finset.mem_filter.mp hx).2
  have hxi : ¬ (undeterminedGcd α k : ℤ) ∣ (x : ℤ) :=
    fun hh => hb.2.2 (Int.natCast_dvd_natCast.mp hh)
  apply hFx
  simp only [F, periodMask, hxi, ite_false, compositionCutSignInt,
    compositionCutResidue_nat N x hb.2.1,
    compositionCutSign_eq_zero_of_not_one α x heven]

/-- The ternary branch supplies literal proper factors without an odd-propagation hypothesis. -/
theorem undetermined_factorization_of_gcd_three {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hg : undeterminedGcd α k = 3) :
    ∃ m : ℕ, 2 ≤ m ∧ m * 3 = N ∧ ∃ δ : Composition m, ∃ ε : Composition 3,
      (compositionProduct δ ε).blocks = α.blocks := by
  have hh := undetermined_factorization_of_stable_frontier_at_gcd α k hk hkr hfirst hne
    (undetermined_evenCutDisagreements_eq_empty_of_gcd_three α k hk hkr hfirst hne hg)
  rw [hg] at hh
  exact hh

end SkewClassInflation
