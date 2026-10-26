/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.TernaryRibbonFactorization
import SkewClassInflation.EvenCutDiscrepancyWindows

/-!
# Proper factorization at a quaternary signed period

The period-four branch of factor-reversal necessity in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The signed channel has opposite nonzero odd residues and zero even
residues.  The actual four-part inventory alternatives exclude an
even discrepancy in a true positive window, without lifting the source.
Sorry-free.
-/

namespace SkewClassInflation

/-- Odd reflection fixes every residue of a four-periodic function from its value at one. -/
theorem odd_four_periodic_values (F : ℤ → ℤ)
    (hperiod : Function.Periodic F (4 : ℤ)) (hodd : ∀ z, F (-z) = -F z) (z : ℤ) :
    F z = if z % 4 = 1 then F 1 else if z % 4 = 3 then -F 1 else 0 := by
  have h0 : F 0 = 0 := by
    have hh := hodd 0
    simp only [neg_zero] at hh
    omega
  have h2 : F 2 = 0 := by
    have hh := hperiod (-2)
    have hn := hodd 2
    norm_num at hh
    omega
  have h3 : F 3 = -F 1 := by
    have hh := hperiod (-1)
    have hn := hodd 1
    norm_num at hh
    omega
  have hr := periodic_int_remainder F 4 hperiod z
  have hnonneg := Int.emod_nonneg z (by decide : (4 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos z (by decide : (0 : ℤ) < 4)
  have hc : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
  rcases hc with he | he | he | he <;> rw [he] at hr ⊢ <;>
    norm_num [← hr, h0, h2, h3]

/-- A genuine quaternary period gives the four-residue form for every proper signed code. -/
theorem undetermined_signed_values_of_gcd_four {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hg : undeterminedGcd α k = 4) :
    ∃ a : ℤ, a ≠ 0 ∧ ∀ x : ℕ, x < N → ¬ 4 ∣ x →
      compositionCutSign α x = if x % 4 = 1 then a else if x % 4 = 3 then -a else 0 := by
  classical
  have hkb := properCuts_bounds α k hk
  have hN : 0 < N := by omega
  obtain ⟨_, _, hd, hnot, hperiod⟩ := undeterminedGcd_signed_period α k hk hkr hfirst hne
  have hP := compositionCutSignInt_masked_period α hN (by omega) hd hperiod
  let F := periodMask (compositionCutSignInt α) (undeterminedGcd α k)
  have hPF : Function.Periodic F (undeterminedGcd α k : ℤ) := hP
  have hP4' := (congrArg (fun q : ℕ => Function.Periodic F (q : ℤ)) hg).mp hPF
  have hP4 : Function.Periodic F (4 : ℤ) := by simpa only [Nat.cast_ofNat] using hP4'
  have hodd : ∀ z, F (-z) = -F z :=
    periodMask_neg _ _ (compositionCutSignInt_neg α hN)
  have hFk : F (k : ℤ) ≠ 0 := by
    have hki : ¬ (undeterminedGcd α k : ℤ) ∣ (k : ℤ) :=
      fun hh => hnot (Int.natCast_dvd_natCast.mp hh)
    simp only [F, periodMask, hki, ite_false, compositionCutSignInt,
      compositionCutResidue_nat N k hkb.2, compositionCutSign,
      hk, hkr, ite_true, ite_false, sub_zero]
    decide
  refine ⟨F 1, ?_, ?_⟩
  · intro he
    have hh := odd_four_periodic_values F hP4 hodd (k : ℤ)
    rw [he] at hh
    exact hFk (by simpa only [neg_zero, ite_self] using hh)
  · intro x hx hn
    have hxi : ¬ (undeterminedGcd α k : ℤ) ∣ (x : ℤ) := by
      rw [hg]
      exact fun hh => hn (Int.natCast_dvd_natCast.mp hh)
    have hh := odd_four_periodic_values F hP4 hodd (x : ℤ)
    have hFx : F (x : ℤ) = compositionCutSign α x := by
      simp only [F, periodMask, hxi, ite_false, compositionCutSignInt,
        compositionCutResidue_nat N x hx]
    rw [hFx] at hh
    have h1 : (x : ℤ) % 4 = 1 ↔ x % 4 = 1 := by exact_mod_cast Iff.rfl (a := x % 4 = 1)
    have h3 : (x : ℤ) % 4 = 3 ↔ x % 4 = 3 := by exact_mod_cast Iff.rfl (a := x % 4 = 3)
    simpa only [h1, h3] using hh

/-- The actual quaternary initial period has no even discrepancy. -/
theorem undetermined_evenCutDisagreements_eq_empty_of_gcd_four {N : ℕ}
    (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hg : undeterminedGcd α k = 4) :
    evenCutDisagreements α (undeterminedGcd α k) (undeterminedCuts α k) = ∅ := by
  classical
  by_contra hD
  obtain ⟨m, hm, x, hx0, hxN, hxnot, hxe, hmxe, hdiff⟩ :=
    undetermined_even_discrepancy_window α k hne (Finset.nonempty_iff_ne_empty.mpr hD)
  obtain ⟨a, ha, hv⟩ := undetermined_signed_values_of_gcd_four α k hk hkr hfirst hne hg
  have hmx0 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
  have hmdiv : 4 ∣ m := by simpa only [hg] using undeterminedGcd_dvd α k m hm
  have hNdiv : 4 ∣ N := by simpa only [hg] using undeterminedGcd_dvd_weight α k hne
  have hxnd : ¬ 4 ∣ x := by simpa only [hg] using hxnot
  have hsx := compositionCutSign_eq_zero_of_not_one α x hxe
  have hvx := hv x (by omega) hxnd
  have hxmod : x % 4 = 2 := by
    have := Nat.mod_lt x (by decide : 0 < 4)
    have : x % 4 ≠ 0 := fun he => hxnd (Nat.dvd_of_mod_eq_zero he)
    split_ifs at hvx <;> omega
  have hnm := Nat.mod_eq_zero_of_dvd hmdiv
  have hnN := Nat.mod_eq_zero_of_dvd hNdiv
  have hwindow : m + x + 1 < N := by omega
  have hsign1 : compositionCutSign α 1 = a := by
    have hh := hv 1 (by omega) (by decide)
    simpa only [Nat.mod_eq_of_lt (by decide : 1 < 4), ite_true] using hh
  have ht1 : compositionCutType α 1 = 1 :=
    compositionCutType_one_of_nonzero_sign α 1 (by rwa [hsign1])
  have hx1nd : ¬ 4 ∣ x + 1 := by omega
  have hsignx1 : compositionCutSign α (x + 1) = -a := by
    have hh := hv (x + 1) (by omega) hx1nd
    have hx1mod : (x + 1) % 4 = 3 := by omega
    simpa only [hx1mod, show ¬ (3 : ℕ) = 1 by decide, ite_false, ite_true] using hh
  have htx1 : compositionCutType α (x + 1) = 1 :=
    compositionCutType_one_of_nonzero_sign α (x + 1) (by rw [hsignx1]; omega)
  have hh := undetermined_even_discrepancy_options α k hk hkr hfirst m hm x 1
    hx0 (by omega) hwindow hxnot (by rw [hg]; decide) hxe hmxe hdiff ht1
  rcases hh with hh | hh
  · have hs := (compositionCutCodeNat_eq_iff α (x + 1) 1).mp hh.1 |>.2
    rw [hsign1, hsignx1] at hs
    exact ha (by omega)
  · have ht := (compositionCutCodeNat_eq_iff α (x + 1) x).mp hh.1 |>.1
    exact hxe (ht.symm.trans htx1)

/-- The quaternary branch supplies literal proper factors without an odd-propagation hypothesis. -/
theorem undetermined_factorization_of_gcd_four {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hg : undeterminedGcd α k = 4) :
    ∃ m : ℕ, 2 ≤ m ∧ m * 4 = N ∧ ∃ δ : Composition m, ∃ ε : Composition 4,
      (compositionProduct δ ε).blocks = α.blocks := by
  have hh := undetermined_factorization_of_stable_frontier_at_gcd α k hk hkr hfirst hne
    (undetermined_evenCutDisagreements_eq_empty_of_gcd_four α k hk hkr hfirst hne hg)
  rw [hg] at hh
  exact hh

/-- A normalized initial gcd at most four supplies actual proper factors of that exact weight. -/
theorem undetermined_factorization_of_gcd_le_four {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (hne : (undeterminedCuts α k).Nonempty) (hg : undeterminedGcd α k ≤ 4) :
    ∃ m : ℕ, 2 ≤ m ∧ m * undeterminedGcd α k = N ∧
      ∃ δ : Composition m, ∃ ε : Composition (undeterminedGcd α k),
        (compositionProduct δ ε).blocks = α.blocks := by
  have hp := undeterminedGcd_ge_three α k hk hkr hfirst hne
  have hc : undeterminedGcd α k = 3 ∨ undeterminedGcd α k = 4 := by omega
  apply undetermined_factorization_of_stable_frontier_at_gcd α k hk hkr hfirst hne
  rcases hc with he | he
  · exact undetermined_evenCutDisagreements_eq_empty_of_gcd_three α k hk hkr hfirst hne he
  · exact undetermined_evenCutDisagreements_eq_empty_of_gcd_four α k hk hkr hfirst hne he

/-- Every actual same-inventory mate through weight fourteen is obtained by factor reversals.
Nonreconstructible sources use the proved ternary or quaternary factor constructor,
and both produced factors lie in the unconditional small-weight range.
-/
theorem ribbonFactorComplete_of_weight_le_fourteen {N : ℕ} (α : Composition N) (hN : N ≤ 14) :
    ribbonFactorComplete α := by
  classical
  by_cases hr : ribbonReconstructible α
  · exact ribbonFactorComplete_of_reconstructible α hr
  obtain ⟨γ, k, hγ, hInv, hnγ, _, _, _, hk, hkr, hfirst⟩ :=
    exists_normalized_first_single_cut α hr
  have hne := undeterminedCuts_nonempty γ hnγ k hk hkr
  have hp := undeterminedGcd_ge_three γ k hk hkr hfirst hne
  have hbound := three_mul_undeterminedGcd_le γ k hne
  have hg : undeterminedGcd γ k ≤ 4 := by omega
  obtain ⟨m, hm, hweight, δ, ε, hfactor⟩ :=
    undetermined_factorization_of_gcd_le_four γ k hk hkr hfirst hne hg
  have hδ := ribbonFactorComplete_of_small_weight δ (by nlinarith)
  have hε := ribbonFactorComplete_of_small_weight ε (by omega)
  have hγcomplete : ribbonFactorComplete γ :=
    (ribbonFactorComplete_congr (compositionProduct δ ε) γ hfactor).mp
      (ribbonFactorComplete_compose δ ε hm (by omega) hδ hε)
  intro β hβ
  have hh := hγcomplete β (hβ.trans hInv.symm)
  rcases hγ with he | he
  · rwa [he] at hh
  · rw [he] at hh
    exact (RibbonFactorReversal.reverse α).trans hh

end SkewClassInflation
