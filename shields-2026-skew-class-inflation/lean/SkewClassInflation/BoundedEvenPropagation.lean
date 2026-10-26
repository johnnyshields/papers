/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundedEvenDiscrepancy

/-!
# Actual bounded even-discrepancy propagation

The bounded first-frontier propagation step for factor-reversal
reconstruction in `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  The second four-part alternative
is excluded by the actual complementary single point and a second
inventory comparison.  The two required positive partition windows
are explicit hypotheses, not supplied by an unproved lifting claim.
Sorry-free.
-/

namespace SkewClassInflation

/-- In the two true positive windows, an even discrepancy preserves every specified single code. -/
theorem bounded_even_discrepancy_agrees {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (hfirst : ∀ j < k, compositionCutType α j ≠ 1)
    (m : ℕ) (hm : m ∈ undeterminedCuts α k) (x z : ℕ)
    (hx0 : 0 < x) (hz0 : 0 < z) (hzm : z < m) (hwindow : 2 * m + x < N)
    (hx : ¬ undeterminedGcd α k ∣ x) (hz : ¬ undeterminedGcd α k ∣ z)
    (hxe : compositionCutType α x ≠ 1) (hmxe : compositionCutType α (m + x) ≠ 1)
    (hdisagree : compositionCutType α x ≠ compositionCutType α (m + x))
    (hzs : compositionCutType α z = 1) :
    compositionCutCodeNat α (x + z) = compositionCutCodeNat α z ∧
      compositionCutCodeNat α (m + x + z) = compositionCutCodeNat α z := by
  classical
  have hmb := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
  have htotal : m + x + z < N := by omega
  have hoptions := undetermined_even_discrepancy_options α k hk hkr hfirst m hm x z
    hx0 hz0 htotal hx hz hxe hmxe hdisagree hzs
  rcases hoptions with hgood | hbad
  · exact hgood
  · exfalso
    let w := m - z
    have hw0 : 0 < w := by dsimp only [w]; omega
    have hwN : w < N := by dsimp only [w]; omega
    have hsumw : w + z = m := by dsimp only [w]; omega
    have hmdiv := undeterminedGcd_dvd α k m hm
    have hwdiv : ¬ undeterminedGcd α k ∣ w := by
      intro hd
      have hsumdiv : undeterminedGcd α k ∣ w + z := by rwa [hsumw]
      exact hz ((Nat.dvd_add_iff_right hd).mpr hsumdiv)
    have hdetz := cutDetermined_of_undeterminedGcd_not_dvd α k z hz0 (by omega) hz
    have hdetw := cutDetermined_of_undeterminedGcd_not_dvd α k w hw0 hwN hwdiv
    have hanti := undetermined_cutSign_antisymm α k m hm z hz0 hzm hdetz hdetw
    have hsignz := compositionCutSign_ne_zero_of_one α z hzs
    have hsignw : compositionCutSign α w ≠ 0 := by
      change compositionCutSign α (m - z) ≠ 0
      rw [hanti]
      omega
    have hwtype := compositionCutType_one_of_nonzero_sign α w hsignw
    have hleftType := (compositionCutCodeNat_eq_iff α (x + z) x).mp hbad.1 |>.1
    have hrightType := (compositionCutCodeNat_eq_iff α (m + x + z) (m + x)).mp hbad.2 |>.1
    have hx'even : compositionCutType α (x + z) ≠ 1 := by rwa [hleftType]
    have hmx'even : compositionCutType α (m + (x + z)) ≠ 1 := by
      have hh : compositionCutType α (m + x + z) ≠ 1 := by rwa [hrightType]
      simpa only [Nat.add_assoc] using hh
    have hdisagree' : compositionCutType α (x + z) ≠ compositionCutType α (m + (x + z)) := by
      intro he
      have hr : compositionCutType α (m + (x + z)) = compositionCutType α (m + x) := by
        simpa only [Nat.add_assoc] using hrightType
      exact hdisagree (hleftType.symm.trans (he.trans hr))
    obtain ⟨hp, _, hpN, _, hperiod⟩ :=
      undeterminedGcd_signed_period α k hk hkr hfirst ⟨m, hm⟩
    have hx' := not_dvd_even_single_sum α (by omega) hpN hperiod x z (by omega)
      hz0 (by omega) hx hxe hzs
    have hsecond := undetermined_even_discrepancy_options α k hk hkr hfirst m hm (x + z) w
      (by omega) hw0 (by dsimp only [w]; omega) hx' hwdiv hx'even hmx'even hdisagree' hwtype
    have hcoord : x + z + w = m + x := by dsimp only [w]; omega
    rcases hsecond with hsecond | hsecond
    · have ht := (compositionCutCodeNat_eq_iff α (x + z + w) w).mp hsecond.1 |>.1
      rw [hcoord, hwtype] at ht
      exact hmxe ht
    · have hc := hsecond.1.trans hbad.1
      rw [hcoord] at hc
      have ht := (compositionCutCodeNat_eq_iff α (m + x) x).mp hc |>.1
      exact hdisagree ht.symm

end SkewClassInflation
