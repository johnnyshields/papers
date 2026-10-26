/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MarkedCharts
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.NoRightRibbons
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MurnaghanNakayama.Derivation

/-!
# Mixed-chart annihilation

«Equal functions at a common period» (`sec:transport`, `lem:mixed-vanishing`)
of `shields-2026-skew-marked-factor.tex`.
The operators act on the actual parent skew Schur function, not on a normalized
composition multiplied by extra factors.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan

/-- An admitted mixed mark is necessarily a copied positive-width legal mark. -/
theorem mixed_readout_legal {η : MarkedInner} (hη : η.IsReadoutLegal)
    (hm : η.case.IsMixed) : η.IsLegal := by
  rcases hη with h | ⟨_, he⟩
  · exact h
  · have hc : η.case = .b := by simpa only [emptyMarkV] using congrArg MarkedInner.case he
    exfalso
    simp [AttachCase.IsMixed, hc] at hm

/-- Every positive period multiple annihilates the genuine mixed parent function.

**Differs from the paper's route.**  Uses the proved absence of removable
period-multiple ribbons and Murnaghan–Nakayama, rather than re-reading the
same boundary obstruction as a closed beta set. -/
theorem mixed_period_derivative_zero {η : MarkedInner} (hη : η.IsReadoutLegal)
    (hm : η.case.IsMixed) {D : Diagram} (hD : IsConnectedSkew D)
    {k : ℕ} (hk : 0 < k) :
    pDeriv (k * η.period.toNat) (cellSchur (η.compose D)) = 0 := by
  have hl := mixed_readout_legal hη hm
  have hp : 0 < η.period.toNat := by have := hl.period_pos; omega
  have hkp : 0 < k * η.period.toNat := Nat.mul_pos hk hp
  have hF : IsSkew (η.compose D) := (hl.isConnectedSkew_compose hD).1
  rcases hm with hc | hd
  · rw [MN.pDeriv_cellSchur_left_of_isSkew hF hkp]
    unfold ribbonSumLeft
    rw [Corner.corner_no_leftRibbons hl hc hD hk]
    simp
  · rw [MN.pDeriv_cellSchur_right_of_isSkew hF hkp]
    unfold ribbonSumRight
    rw [Corner.corner_no_rightRibbons_d hl hd hD hk]
    simp

/-- Cell translations in a supplied chart do not change the annihilation statement. -/
theorem mixed_chart_derivative_zero {χ : Chart} (hχ : χ.IsProperReadoutLegal)
    (hm : χ.ω.case.IsMixed) {F : Diagram} (hF : χ.IsChartOf F)
    {k : ℕ} (hk : 0 < k) : pDeriv (k * χ.period.toNat) (cellSchur F) = 0 := by
  obtain ⟨t, ht⟩ := hF
  rw [ht, cellSchur_translate]
  exact mixed_period_derivative_zero hχ.2.2.2 hm hχ.1 hk

end SkewMarkedFactor
