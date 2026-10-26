/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Setting
import SkewRibbonCoarsenings.SubsetDP

/-!
# The reflected probes at weight thirty

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:realization`
(`ex:reflection`; the quantities `H_y`, `Δ` of `eq:deltaH`, the packing ledger of
`lem:packing`, and the labeled-to-ordinary passage of `lem:labels`).

All statements are exact finite computations at `n = 30`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

/-- Cut set of `b` in `ex:reflection`: the periodic mask `(0,1,1,0,0,0,1,0,1,0)` off the
`5`-grid, together with `b(5) = b(25) = b(10) = 1`, `b(15) = b(20) = 0`. -/
def reflB : Finset ℕ := {1, 2, 5, 6, 8, 10, 11, 12, 16, 18, 21, 22, 25, 26, 28}

/-- Cut set of `c` in `ex:reflection`: `b` with the values at `10, 20` exchanged. -/
def reflC : Finset ℕ := {1, 2, 5, 6, 8, 11, 12, 16, 18, 20, 21, 22, 25, 26, 28}

/-- The function `f_y(x) = 𝓑_e(x + y) - 𝓑_e(x)` of `eq:deltaH` for the mask `𝓑_5` of `b`. -/
def reflF (y x : ZMod 30) : ℤ := maskFun 30 reflB 5 (x + y) - maskFun 30 reflB 5 x

/-- The function `w` of `ex:reflection` (`d = 10`). -/
def reflW (x : ZMod 30) : ℤ := wFun 30 reflB reflC 10 x

/-- `H_y(r, s, z)` of `eq:deltaH` in `ex:reflection`. -/
def reflH (y r s z : ZMod 30) : ℤ :=
  reflF y r * (reflW s + reflW z) + reflF y s * (reflW r + reflW z) +
    reflF y z * (reflW r + reflW s)

/-- `ex:reflection`, data: `c` agrees with `b` except at `10, 20`, where the values are
exchanged; `b(5) = b(25) = 1`, `b(15) = 0`, `b(10) = 1`, `b(20) = 0`; both are cut sets of
weight `30`. -/
theorem reflection_cut_data :
    IsCutSet 30 reflB ∧ IsCutSet 30 reflC ∧
    (reflB.erase 10) = (reflC.erase 20) ∧ 10 ∈ reflB ∧ 20 ∉ reflB ∧ 10 ∉ reflC ∧ 20 ∈ reflC ∧
    cutInd 30 reflB 5 = 1 ∧ cutInd 30 reflB 25 = 1 ∧ cutInd 30 reflB 15 = 0 ∧
    cutInd 30 reflB 10 = 1 ∧ cutInd 30 reflB 20 = 0 := by
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩ <;> unfold IsCutSet <;> decide +kernel

/-- `ex:reflection`, the periodic mask: `(𝓑₅(0), …, 𝓑₅(9)) = (0,1,1,0,0,0,1,0,1,0)`, and `𝓑₅`
is `10`-periodic on `ℤ/30`. -/
theorem reflection_mask :
    (List.range 10).map (fun x : ℕ => maskFun 30 reflB 5 (x : ZMod 30)) =
      [0, 1, 1, 0, 0, 0, 1, 0, 1, 0] ∧
    IsPeriod (maskFun 30 reflB 5) 10 := by
  refine ⟨by decide +kernel, ?_⟩
  unfold IsPeriod
  decide +kernel

/-- `ex:reflection`, the setting: `d = gcd(30, supp v) = 10`, `v` is supported on `{10, 20}`,
and `e = 5` is the least period of `w`; the odd part `w` has `d = 10` as a period. -/
theorem reflection_setting :
    supportGcd (vFun 30 reflB reflC) = 10 ∧
    (∀ x : ZMod 30, vFun 30 reflB reflC x ≠ 0 ↔ x = 10 ∨ x = 20) ∧
    IsOdd reflW ∧ IsPeriod reflW 10 ∧ IsLeastPeriod reflW 5 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · unfold IsOdd; decide +kernel
  · unfold IsPeriod; decide +kernel
  refine ⟨by norm_num, by norm_num, by unfold IsPeriod; decide +kernel, ?_⟩
  intro p hp hd hper
  have hp30 : p ≤ 30 := Nat.le_of_dvd (by norm_num) hd
  by_contra hlt
  interval_cases p <;> first | omega | (revert hd hper; unfold IsPeriod; decide +kernel)

/-- `ex:reflection`, bottom probes: with `a = 10`, `W = 20`, `t = 15` the probes `(9,8,8)` give
`H_t = 2` and `Δ = 1`, and their sum is `25`, whereas `W - t = 5`. -/
theorem reflection_bottom_probes :
    reflH 15 9 8 8 = 2 ∧ cutInd 30 reflB 25 - cutInd 30 reflB 15 = 1 ∧
    9 + 8 + 8 = 25 ∧ 20 - 15 = 5 ∧ 25 ≠ 20 - 15 ∧ 20 - 15 < 9 + 8 + 8 := by
  refine ⟨by decide +kernel, by decide +kernel, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `ex:reflection`, reflection: target `t' = W - t = 5`, probes `(1,2,2) = (p₁ - 9, p₁ - 8, p₁ - 8)`
with `p₁ = 10`, `H_5 = -2`, `Δ' = -1`; the reflected sum `5` fits in `t' = 5`. -/
theorem reflection_reflected_probes :
    20 - 15 = 5 ∧ (10 - 9, 10 - 8, 10 - 8) = (1, 2, 2) ∧
    reflH 5 1 2 2 = -2 ∧ cutInd 30 reflB 15 - cutInd 30 reflB 5 = -1 ∧
    cutInd 30 reflB (10 + 5) - cutInd 30 reflB 5 = -1 ∧ 1 + 2 + 2 ≤ 5 := by
  refine ⟨by norm_num, by norm_num, by decide +kernel, by decide +kernel, by decide +kernel, by norm_num⟩

/-- `ex:reflection`, padding: the first probe padded by `10` gives the positive weight-`30`
list `(10, 5, 11, 2, 2)`. -/
theorem reflection_padded_list :
    (10, 5, 11, 2, 2) = (10, 5, 1 + 10, 2, 2) ∧ 10 + 5 + 11 + 2 + 2 = 30 := by
  refine ⟨by norm_num, by norm_num⟩

/-- `ex:reflection`, labeled difference: `K_b - K_c = -2` at the list `(10, 5, 11, 2, 2)`
(`ΔK` of `lem:labels`). -/
theorem reflection_labeled_difference :
    (K reflB ![10, 5, 11, 2, 2] : ℤ) - K reflC ![10, 5, 11, 2, 2] = -2 := by
  decide +kernel

/-- Ordinary multiplicities at `(11, 10, 5, 2, 2)`, computed by the subset recurrence
`eq:subset-dp` (`subset_dp_fuel`): `m_β = 6` and `m_γ = 7`. -/
theorem reflection_mult_values :
    mult 30 reflB {11, 10, 5, 2, 2} = 6 ∧ mult 30 reflC {11, 10, 5, 2, 2} = 7 := by
  have hp : stateParts ![2, 5, 10, 11] ![2, 1, 1, 1] = {11, 10, 5, 2, 2} := by decide +kernel
  have hs : stateSum ![2, 5, 10, 11] ![2, 1, 1, 1] = 30 := by decide +kernel
  have hi : Function.Injective ![2, 5, 10, 11] := by decide +kernel
  have hpos : ∀ i, 0 < (![2, 5, 10, 11] : Fin 4 → ℕ) i := by decide +kernel
  have hν : (![2, 1, 1, 1] : Fin 4 → ℕ) ≠ 0 := by decide +kernel
  have hB := subset_dp_fuel (S := reflB) hi hpos hν (by rw [hs]; unfold IsCutSet; decide +kernel)
  have hC := subset_dp_fuel (S := reflC) hi hpos hν (by rw [hs]; unfold IsCutSet; decide +kernel)
  rw [hp, hs] at hB hC
  rw [hB, hC]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- `ex:reflection`, ordinary difference: exact division by `2!` (the labeled counts are
`κ(λ) m_β(λ)` with `κ = 2`) gives `m_β - m_γ = -1` at `(11, 10, 5, 2, 2)`. -/
theorem reflection_ordinary_difference :
    (mult 30 reflB {11, 10, 5, 2, 2} : ℤ) - mult 30 reflC {11, 10, 5, 2, 2} = -1 := by
  rw [reflection_mult_values.1, reflection_mult_values.2]; norm_num

/-- `ex:reflection`, `lem:labels` at this list: the labeled counts are twice the ordinary
multiplicities, because the only repeated numerical part is the pair of twos. -/
theorem reflection_labels :
    K reflB ![10, 5, 11, 2, 2] = 2 * mult 30 reflB {11, 10, 5, 2, 2} ∧
    K reflC ![10, 5, 11, 2, 2] = 2 * mult 30 reflC {11, 10, 5, 2, 2} := by
  rw [reflection_mult_values.1, reflection_mult_values.2]
  exact ⟨by decide +kernel, by decide +kernel⟩

end SkewRibbonCoarsenings
