/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Setting
import SkewRibbonCoarsenings.SubsetDP

/-!
# A multilevel marked detector at weight seventy-two

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, the appendix `app:multilevel`.

All statements are exact finite computations at `n = 72`.  The labeled counts `K` over six
labels are evaluated by the kernel; the ordinary multiplicities by the subset recurrence of
`eq:subset-dp`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

/-- The cut set `S` of `app:multilevel`. -/
def multS : Finset ℕ :=
  ((Finset.Ioo 0 72).filter fun x => x % 4 = 1 ∨ x % 12 = 6 ∨ x % 24 = 8 ∨ x % 24 = 16) ∪ {24, 36}

/-- The cut set `T = (S ∖ {24}) ∪ {48}` of `app:multilevel`. -/
def multT : Finset ℕ := (multS.erase 24) ∪ {48}

/-- The function `f_y` with `e = 4` for the mask `𝓑₄` of `S`. -/
def multF (y x : ZMod 72) : ℤ := maskFun 72 multS 4 (x + y) - maskFun 72 multS 4 x

/-- The function `w` of `app:multilevel` (`d = 24`). -/
def multW (x : ZMod 72) : ℤ := wFun 72 multS multT 24 x

/-- `H_y(r, s, z)` of `eq:deltaH`. -/
def multH (y r s z : ZMod 72) : ℤ :=
  multF y r * (multW s + multW z) + multF y s * (multW r + multW z) +
    multF y z * (multW r + multW s)

/-- `app:multilevel`, cut data: both are cut sets of weight `72`, and `v` is supported exactly on
`{24, 48}` with `v(24) = 1`, `v(48) = -1`. -/
theorem multilevel_v :
    IsCutSet 72 multS ∧ IsCutSet 72 multT ∧
    vFun 72 multS multT 24 = 1 ∧ vFun 72 multS multT 48 = -1 ∧
    (∀ x : ZMod 72, vFun 72 multS multT x ≠ 0 ↔ x = 24 ∨ x = 48) := by
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩ <;>
    unfold IsCutSet <;> decide +kernel

/-- `app:multilevel`, least periods: the off-grid odd part `w` has least period `4`, and the masks
`𝓑₄, 𝓑₁₂, 𝓑₂₄` have least periods `12, 24, 72`; with `d = gcd(72, supp v) = 24`. -/
theorem multilevel_periods :
    supportGcd (vFun 72 multS multT) = 24 ∧ IsLeastPeriod multW 4 ∧
    IsLeastPeriod (maskFun 72 multS 4) 12 ∧ IsLeastPeriod (maskFun 72 multS 12) 24 ∧
    IsLeastPeriod (maskFun 72 multS 24) 72 := by
  have key : ∀ (f : ZMod 72 → ℤ) (e : ℕ), IsPeriod f e → 0 < e → e ∣ 72 →
      (∀ p, 0 < p → p < e → p ∣ 72 → ¬ IsPeriod f p) → IsLeastPeriod f e := by
    intro f e h1 h2 h3 h4
    exact ⟨h2, h3, h1, fun p hp hd hper => by
      by_contra hlt; exact h4 p hp (by omega) hd hper⟩
  refine ⟨by decide +kernel, ?_, ?_, ?_, ?_⟩ <;> apply key <;>
    first | (unfold IsPeriod; decide +kernel) | decide +kernel | skip
  · intro p hp hlt hd; interval_cases p <;> first | omega | (unfold IsPeriod; decide +kernel)
  · intro p hp hlt hd; interval_cases p <;> first | omega | (unfold IsPeriod; decide +kernel)
  · intro p hp hlt hd; interval_cases p <;> first | omega | (unfold IsPeriod; decide +kernel)
  · intro p hp hlt hd; interval_cases p <;> first | omega | (unfold IsPeriod; decide +kernel)

/-- `app:multilevel`, the witness: `a = 24`, `t = 12`, `y₀ = 20`, `(r, s, z) = (11, 11, 6)`,
`Σ = 48`, `W = 48`, `W - t = 36`, `C_box = 3·12 + 24 = 60 = W + p₁`; `Σ` does not fit. -/
theorem multilevel_witness :
    (11 + 11 + 6 + 20 = 48) ∧ (72 - 24 = 48) ∧ (48 - 12 = 36) ∧ (3 * 12 + 24 = 60) ∧
    (60 - 12 = 48) ∧ ¬ (48 ≤ 36) ∧
    cutInd 72 multS (24 + 12) - cutInd 72 multS 12 = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by decide +kernel⟩

/-- `app:multilevel`, the reflection: `t' = W - t = 36`, `y₀' = p₂ - y₀ = 4`,
`(r', s', z') = (p₁ - r, p₁ - s, p₁ - z) = (1, 1, 6)`, `Σ' = C_box - Σ = 12`, no padding is
needed, and `24 + 36 + 4 + 1 + 1 + 6 = 72`. -/
theorem multilevel_reflection :
    (48 - 12 = 36) ∧ (24 - 20 = 4) ∧ (12 - 11, 12 - 11, 12 - 6) = (1, 1, 6) ∧
    (60 - 48 = 12) ∧ (4 + 1 + 1 + 6 = 12) ∧ (24 + 36 + 4 + 1 + 1 + 6 = 72) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `app:multilevel`, the four factors of the detector on the positive list
`(24, 36, 4, 1, 1, 6)`: `v(24) = 1`, `b(60) - b(36) = -1`,
`𝓑₁₂(40) - 𝓑₁₂(4) = 1`, `H₄(1, 1, 6) = -2`. -/
theorem multilevel_factors :
    vFun 72 multS multT 24 = 1 ∧ cutInd 72 multS 60 - cutInd 72 multS 36 = -1 ∧
    maskFun 72 multS 12 40 - maskFun 72 multS 12 4 = 1 ∧ multH 4 1 1 6 = -2 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `app:multilevel`, labeled discrepancy: `K_b - K_c = -2` at `(36, 24, 6, 4, 1, 1)`
(the counts are `50` and `52`). -/
theorem multilevel_labeled_difference :
    (K multS ![36, 24, 6, 4, 1, 1] : ℤ) - K multT ![36, 24, 6, 4, 1, 1] = -2 := by
  decide +kernel

/-- `app:multilevel`, ordinary multiplicities at `(36, 24, 6, 4, 1, 1)`, by the subset
recurrence `eq:subset-dp`: `m_β = 25` and `m_γ = 26`. -/
theorem multilevel_mult_values :
    mult 72 multS {36, 24, 6, 4, 1, 1} = 25 ∧ mult 72 multT {36, 24, 6, 4, 1, 1} = 26 := by
  have hp : stateParts ![1, 4, 6, 24, 36] ![2, 1, 1, 1, 1] = {36, 24, 6, 4, 1, 1} := by
    decide +kernel
  have hs : stateSum ![1, 4, 6, 24, 36] ![2, 1, 1, 1, 1] = 72 := by decide +kernel
  have hi : Function.Injective ![1, 4, 6, 24, 36] := by decide +kernel
  have hpos : ∀ i, 0 < (![1, 4, 6, 24, 36] : Fin 5 → ℕ) i := by decide +kernel
  have hν : (![2, 1, 1, 1, 1] : Fin 5 → ℕ) ≠ 0 := by decide +kernel
  have hB := subset_dp_fuel (S := multS) hi hpos hν (by rw [hs]; unfold IsCutSet; decide +kernel)
  have hC := subset_dp_fuel (S := multT) hi hpos hν (by rw [hs]; unfold IsCutSet; decide +kernel)
  rw [hp, hs] at hB hC
  rw [hB, hC]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- `app:multilevel`, ordinary discrepancy: the only repeated numerical part is the pair of
ones, so the labeled counts are `2 m` and the ordinary discrepancy is `-1`. -/
theorem multilevel_ordinary_difference :
    (mult 72 multS {36, 24, 6, 4, 1, 1} : ℤ) - mult 72 multT {36, 24, 6, 4, 1, 1} = -1 ∧
    K multS ![36, 24, 6, 4, 1, 1] = 2 * mult 72 multS {36, 24, 6, 4, 1, 1} ∧
    K multT ![36, 24, 6, 4, 1, 1] = 2 * mult 72 multT {36, 24, 6, 4, 1, 1} := by
  rw [multilevel_mult_values.1, multilevel_mult_values.2]
  refine ⟨by norm_num, by decide +kernel, by decide +kernel⟩

end SkewRibbonCoarsenings
