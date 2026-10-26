/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OrdinaryFold/Scalar.lean`. -/
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common
import GluingCore.Tactics


/-!
# Scalar arithmetic of the slots of the fold

Formalizes `shields-2026-skew-factor-gluing.tex`, «Two ordinary roots»
(`prop:gluing-ordinary-fold`),
the choice of the slots `τ`, `σ` and of the attachment case of the folded mark.

The statements are linear-arithmetic facts about the generic bits at the residues `τ = ha mod g`,
`σ = hb mod g`, `0`, `w_g`, with `ha`, `hb` the exceptional phases of the first root, `bg = b g`,
`w = bg + w_g`: the bit equalities of the budgets `E1`, `E2`, the caps `G1`–`G4`, and instances of
the positivity of the heights.  Each is proved by `omega` after splitting the conditionals.

Sorry-free.
-/

namespace GluingCore
namespace OrdinaryFold


theorem scalar_range_a (g wg bg ha τ : ℕ) (a0τ : ℤ)
    (_hwg : wg < g) (hbg : bg = 0 ∨ g ≤ bg) (hha : ha < bg + wg)
    (hτ : (ha < g ∧ τ = ha) ∨ (g ≤ ha ∧ τ = ha - bg ∧ bg ≤ ha ∧ ha < bg + g))
    (G1 : 1 ≤ ha → wg < ha → a0τ = 1) (G2 : ha + wg < bg + wg → a0τ = 0) : τ ≤ wg := by
  rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · by_contra hcon
    have := G1 (by omega) (by omega)
    have := G2 (by omega)
    omega
  · omega

theorem scalar_range_b (g wg bg hb σ : ℕ) (b0σ : ℤ) (_hwg : wg < g) (hbg : bg = 0 ∨ g ≤ bg)
    (hhb : hb ≤ bg + wg)
    (hσ : (hb < g ∧ σ = hb) ∨ (g ≤ hb ∧ σ = hb - bg ∧ bg ≤ hb ∧ hb < bg + g))
    (G3 : wg < hb → b0σ = 0) (G4 : hb < bg + wg → hb + wg < bg + wg → b0σ = 1) : σ ≤ wg := by
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · by_contra hcon
    have := G3 (by omega)
    have := G4 (by omega) (by omega)
    omega
  · omega

theorem scalar_rho (wg bg ha hb τ σ : ℕ) (a0τ b0σ a00 b00 a0w b0w : ℤ)
    (hbit : (a0τ = 0 ∨ a0τ = 1) ∧ (b0σ = 0 ∨ b0σ = 1) ∧ (a00 = 0 ∨ a00 = 1) ∧
      (b00 = 0 ∨ b00 = 1) ∧ (a0w = 0 ∨ a0w = 1) ∧ (b0w = 0 ∨ b0w = 1))
    (hτ0 : τ = 0 → a0τ = a00) (hσw : σ = wg → b0σ = b0w)
    (heps : a00 - b00 = 0 ∨ a00 - b00 = 1) (hepst : b0w - a0w = 0 ∨ b0w - a0w = 1)
    (E1 : (if 1 ≤ ha then 1 - a0τ else 0) + b0σ = a00 - b00)
    (E2 : (if hb < bg + wg then 1 - b0σ else 0) + a0τ = b0w - a0w)
    (hhb : hb ≤ bg + wg) (hha0 : ha = 0 → τ = 0) (hhbw : hb = bg + wg → σ = wg) :
    a0τ = b0σ := by
  by_cases h1 : 1 ≤ ha <;> by_cases h2 : hb < bg + wg <;>
    simp only [h1, h2, ite_true, ite_false] at E1 E2 <;> omega


theorem scalar_pos_a (g wg bg ha hb τ σ r : ℕ) (a0τ b0σ _a00 _b00 _a0w _b0w sr : ℤ)
    (hwg : wg < g) (_hbg : bg = 0 ∨ g ≤ bg) (_hha : ha < bg + wg) (_hhb1 : 1 ≤ hb)
    (_hhb : hb ≤ bg + wg)
    (hτ : (ha < g ∧ τ = ha) ∨ (g ≤ ha ∧ τ = ha - bg ∧ bg ≤ ha ∧ ha < bg + g))
    (hσ : (hb < g ∧ σ = hb) ∨ (g ≤ hb ∧ σ = hb - bg ∧ bg ≤ hb ∧ hb < bg + g))
    (hbit : (a0τ = 0 ∨ a0τ = 1) ∧ (b0σ = 0 ∨ b0σ = 1))
    (G1 : 1 ≤ ha → wg < ha → a0τ = 1) (G3 : wg < hb → b0σ = 0)
    (hρ : a0τ = b0σ) (hnew : a0τ = 1 ∨ τ < σ) (_hr : r < wg)
    (hH1 : 1 ≤ 1 + sr + (if ha ≤ r then (if 1 ≤ ha then 1 - a0τ else 0) else 0) +
      (if hb ≤ r then b0σ else 0))
    (hM1 : 1 + (if hb ≤ r then 1 else 0) ≤ 1 + sr + (if ha ≤ r then (if 1 ≤ ha then 1 - a0τ else 0)
        else 0) +
      (if hb ≤ r then b0σ else 0))
    (hM2 : 1 + (if hb ≤ bg + r then 1 else 0) ≤ 1 + sr +
      (if ha ≤ bg + r then (if 1 ≤ ha then 1 - a0τ else 0) else 0) +
      (if hb ≤ bg + r then b0σ else 0)) :
    1 + (if σ ≤ r then 1 else 0) ≤ 1 + sr + (if ha ≤ r then (if 1 ≤ ha then 1 - a0τ else 0) else 0)
        +
      (if hb ≤ r then b0σ else 0) := by
  split_ifs at hH1 hM1 hM2 ⊢ <;> omega


theorem scalar_b1 (g wg bg ha hb τ σ : ℕ) (a0τ b0σ a00 b00 : ℤ)
    (_hwg1 : 1 ≤ wg) (_hhb1 : 1 ≤ hb)
    (hτ : (ha < g ∧ τ = ha) ∨ (g ≤ ha ∧ τ = ha - bg ∧ bg ≤ ha ∧ ha < bg + g))
    (hσ : (hb < g ∧ σ = hb) ∨ (g ≤ hb ∧ σ = hb - bg ∧ bg ≤ hb ∧ hb < bg + g))
    (hbit : (a0τ = 0 ∨ a0τ = 1) ∧ (b0σ = 0 ∨ b0σ = 1))
    (hτ0 : τ = 0 → a0τ = a00) (hσ0 : σ = 0 → b0σ = b00)
    (E1 : (if 1 ≤ ha then 1 - a0τ else 0) + b0σ = a00 - b00)
    (hρ : a0τ = b0σ) (hnew : ¬ (a0τ = 1 ∨ τ < σ))
    (hMbg : 1 + (if hb ≤ bg then 1 else 0) ≤ 1 +
      (if ha ≤ bg then (if 1 ≤ ha then 1 - a0τ else 0) else 0) + (if hb ≤ bg then b0σ else 0)) :
    1 ≤ τ := by
  by_contra h0
  have hτ0' : τ = 0 := by omega
  have hσ0' : σ = 0 := by omega
  have e1 := hτ0 hτ0'
  have e2 := hσ0 hσ0'
  by_cases h1 : 1 ≤ ha
  · simp only [h1, ite_true] at E1
    omega
  · simp only [h1, ite_false] at E1
    have : ha = 0 := by omega
    subst this
    by_cases h2 : hb ≤ bg
    · simp only [h2, ite_true, show 0 ≤ bg by omega, h1, ite_false] at hMbg
      omega
    · omega

theorem scalar_b2 (g wg bg ha hb τ σ : ℕ) (a0τ b0σ a00 b00 a0w b0w : ℤ)
    (hwg1 : 1 ≤ wg) (hwg : wg < g) (_hha : ha < bg + wg) (hhb1 : 1 ≤ hb)
    (hhb : hb ≤ bg + wg)
    (hτ : (ha < g ∧ τ = ha) ∨ (g ≤ ha ∧ τ = ha - bg ∧ bg ≤ ha ∧ ha < bg + g))
    (hσ : (hb < g ∧ σ = hb) ∨ (g ≤ hb ∧ σ = hb - bg ∧ bg ≤ hb ∧ hb < bg + g))
    (hbit : (a0τ = 0 ∨ a0τ = 1) ∧ (b0σ = 0 ∨ b0σ = 1) ∧ (a00 = 0 ∨ a00 = 1) ∧
      (b00 = 0 ∨ b00 = 1) ∧ (a0w = 0 ∨ a0w = 1) ∧ (b0w = 0 ∨ b0w = 1))
    (hτw : τ = wg → a0τ = a0w) (hσw : σ = wg → b0σ = b0w)
    (E1 : (if 1 ≤ ha then 1 - a0τ else 0) + b0σ = a00 - b00)
    (E2 : (if hb < bg + wg then 1 - b0σ else 0) + a0τ = b0w - a0w)
    (hρ : a0τ = b0σ) (hnew : ¬ (a0τ = 1 ∨ τ < σ)) (hτr : τ ≤ wg) (hσr : σ ≤ wg)
    (hPw1 : 1 ≤ 1 + (-(a00 - b00) - (a0w - b0w)) +
      (if ha ≤ wg - 1 then (if 1 ≤ ha then 1 - a0τ else 0) else 0) +
      (if hb ≤ wg - 1 then b0σ else 0)) :
    σ + 1 ≤ wg := by
  by_contra hcon
  have hσe : σ = wg := by omega
  have hτe : τ = wg := by omega
  have e1 := hτw hτe
  have e2 := hσw hσe
  have h1 : 1 ≤ ha := by omega
  simp only [h1, ite_true] at E1
  by_cases h2 : hb < bg + wg
  · simp only [h2, ite_true] at E2
    omega
  · simp only [h2, ite_false] at E2
    have hbe : hb = bg + wg := by omega
    have hh : ¬ hb ≤ wg - 1 := by omega
    simp only [hh, ite_false, h1, ite_true] at hPw1
    by_cases h3 : ha ≤ wg - 1
    · omega
    · simp only [h3, ite_false] at hPw1
      omega

theorem scalar_b345 (g wg bg ha hb τ σ : ℕ) (a0τ b0σ a00 b00 a0w b0w : ℤ)
    (_hha : ha < bg + wg) (hhb1 : 1 ≤ hb) (hhb : hb ≤ bg + wg)
    (hτ : (ha < g ∧ τ = ha) ∨ (g ≤ ha ∧ τ = ha - bg ∧ bg ≤ ha ∧ ha < bg + g))
    (hσ : (hb < g ∧ σ = hb) ∨ (g ≤ hb ∧ σ = hb - bg ∧ bg ≤ hb ∧ hb < bg + g))
    (hbit : (a0τ = 0 ∨ a0τ = 1) ∧ (b0σ = 0 ∨ b0σ = 1) ∧ (a00 = 0 ∨ a00 = 1) ∧
      (b00 = 0 ∨ b00 = 1) ∧ (a0w = 0 ∨ a0w = 1) ∧ (b0w = 0 ∨ b0w = 1))
    (hσw : σ = wg → b0σ = b0w)
    (E1 : (if 1 ≤ ha then 1 - a0τ else 0) + b0σ = a00 - b00)
    (E2 : (if hb < bg + wg then 1 - b0σ else 0) + a0τ = b0w - a0w)
    (hρ : a0τ = b0σ) (hnew : ¬ (a0τ = 1 ∨ τ < σ)) (h1 : 1 ≤ τ) (h2 : σ + 1 ≤ wg) :
    b0w = 1 ∧ a00 = 1 ∧ (1 ≤ σ → b00 = 0) := by
  have hha1 : 1 ≤ ha := by omega
  simp only [hha1, ite_true] at E1
  have hhb' : hb < bg + wg := by omega
  simp only [hhb', ite_true] at E2
  omega

theorem scalar_pos_b (g wg bg ha hb τ σ r : ℕ) (a0τ b0σ sr : ℤ)
    (hwg : wg < g) (_hbg : bg = 0 ∨ g ≤ bg) (_hha : ha < bg + wg) (_hhb1 : 1 ≤ hb)
    (_hhb : hb ≤ bg + wg)
    (hτ : (ha < g ∧ τ = ha) ∨ (g ≤ ha ∧ τ = ha - bg ∧ bg ≤ ha ∧ ha < bg + g))
    (hσ : (hb < g ∧ σ = hb) ∨ (g ≤ hb ∧ σ = hb - bg ∧ bg ≤ hb ∧ hb < bg + g))
    (hbit : (a0τ = 0 ∨ a0τ = 1) ∧ (b0σ = 0 ∨ b0σ = 1))
    (G1 : 1 ≤ ha → wg < ha → a0τ = 1) (G3 : wg < hb → b0σ = 0)
    (hρ : a0τ = b0σ) (hnew : ¬ (a0τ = 1 ∨ τ < σ)) (_h1 : 1 ≤ τ) (_hr : r < wg)
    (hH1 : 1 ≤ 1 + sr + (if ha ≤ r then (if 1 ≤ ha then 1 - a0τ else 0) else 0) +
      (if hb ≤ r then b0σ else 0))
    (hM1 : 1 + (if hb ≤ r then 1 else 0) ≤ 1 + sr + (if ha ≤ r then (if 1 ≤ ha then 1 - a0τ else 0)
        else 0) +
      (if hb ≤ r then b0σ else 0))
    (hM2 : 1 + (if hb ≤ bg + r then 1 else 0) ≤ 1 + sr +
      (if ha ≤ bg + r then (if 1 ≤ ha then 1 - a0τ else 0) else 0) +
      (if hb ≤ bg + r then b0σ else 0)) :
    1 + (if τ ≤ r then 1 else 0) ≤ 1 + sr + (if ha ≤ r then (if 1 ≤ ha then 1 - a0τ else 0) else 0)
        +
      (if hb ≤ r then b0σ else 0) := by
  split_ifs at hH1 hM1 hM2 ⊢ <;> omega


theorem scalar_a (g wg bg ha hb τ σ : ℕ) (a0τ b0σ a00 b00 a0w b0w : ℤ)
    (hwg : wg < g) (_hha : ha < bg + wg) (_hhb1 : 1 ≤ hb) (hhb : hb ≤ bg + wg)
    (hτ : (ha < g ∧ τ = ha) ∨ (g ≤ ha ∧ τ = ha - bg ∧ bg ≤ ha ∧ ha < bg + g))
    (hσ : (hb < g ∧ σ = hb) ∨ (g ≤ hb ∧ σ = hb - bg ∧ bg ≤ hb ∧ hb < bg + g))
    (hbit : (a0τ = 0 ∨ a0τ = 1) ∧ (b0σ = 0 ∨ b0σ = 1) ∧ (a00 = 0 ∨ a00 = 1) ∧
      (b00 = 0 ∨ b00 = 1) ∧ (a0w = 0 ∨ a0w = 1) ∧ (b0w = 0 ∨ b0w = 1))
    (hτ0 : τ = 0 → a0τ = a00) (hτw : τ = wg → a0τ = a0w)
    (hσ0 : σ = 0 → b0σ = b00) (hσw : σ = wg → b0σ = b0w)
    (E1 : (if 1 ≤ ha then 1 - a0τ else 0) + b0σ = a00 - b00)
    (E2 : (if hb < bg + wg then 1 - b0σ else 0) + a0τ = b0w - a0w)
    (hτr : τ ≤ wg) (hσr : σ ≤ wg)
    (hρ : a0τ = b0σ) (hnew : a0τ = 1 ∨ τ < σ) :
    τ < wg ∧ 1 ≤ σ ∧ a0w = 0 ∧ b00 = 0 ∧ (1 ≤ τ → a00 = 1) := by
  by_cases h1 : 1 ≤ ha <;> by_cases h2 : hb < bg + wg <;>
    simp only [h1, h2, ite_true, ite_false] at E1 E2 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

end OrdinaryFold
end GluingCore
