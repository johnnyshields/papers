import SkewGluing.OrdinaryFold

/-!
# The cap budgets of the slots of the fold

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots»
(`prop:gluing-ordinary-fold`),
the display of the cap budgets in case (a): with `τ`, `σ` the slots, `ρ = A⁰_τ = B⁰_σ`,
`i = 1_{τ>0}` and `j = 1_{σ<w_g}`,
`C_0 = i (1 - ρ) + ρ`, `-C_{w_g} = ρ + j (1 - ρ)` and
`∑_{r=1}^{w_g-1} C_r + (i - j) (1 - ρ) = 0`
(`GcdPair.cap_budgets`).

Sorry-free.
-/

namespace SkewGluing
namespace OrdinaryDrift

variable {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}

/-- **The cap budgets.**  For the first root of two ordinary roots (`GcdPair`) with slots
`τ = ha₁ mod g`, `σ = hb₁ mod g`, `ρ = A⁰_τ`, `i = 1_{τ>0}`, `j = 1_{σ<w_g}` and
`C_k = A⁰_k - B⁰_k`:
`C_0 = i (1 - ρ) + ρ`, `-C_{w_g} = ρ + j (1 - ρ)` and
`C_1 + ⋯ + C_{w_g-1} + (i - j) (1 - ρ) = 0`. -/
theorem GcdPair.cap_budgets (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂)
    (hwg1 : 1 ≤ wg) (hha : ha₁ < b * g + wg) (hhb1 : 1 ≤ hb₁) :
    A0 0 - B0 0 = (if 0 < ha₁ % g then 1 else 0) * (1 - A0 (ha₁ % g)) + A0 (ha₁ % g) ∧
    -(A0 wg - B0 wg) = A0 (ha₁ % g) +
      (if hb₁ % g < wg then 1 else 0) * (1 - A0 (ha₁ % g)) ∧
    ∑ r ∈ Finset.range (wg - 1), (A0 (r + 1) - B0 (r + 1)) +
      ((if 0 < ha₁ % g then 1 else 0) - (if hb₁ % g < wg then 1 else 0)) *
        (1 - A0 (ha₁ % g)) = 0 := by
  have sc := h.slotScalars hha hhb1
  have hg := h.g_pos
  have hwg := h.wg_lt
  have hhb := h.root₁.hb_le
  obtain ⟨d1, d2, d3, d4, -⟩ := h.drift_full
  obtain ⟨G1, G2, G3, G4⟩ := h.cap_facts
  have hτs := h.tau_struct hha
  have hσs := h.sigma_struct hhb
  have E1 := h.budget_initial
  simp only [hhb1, ite_true] at E1
  have E2 := h.budget_terminal
  simp only [hha, ite_true] at E2
  have hρ := sc.rho
  have hbit1 := h.A0_bit (ha₁ % g) (Nat.mod_lt _ hg)
  have hsum : ∑ r ∈ Finset.range (wg - 1), (A0 (r + 1) - B0 (r + 1)) +
      (A0 wg - B0 wg) = -(A0 0 - B0 0) := by
    have e : wg = (wg - 1) + 1 := by omega
    have h3 : genSum (incr A0 B0 g) wg = ∑ r ∈ Finset.range (wg - 1), (A0 (r + 1) - B0 (r + 1)) +
        (A0 wg - B0 wg) := by
      conv_lhs => rw [e]
      rw [genSum_incr_succ, ← e, ordFold_genSum_incr_lt A0 B0 (show wg - 1 < g by omega),
        Nat.mod_eq_of_lt (by omega : wg < g)]
    rw [← h3]; exact d3
  have hbg : b = 0 ∨ g ≤ b * g := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · left; exact h0
    · right; exact Nat.le_mul_of_pos_left g h0
  rcases hbit1 with h0 | h1
  · -- `ρ = 0`: the slots are `τ = t < g` and `σ = s - b g`
    have hρB : B0 (hb₁ % g) = 0 := by rw [← hρ]; exact h0
    have hτ : ha₁ < g := by
      rcases hτs with ⟨h1, -⟩ | ⟨h1, h2, h3, h4⟩
      · exact h1
      · have := G1 (by omega) (by omega)
        omega
    have hσ : b * g ≤ hb₁ := by
      by_contra hcon
      have hlt : hb₁ % g = hb₁ := by
        rcases hσs with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
        · exact h2
        · omega
      have := G4 (by omega) (by omega)
      omega
    have hτ' : ha₁ % g = ha₁ := Nat.mod_eq_of_lt hτ
    have hσ' : hb₁ % g = hb₁ - b * g := by
      rcases hσs with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · have : b * g = 0 := by
          rcases hbg with h0 | h0
          · simp [h0]
          · omega
        rw [h2]; omega
      · exact h2
    simp only [h0, hρB] at E1 E2 ⊢
    rw [hτ', hσ']
    have hi : (if 0 < ha₁ then (1 : ℤ) else 0) = if 1 ≤ ha₁ then 1 else 0 := by
      split_ifs <;> omega
    have hj : (if hb₁ - b * g < wg then (1 : ℤ) else 0) = if hb₁ < b * g + wg then 1 else 0 := by
      split_ifs <;> omega
    rw [hi, hj]
    split_ifs at E1 E2 ⊢ <;> omega
  · -- `ρ = 1`
    rw [h1] at E1 E2 ⊢
    refine ⟨?_, ?_, ?_⟩
    · split_ifs at E1 ⊢ <;> omega
    · split_ifs at E2 ⊢ <;> omega
    · split_ifs at E1 E2 ⊢ <;> omega

end OrdinaryDrift
end SkewGluing
