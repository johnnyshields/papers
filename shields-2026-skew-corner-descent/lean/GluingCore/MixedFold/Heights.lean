/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MixedFold/Heights.lean`. -/
import GluingCore.MixedFold.Slots

/-!
# Heights of the parent at the pinch positions

Formalizes `shields-2026-skew-factor-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, `eq:gluing-pinches` and the sum of the two generic slot bits).

With the generic words, the first interface relation of the first chart gives
`Ab t₁ + Ab s₁ = 1` (`Gen.Ab_phase_sum`), the terminal deviations give
`Ab t₁ + [s₁ < w₁] Ab s₁ = 1 - Ab v` (`Gen.term_mass`), and the parent has height one at
`v`, `g - 1`, and `N - g` (`Gen.ht_v`, `Gen.ht_pred_g`, `Gen.ht_Ng`).

Sorry-free.
-/

namespace GluingCore

open PeriodWords

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}
  {P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂} {Ab Bb : ℤ → ℤ} {a b r M v : ℕ}

theorem sim_mid (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) {y : ℤ} (h1 : (w₁ : ℤ) + 1 ≤ y)
    (h2 : y ≤ (w₁ : ℤ) + p) (hs : mixFoldSim p Q s₁ t₁ s₂ t₂ y) :
    y = (p : ℤ) + t₁ ∨ y = (p : ℤ) + s₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hwp := P.c₁.w_lt
  have key : ∀ c : ℤ, 0 ≤ c → c ≤ w₁ → y % (p : ℤ) = c → y = (p : ℤ) + c := by
    intro c hc0 hc1 hyc
    have hmod : ((p : ℤ) + c) % (p : ℤ) = c := by
      rw [Int.add_emod, Int.emod_self, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
        Int.emod_eq_of_lt hc0 (by omega)]
    have hd : (p : ℤ) ∣ y - ((p : ℤ) + c) :=
      PeriodWords.dvd_sub_of_emod_eq (by rw [hyc, hmod])
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  have := hs.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact Or.inl (key t₁ ht1 (by omega) h)
  · exact Or.inr (key s₁ (by omega) (by omega) h)

theorem Gen.Ab_phase_sum (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) : Ab t₁ + Ab s₁ = 1 := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  have hwp := P.c₁.w_lt
  have hN := P.c₁.two_q_add_w_le
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  have hint := P.x₁.inter hN
  rw [mixFold_ht_eq_add_dev A B Ab Bb (p + w₁), mixFold_ht_eq_add_dev A B Ab Bb w₁] at hint
  have e1 : p + w₁ = w₁ + a * Nat.gcd p Q := by have := hA.hp; omega
  have hg1 := mixFold_gen_ht_mul (Ab := Ab) (Bb := Bb) (g := Nat.gcd p Q) hG.Ab_per hG.Bb_per w₁ a
  rw [← e1, hΔ] at hg1
  have hsplit := mixFold_devSum_add' A B Ab Bb w₁ p
  have e2 : w₁ + p = p + w₁ := by ring
  rw [e2] at hsplit
  have hW := mixFold_winSum_pair A B Ab Bb w₁ p ((p : ℤ) + t₁) ((p : ℤ) + s₁) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun y hy1 hy2 hne1 hne2 => by
      by_contra h
      have := hG.dev_ne_zero_sim P (by omega) (by omega) h
      rcases sim_mid P hy1 (by omega) this with h' | h'
      · exact hne1 h'
      · exact hne2 h')
  rw [hG.dev_eq P (by omega) (by omega), hG.dev_eq P (by omega) (by omega)] at hW
  have hq1 : Ab ((p : ℤ) + t₁) = Ab t₁ := by
    apply hG.Ab_eq_of_dvd; exact ⟨-(a : ℤ), by rw [cp]; ring⟩
  have hq2 : Ab ((p : ℤ) + s₁) = Ab s₁ := by
    apply hG.Ab_eq_of_dvd; exact ⟨-(a : ℤ), by rw [cp]; ring⟩
  rw [hq1, hq2] at hW
  linarith

theorem Gen.devSum_v (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_devSum A B Ab Bb v = Ab (Nat.gcd p Q : ℕ) := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hvg := hA.hvg
  have hp1 := P.p_pos
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hwp := P.c₁.w_lt
  have hD := hG.devSum_init (n := p - 1) (by omega) (by omega)
  have hsplit := mixFold_devSum_add' A B Ab Bb v (p - 1 - v)
  have e : v + (p - 1 - v) = p - 1 := by omega
  rw [e, hD, hI] at hsplit
  have h0 := mixFold_winSum_zero A B Ab Bb v (p - 1 - v) (fun y hy1 hy2 =>
    hG.init_conf hA y (by omega) (by omega))
  linarith

theorem Gen.ht_v (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) : mixFold_ht A B v = 1 := by
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hG.ht_gen_v hA, hG.devSum_v hA]; ring

theorem Gen.ht_pred_g (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_ht A B (Nat.gcd p Q - 1) = 1 := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hvg := hA.hvg
  have hg := P.g_pos
  have hsplit := mixFold_devSum_add' A B Ab Bb v (Nat.gcd p Q - 1 - v)
  have e : v + (Nat.gcd p Q - 1 - v) = Nat.gcd p Q - 1 := by omega
  rw [e, hG.devSum_v hA] at hsplit
  have h0 := mixFold_winSum_zero A B Ab Bb v (Nat.gcd p Q - 1 - v) (fun y hy1 hy2 =>
    hG.init_conf hA y (by omega) (by omega))
  rw [mixFold_ht_eq_add_dev A B Ab Bb, mixFold_gen_ht_pred hg, hΔ, hG.Bb_g' hA, hsplit, h0]
  ring

theorem Gen.term_mass (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    Ab t₁ + (if s₁ < w₁ then Ab s₁ else 0) = 1 - Ab (v : ℤ) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  have hwp := P.c₁.w_lt
  have hN := P.c₁.two_q_add_w_le
  have hq := P.p_pos
  have hW := hG.term_window hA
  have hcast : ((N - p : ℕ) : ℤ) = (N : ℤ) - p := by omega
  have hcast2 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  by_cases hsw : s₁ < w₁
  · simp only [hsw, ite_true]
    rw [mixFold_winSum_pair A B Ab Bb (N - p) (p - 1) ((N : ℤ) - w₁ + t₁) ((N : ℤ) - w₁ + s₁)
      (by omega) (by omega) (by omega) (by omega) (by omega) (fun y hy1 hy2 hne1 hne2 => by
        by_contra h
        rcases hG.term_support hA (by omega) (by omega) h with h' | h'
        · exact hne1 h'
        · exact hne2 h'), SlotOK.dev_term hG (slotOK_t P) (by omega),
      SlotOK.dev_term hG (slotOK_s P) hsw, hA.Ab_term hG, hA.Ab_term hG] at hW
    linarith
  · simp only [hsw, ite_false]
    rw [mixFold_winSum_single A B Ab Bb (N - p) (p - 1) ((N : ℤ) - w₁ + t₁)
      (by omega) (by omega) (fun y hy1 hy2 hne => by
        by_contra h
        rcases hG.term_support hA (by omega) (by omega) h with h' | h'
        · exact hne h'
        · omega), SlotOK.dev_term hG (slotOK_t P) (by omega), hA.Ab_term hG] at hW
    linarith

theorem Gen.ht_Ng (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_ht A B (N - Nat.gcd p Q) = 1 := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  have hN := P.c₁.two_q_add_w_le
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hvg := hA.hvg
  have hg := P.g_pos
  have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hMg : M * Nat.gcd p Q + v = N := hA.hN.symm
  have h1 := P.ok.last
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hG.ht_gen_N1 hA] at h1
  have hsplit := mixFold_devSum_add' A B Ab Bb (N - Nat.gcd p Q) (Nat.gcd p Q - 1)
  have e : N - Nat.gcd p Q + (Nat.gcd p Q - 1) = N - 1 := by omega
  rw [e] at hsplit
  have hW := hG.term_window hA
  have hsp := mixFold_winSum_add A B Ab Bb (N - p) (p - Nat.gcd p Q) (Nat.gcd p Q - 1)
  have e1 : p - Nat.gcd p Q + (Nat.gcd p Q - 1) = p - 1 := by omega
  have e2 : N - p + (p - Nat.gcd p Q) = N - Nat.gcd p Q := by omega
  rw [e1, e2] at hsp
  have hz := mixFold_winSum_zero A B Ab Bb (N - p) (p - Nat.gcd p Q) (fun y hy1 hy2 =>
    hG.term_conf hA y (by omega) (by omega))
  have e3 : N - Nat.gcd p Q = v + (M - 1) * Nat.gcd p Q := by
    have : (M - 1) * Nat.gcd p Q + Nat.gcd p Q = M * Nat.gcd p Q := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  have hgen : mixFold_ht Ab Bb (N - Nat.gcd p Q) = 1 - Ab (Nat.gcd p Q : ℕ) := by
    rw [e3, mixFold_gen_ht_mul hG.Ab_per hG.Bb_per, hΔ, hG.ht_gen_v hA]; ring
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hgen]
  linarith

end MixFoldPair

end GluingCore
