/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MixedFold/Confine.lean`. -/
import GluingCore.MixedFold.Window

/-!
# Confinement of the initial and terminal deviations

Formalizes `shields-2026-skew-factor-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, `eq:gluing-mixed-phases`: positivity confines the initial correction
to the first `w_g` steps, and reading backward confines the terminal deficit to the last `w_g`).

Write `p = a g`, `w₁ = b g + v`, `N = M g + v` with `0 < v < g`.  With zero drift the generic height
satisfies `H̄(v) = 1 - Ab_g`.  Positivity of the height at `v` forces every initial deviation to
sit at a position `≤ v` (`Gen.init_conf`), and positivity at `M g - 1` forces every terminal
deviation to sit at a position `≥ M g` (`Gen.term_conf`); the terminal deviations total `Ab_v - 1`
(`Gen.term_window`).

Sorry-free.
-/

namespace GluingCore

open PeriodWords

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}

/-- The arithmetic of the first chart: `p = a g`, `w₁ = b g + v`, `N = M g + v`, `N = r p + w₁`. -/
structure Arith (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) (a b r M v : ℕ) : Prop where
  hp : p = a * Nat.gcd p Q
  hw : w₁ = b * Nat.gcd p Q + v
  hN : N = M * Nat.gcd p Q + v
  hNr : N = r * p + w₁
  hM : M = r * a + b
  hv0 : 0 < v
  hvg : v < Nat.gcd p Q
  ha : 2 ≤ a
  hr : 2 ≤ r

theorem exists_arith (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    ∃ a b r M v : ℕ, P.Arith a b r M v := by
  obtain ⟨r, hr, hNr⟩ := P.c₁.span_eq
  have hg := P.g_pos
  set g := Nat.gcd p Q with hgdef
  obtain ⟨a, hp⟩ : g ∣ p := Nat.gcd_dvd_left p Q
  have hp' : p = a * g := by rw [hp]; ring
  have ha : 2 ≤ a := by
    by_contra h
    have hq := P.p_pos
    have : a = 0 ∨ a = 1 := by omega
    rcases this with h0 | h1
    · rw [h0] at hp'; omega
    · apply P.nd₁
      rw [hp', h1, one_mul]; exact Nat.gcd_dvd_right p Q
  refine ⟨a, w₁ / g, r, N / g, N % g, ⟨hp', ?_, ?_, hNr, ?_, P.rem, Nat.mod_lt _ hg, ha, hr⟩⟩
  · have : w₁ % g = N % g := by
      rw [hNr, hp']
      rw [show r * (a * g) + w₁ = w₁ + g * (r * a) by ring, Nat.add_mul_mod_self_left]
    rw [← this]; exact (Nat.div_add_mod' w₁ g).symm
  · exact (Nat.div_add_mod' N g).symm
  · have h1 : N = (N / g) * g + N % g := (Nat.div_add_mod' N g).symm
    have h2 : w₁ = (w₁ / g) * g + w₁ % g := (Nat.div_add_mod' w₁ g).symm
    have h3 : w₁ % g = N % g := by
      rw [hNr, hp']
      rw [show r * (a * g) + w₁ = w₁ + g * (r * a) by ring, Nat.add_mul_mod_self_left]
    have h4 : (N / g) * g = (r * a + w₁ / g) * g := by
      have : (N / g) * g + N % g = (r * a + w₁ / g) * g + N % g := by
        calc (N / g) * g + N % g = N := h1.symm
          _ = r * (a * g) + w₁ := by rw [← hp']; exact hNr
          _ = r * (a * g) + ((w₁ / g) * g + w₁ % g) := by rw [← h2]
          _ = (r * a + w₁ / g) * g + N % g := by rw [h3]; ring
      omega
    exact Nat.eq_of_mul_eq_mul_right hg h4

variable {P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂} {Ab Bb : ℤ → ℤ} {a b r M v : ℕ}

theorem Gen.dev_nonneg_init (hG : P.Gen Ab Bb) {y : ℤ} (h1 : 1 ≤ y) (h2 : y ≤ (p : ℤ) - 1) :
    0 ≤ mixFold_dev A B Ab Bb y := by
  by_cases h : mixFold_dev A B Ab Bb y = 0
  · omega
  · rcases hG.init_support h1 h2 h with rfl | rfl
    · rw [hG.dev_t (by omega)]
      have := hG.Ab_bit y; omega
    · rw [hG.dev_s]
      have := hG.Ab_bit y; omega

/-- `H̄(v) = 1 - Ab_g`: the first singleton height `H_{w₁} = 1`, at zero drift. -/
theorem Gen.ht_gen_v (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_ht Ab Bb v = 1 - Ab (Nat.gcd p Q : ℕ) := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have hwp := P.c₁.w_lt
  have hH := P.x₁.single_w
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hA.hw] at hH
  have e1 := mixFold_gen_ht_mul (Ab := Ab) (Bb := Bb) (g := Nat.gcd p Q) hG.Ab_per hG.Bb_per v b
  rw [add_comm v, hΔ] at *
  have hdev := hG.devSum_init (n := b * Nat.gcd p Q + v) (by rw [← hA.hw]; omega)
    (by rw [← hA.hw]; omega)
  rw [← hA.hw] at hdev
  rw [← hA.hw] at e1 hH
  rw [e1, hdev, hI] at hH
  simp at hH
  linarith

theorem Gen.init_conf (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    ∀ y : ℤ, (v : ℤ) < y → y ≤ (p : ℤ) - 1 → mixFold_dev A B Ab Bb y = 0 := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hvp : v + 1 ≤ p := by have := hA.hvg; omega
  have hN := P.c₁.two_q_add_w_le
  have hpos := P.ok.pos v (by omega)
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hG.ht_gen_v hA] at hpos
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have hwp := P.c₁.w_lt
  have hD := hG.devSum_init (n := p - 1) (by omega) (by omega)
  have hsplit := mixFold_devSum_add' A B Ab Bb v (p - 1 - v)
  have e : v + (p - 1 - v) = p - 1 := by omega
  rw [e, hD] at hsplit
  have hnn : ∀ y : ℤ, (v : ℤ) + 1 ≤ y → y ≤ (v : ℤ) + ((p - 1 - v : ℕ) : ℤ) →
      0 ≤ mixFold_dev A B Ab Bb y := fun y h1 h2 =>
    hG.dev_nonneg_init (by omega) (by omega)
  have h0 : mixFold_winSum A B Ab Bb v (p - 1 - v) = 0 := by
    have h1 := mixFold_winSum_nonneg A B Ab Bb v (p - 1 - v) hnn
    rw [hI] at hsplit
    omega
  intro y hy1 hy2
  exact mixFold_winSum_terms_zero A B Ab Bb v (p - 1 - v) hnn h0 y (by omega) (by omega)

theorem Gen.term_support (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {y : ℤ}
    (h1 : (N : ℤ) - p < y) (h2 : y ≤ (N : ℤ) - 1) (h : mixFold_dev A B Ab Bb y ≠ 0) :
    y = (N : ℤ) - w₁ + t₁ ∨ y = (N : ℤ) - w₁ + s₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hwp := P.c₁.w_lt
  have hN := P.c₁.two_q_add_w_le
  have hsim := hG.dev_ne_zero_sim P (by omega) h2 h
  have hNr := hA.hNr
  have hNw : (N : ℤ) - w₁ = (r : ℤ) * p := by
    have : (N : ℤ) = (r : ℤ) * p + w₁ := by exact_mod_cast hNr
    linarith
  have key : ∀ c : ℤ, 0 ≤ c → c ≤ w₁ → y % (p : ℤ) = c → y = (N : ℤ) - w₁ + c := by
    intro c hc0 hc1 hyc
    have hmod : ((N : ℤ) - w₁ + c) % (p : ℤ) = c := by
      rw [hNw, Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
        Int.emod_eq_of_lt hc0 (by omega)]
    have hd : (p : ℤ) ∣ y - ((N : ℤ) - w₁ + c) :=
      PeriodWords.dvd_sub_of_emod_eq (by rw [hyc, hmod])
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  have := hsim.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact Or.inl (key t₁ ht1 (by omega) h)
  · exact Or.inr (key s₁ (by omega) (by omega) h)

theorem Gen.dev_et (hG : P.Gen Ab Bb) :
    mixFold_dev A B Ab Bb ((N : ℤ) - w₁ + t₁) = - Ab ((N : ℤ) - w₁ + t₁) := by
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  rw [hG.dev_eq P (by omega) (by omega)]
  have := (P.c₁.caps_d P.w₁_pos rfl).2.2.1
  rw [this]; ring

theorem Gen.dev_es (hG : P.Gen Ab Bb) (hlt : s₁ < w₁) :
    mixFold_dev A B Ab Bb ((N : ℤ) - w₁ + s₁) = - Ab ((N : ℤ) - w₁ + s₁) := by
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  rw [hG.dev_eq P (by omega) (by omega)]
  have := (P.c₁.caps_d P.w₁_pos rfl).2.2.2.1 hlt
  rw [this]; ring

theorem Gen.term_nonpos (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {y : ℤ}
    (h1 : (N : ℤ) - p < y) (h2 : y ≤ (N : ℤ) - 1) : mixFold_dev A B Ab Bb y ≤ 0 := by
  by_cases h : mixFold_dev A B Ab Bb y = 0
  · omega
  · obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
    rcases hG.term_support hA h1 h2 h with rfl | rfl
    · rw [hG.dev_et]; have := hG.Ab_bit ((N : ℤ) - w₁ + t₁); omega
    · rw [hG.dev_es (by omega)]; have := hG.Ab_bit ((N : ℤ) - w₁ + s₁); omega

theorem Gen.Bb_v (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) : Bb (v : ℤ) = 1 := by
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  have h1 := hG.Bb_mul P (v : ℤ) b
  have e : (v : ℤ) + (b : ℤ) * (Nat.gcd p Q : ℕ) = (w₁ : ℤ) := by
    have := hA.hw
    have h2 : (w₁ : ℤ) = (b : ℤ) * (Nat.gcd p Q : ℕ) + v := by exact_mod_cast this
    rw [h2]; ring
  rw [e] at h1
  rw [← h1, ← hG.B_eq w₁ (by have := P.w₁_pos; omega) (by omega)]
  exact (P.c₁.caps_d P.w₁_pos rfl).2.2.2.2.1

theorem Gen.Bb_g' (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) : Bb (Nat.gcd p Q : ℕ) = 0 :=
  hG.Bb_g hA.hp (by have := hA.ha; omega)

theorem Gen.ht_gen_Np (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_ht Ab Bb (N - p) = 1 - Ab (Nat.gcd p Q : ℕ) := by
  obtain ⟨hΔ, -, -⟩ := hG.drift
  have hMa : a ≤ M := by
    have := hA.hM; have := hA.hr; nlinarith
  have e : N - p = v + (M - a) * Nat.gcd p Q := by
    have h1 := hA.hN; have h2 := hA.hp
    have hle : a * Nat.gcd p Q ≤ M * Nat.gcd p Q := Nat.mul_le_mul_right _ hMa
    have : N - p = (M - a) * Nat.gcd p Q + v := by
      rw [Nat.sub_mul]; omega
    omega
  rw [e, mixFold_gen_ht_mul hG.Ab_per hG.Bb_per, hΔ, hG.ht_gen_v hA]
  ring

theorem Gen.ht_gen_N1 (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_ht Ab Bb (N - 1) = 2 - Ab (Nat.gcd p Q : ℕ) - Ab (v : ℤ) := by
  obtain ⟨hΔ, -, -⟩ := hG.drift
  have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have e : N - 1 = (v - 1) + M * Nat.gcd p Q := by
    have h1 := hA.hN; have := hA.hv0; omega
  have hv1 := hA.hv0
  rw [e, mixFold_gen_ht_mul hG.Ab_per hG.Bb_per, hΔ, mixFold_gen_ht_pred hv1,
    hG.ht_gen_v hA, hG.Bb_v hA]
  ring

theorem Gen.ht_gen_Mg (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_ht Ab Bb (M * Nat.gcd p Q - 1) = 1 - Ab (Nat.gcd p Q : ℕ) := by
  obtain ⟨hΔ, -, -⟩ := hG.drift
  have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hg := P.g_pos
  rw [mixFold_nat_mul_pred M _ hM1 hg, mixFold_gen_ht_mul hG.Ab_per hG.Bb_per, hΔ,
    mixFold_gen_ht_pred hg, hG.Bb_g' hA, hΔ]
  ring

/-- The terminal deviations total `Ab_v - 1` (`= -f`). -/
theorem Gen.term_window (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_winSum A B Ab Bb (N - p) (p - 1) = Ab (v : ℤ) - 1 := by
  have hN := P.c₁.two_q_add_w_le
  have hq := P.p_pos
  have h1 := P.ok.last
  have h2 := P.x₁.single_Nq
  have e : N - p + (p - 1) = N - 1 := by omega
  rw [mixFold_ht_eq_add_dev A B Ab Bb] at h1 h2
  rw [hG.ht_gen_N1 hA] at h1
  rw [hG.ht_gen_Np hA] at h2
  have hs := mixFold_devSum_add' A B Ab Bb (N - p) (p - 1)
  rw [e] at hs
  linarith

theorem Gen.term_conf (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    ∀ y : ℤ, (N : ℤ) - p < y → y < (M : ℤ) * Nat.gcd p Q → mixFold_dev A B Ab Bb y = 0 := by
  have hN := P.c₁.two_q_add_w_le
  have hq := P.p_pos
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hvg := hA.hvg
  have hvp : v + 1 ≤ p := by omega
  have hMg : M * Nat.gcd p Q + v = N := hA.hN.symm
  have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hMg1 : Nat.gcd p Q ≤ M * Nat.gcd p Q := by nlinarith
  have hpos := P.ok.pos (M * Nat.gcd p Q - 1) (by omega)
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hG.ht_gen_Mg hA] at hpos
  have h1 := P.ok.last
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hG.ht_gen_N1 hA] at h1
  have hs1 : N - 1 = (M * Nat.gcd p Q - 1) + v := by omega
  have hsplit := mixFold_devSum_add' A B Ab Bb (M * Nat.gcd p Q - 1) v
  rw [← hs1] at hsplit
  have hW := hG.term_window hA
  have e2 : p - 1 = (p - v - 1) + v := by omega
  have e3 : N - p + (p - v - 1) = M * Nat.gcd p Q - 1 := by omega
  have hsp := mixFold_winSum_add A B Ab Bb (N - p) (p - v - 1) v
  rw [← e2, e3] at hsp
  have hnp : ∀ y : ℤ, ((N - p : ℕ) : ℤ) + 1 ≤ y → y ≤ ((N - p : ℕ) : ℤ) + ((p - v - 1 : ℕ) : ℤ) →
      mixFold_dev A B Ab Bb y ≤ 0 := fun y h1 h2 => hG.term_nonpos hA (by omega) (by omega)
  have hfirst := mixFold_winSum_nonpos A B Ab Bb (N - p) (p - v - 1) hnp
  have hfirst0 : mixFold_winSum A B Ab Bb (N - p) (p - v - 1) = 0 := by omega
  intro y hy1 hy2
  exact mixFold_winSum_terms_zero' A B Ab Bb (N - p) (p - v - 1) hnp hfirst0 y (by omega)
    (by omega)

end MixFoldPair

end GluingCore
