import SkewGluing.MixedFold.Gen

/-!
# Zero drift

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, the drift argument: `Δ = 0`, and `eq:gluing-pinches`).

With the generic words `Ab`, `Bb` and the deviation sums of `MixedFold.Gen`, the singleton height
`H_{q-1} = 1` of each chart gives `a Δ - Ab_g + I = 0` (`mixFold_genE2`), where `I ∈ [0, 2]` is the
sum of the initial deviations, which sit at the two phases (`MixFoldPair.devSum_init`).  Since
`gcd(a, c) = 1` and `a, c ≥ 2` this forces `Δ = 0` and `I = Ab_g` for both charts.

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

theorem mixFold_nat_mul_pred (a g : ℕ) (ha : 1 ≤ a) (hg : 1 ≤ g) :
    a * g - 1 = (g - 1) + (a - 1) * g := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_mul]
  simp only [Nat.add_sub_cancel, one_mul]
  omega

/-- The generic heights at `g - 1`: `H̄(g-1) = 1 + Δ - (Ab_g - Bb_g)`. -/
theorem mixFold_gen_ht_pred {Ab Bb : ℤ → ℤ} {g : ℕ} (hg : 1 ≤ g) :
    mixFold_ht Ab Bb (g - 1) = mixFold_ht Ab Bb g - (Ab g - Bb g) := by
  have h := mixFold_ht_succ Ab Bb (g - 1)
  have e : g - 1 + 1 = g := by omega
  rw [e] at h
  have e2 : ((g - 1 : ℕ) : ℤ) + 1 = g := by omega
  rw [e2] at h
  linarith

/-- **The singleton height `H_{q-1} = 1`, in terms of generic data.**  For `q = a g`:
`a Δ - (Ab_g - Bb_g) + devSum (q - 1) = 0`. -/
theorem mixFold_genE2 {A B Ab Bb : ℤ → ℤ} {g a : ℕ} (hg : 1 ≤ g) (ha : 1 ≤ a)
    (hA : ∀ x, Ab (x + g) = Ab x) (hB : ∀ x, Bb (x + g) = Bb x)
    (hH : mixFold_ht A B (a * g - 1) = 1) :
    (a : ℤ) * (mixFold_ht Ab Bb g - 1) - (Ab g - Bb g) +
      mixFold_devSum A B Ab Bb (a * g - 1) = 0 := by
  rw [mixFold_ht_eq_add_dev A B Ab Bb, mixFold_nat_mul_pred a g ha hg,
    mixFold_gen_ht_mul hA hB, mixFold_gen_ht_pred hg] at hH
  have e : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
  rw [e] at hH
  rw [mixFold_nat_mul_pred a g ha hg]
  linarith

theorem mixFold_devSum_single (A B Ab Bb : ℤ → ℤ) (n : ℕ) (x : ℤ) (h1 : 1 ≤ x)
    (h2 : x ≤ (n : ℤ)) (hS : ∀ y : ℤ, 1 ≤ y → y ≤ (n : ℤ) → y ≠ x → mixFold_dev A B Ab Bb y = 0) :
    mixFold_devSum A B Ab Bb n = mixFold_dev A B Ab Bb x := by
  rw [mixFold_devSum_eq_of_support A B Ab Bb n {x}
    (fun y hy1 hy2 hy => hS y hy1 hy2 (by simpa using hy))]
  have : ({x} : Finset ℤ).filter (fun y => 1 ≤ y ∧ y ≤ (n : ℤ)) = {x} := by
    ext y; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, h1, h2⟩
  rw [this]; simp

theorem mixFold_devSum_pair (A B Ab Bb : ℤ → ℤ) (n : ℕ) (x₁ x₂ : ℤ) (hne : x₁ ≠ x₂)
    (h1 : 1 ≤ x₁) (h1' : x₁ ≤ (n : ℤ)) (h2 : 1 ≤ x₂) (h2' : x₂ ≤ (n : ℤ))
    (hS : ∀ y : ℤ, 1 ≤ y → y ≤ (n : ℤ) → y ≠ x₁ → y ≠ x₂ → mixFold_dev A B Ab Bb y = 0) :
    mixFold_devSum A B Ab Bb n = mixFold_dev A B Ab Bb x₁ + mixFold_dev A B Ab Bb x₂ := by
  rw [mixFold_devSum_eq_of_support A B Ab Bb n {x₁, x₂} (fun y hy1 hy2 hy => hS y hy1 hy2
    (fun h => hy (by simp [h])) (fun h => hy (by simp [h])))]
  have : ({x₁, x₂} : Finset ℤ).filter (fun y => 1 ≤ y ∧ y ≤ (n : ℤ)) = {x₁, x₂} := by
    ext y; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, h1, h1'⟩
      · exact ⟨Or.inr rfl, h2, h2'⟩
  rw [this, Finset.sum_pair hne]

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}
  {P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂} {Ab Bb : ℤ → ℤ}

/-- The initial deviation mass of the first chart: the deviations at the phases `t₁` (when
`t₁ ≥ 1`) and `s₁`, where `A = 1`. -/
def initMass (Ab : ℤ → ℤ) (s₁ t₁ : ℤ) : ℤ := (if 1 ≤ t₁ then 1 - Ab t₁ else 0) + (1 - Ab s₁)

theorem initMass_nonneg (hAb : ∀ x, Ab x = 0 ∨ Ab x = 1) (s₁ t₁ : ℤ) : 0 ≤ initMass Ab s₁ t₁ := by
  unfold initMass
  have := hAb t₁; have := hAb s₁
  split_ifs <;> omega

theorem initMass_le (hAb : ∀ x, Ab x = 0 ∨ Ab x = 1) (s₁ t₁ : ℤ) : initMass Ab s₁ t₁ ≤ 2 := by
  unfold initMass
  have := hAb t₁; have := hAb s₁
  split_ifs <;> omega

theorem Gen.init_support (hG : P.Gen Ab Bb) {y : ℤ} (h1 : 1 ≤ y) (h2 : y ≤ (p : ℤ) - 1)
    (h : mixFold_dev A B Ab Bb y ≠ 0) : y = t₁ ∨ y = s₁ := by
  have hN := P.c₁.two_q_add_w_le
  have hsim := hG.dev_ne_zero_sim P h1 (by omega) h
  have e : y % (p : ℤ) = y := Int.emod_eq_of_lt (by omega) (by omega)
  have := hsim.1
  rw [e] at this
  simpa using this

theorem Gen.dev_t (hG : P.Gen Ab Bb) (ht : 1 ≤ t₁) :
    mixFold_dev A B Ab Bb t₁ = 1 - Ab t₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  rw [hG.dev_eq P ht (by omega)]
  have := (P.c₁.caps_d P.w₁_pos rfl).1 ht
  rw [this]

theorem Gen.dev_s (hG : P.Gen Ab Bb) : mixFold_dev A B Ab Bb s₁ = 1 - Ab s₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  rw [hG.dev_eq P hs1 (by omega)]
  have := (P.c₁.caps_d P.w₁_pos rfl).2.1
  rw [this]

/-- The deviation sum over the initial region is the initial mass of the first chart. -/
theorem Gen.devSum_init (hG : P.Gen Ab Bb) {n : ℕ} (hn1 : s₁ ≤ (n : ℤ))
    (hn2 : (n : ℤ) ≤ (p : ℤ) - 1) :
    mixFold_devSum A B Ab Bb n = initMass Ab s₁ t₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  have hwp := P.c₁.w_lt
  unfold initMass
  by_cases ht : 1 ≤ t₁
  · simp only [ht, ite_true]
    rw [mixFold_devSum_pair A B Ab Bb n t₁ s₁ (by omega) ht (by omega) hs1 hn1
      (fun y hy1 hy2 hne1 hne2 => by
        by_contra h
        rcases hG.init_support hy1 (by omega) h with rfl | rfl
        · exact hne1 rfl
        · exact hne2 rfl), hG.dev_t ht, hG.dev_s]
  · simp only [ht, ite_false]
    rw [mixFold_devSum_single A B Ab Bb n s₁ hs1 hn1
      (fun y hy1 hy2 hne => by
        by_contra h
        rcases hG.init_support hy1 (by omega) h with rfl | rfl
        · omega
        · exact hne rfl), hG.dev_s]
    ring

theorem Gen.Bb_g (hG : P.Gen Ab Bb) {a : ℕ} (ha : p = a * Nat.gcd p Q) (ha1 : 1 ≤ a) :
    Bb (Nat.gcd p Q : ℕ) = 0 := by
  have hN := P.c₁.two_q_add_w_le
  have hq := P.c₁.q_pos
  have h1 := hG.Bb_mul P (Nat.gcd p Q : ℕ) (a - 1)
  have e : (((Nat.gcd p Q : ℕ) : ℤ) + ((a - 1 : ℕ) : ℤ) * ((Nat.gcd p Q : ℕ) : ℤ)) = (p : ℤ) := by
    have : (p : ℤ) = (a : ℤ) * (Nat.gcd p Q : ℕ) := by exact_mod_cast ha
    have e2 : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
    rw [e2, this]; ring
  rw [e] at h1
  rw [← h1, ← hG.B_eq p (by omega) (by omega)]
  exact (P.c₁.caps_d P.w₁_pos rfl).2.2.2.2.2

/-- **`a Δ - Ab_g + I₁ = 0`** for the first chart `p = a g`. -/
theorem Gen.E2 (hG : P.Gen Ab Bb) {a : ℕ} (ha : p = a * Nat.gcd p Q) (ha1 : 1 ≤ a) :
    (a : ℤ) * (mixFold_ht Ab Bb (Nat.gcd p Q : ℕ) - 1) - Ab (Nat.gcd p Q : ℕ) +
      initMass Ab s₁ t₁ = 0 := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hwp := P.c₁.w_lt
  have hg := P.g_pos
  have hH := P.c₁.single_d P.w₁_pos rfl
  rw [ha] at hH
  have := mixFold_genE2 (A := A) (B := B) (Ab := Ab) (Bb := Bb) hg ha1 hG.Ab_per hG.Bb_per hH
  rw [hG.Bb_g ha ha1] at this
  have hp1 : 1 ≤ p := P.p_pos
  have hdev := hG.devSum_init (n := a * Nat.gcd p Q - 1) (by rw [← ha]; omega)
    (by rw [← ha]; omega)
  rw [hdev] at this
  linarith

/-- **Zero drift.**  `Δ = 0`, and the initial deviation mass of each chart is `Ab_g`. -/
theorem Gen.drift (hG : P.Gen Ab Bb) :
    mixFold_ht Ab Bb (Nat.gcd p Q : ℕ) = 1 ∧ initMass Ab s₁ t₁ = Ab (Nat.gcd p Q : ℕ) ∧
      initMass Ab s₂ t₂ = Ab (Nat.gcd p Q : ℕ) := by
  obtain ⟨a, c, hac, hp, hQ⟩ := Nat.exists_coprime p Q
  have hg := P.g_pos
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · have := P.p_pos; rw [h] at hp; omega
    · exact h
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · have := P.Q_pos; rw [h] at hQ; omega
    · exact h
  have ha2 : 2 ≤ a := by
    by_contra h
    have : a = 1 := by omega
    apply P.nd₁
    rw [hp, this, one_mul]; exact Nat.gcd_dvd_right p Q
  have hc2 : 2 ≤ c := by
    by_contra h
    have : c = 1 := by omega
    apply P.nd₂
    rw [hQ, this, one_mul]; exact Nat.gcd_dvd_left p Q
  have e1 := hG.E2 hp ha1
  have hQ' : Q = c * Nat.gcd Q p := by rw [Nat.gcd_comm]; exact hQ
  have e2 := hG.symm.E2 hQ' hc1
  rw [Nat.gcd_comm Q p] at e2
  have b1 : 0 ≤ Ab (Nat.gcd p Q : ℕ) ∧ Ab (Nat.gcd p Q : ℕ) ≤ 1 := by
    have := hG.Ab_bit (Nat.gcd p Q : ℕ); omega
  have i1 := initMass_nonneg hG.Ab_bit s₁ t₁
  have i1' := initMass_le hG.Ab_bit s₁ t₁
  have i2 := initMass_nonneg hG.Ab_bit s₂ t₂
  have i2' := initMass_le hG.Ab_bit s₂ t₂
  have hΔ : mixFold_ht Ab Bb (Nat.gcd p Q : ℕ) - 1 = 0 := by
    set D := mixFold_ht Ab Bb (Nat.gcd p Q : ℕ) - 1 with hD
    have ha2' : (2 : ℤ) ≤ a := by exact_mod_cast ha2
    have hc2' : (2 : ℤ) ≤ c := by exact_mod_cast hc2
    rcases lt_trichotomy D 0 with hneg | hz | hpos
    · exfalso
      have h1 : (a : ℤ) ≤ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a) (by linarith : (0 : ℤ) ≤ -D - 1)]
      have h2 : (c : ℤ) ≤ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ c) (by linarith : (0 : ℤ) ≤ -D - 1)]
      have : a = 2 := by omega
      have : c = 2 := by omega
      subst_vars
      exact absurd hac (by decide)
    · exact hz
    · exfalso
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a - 2) (by linarith : (0 : ℤ) ≤ D - 1)]
  rw [hΔ] at e1 e2
  refine ⟨by linarith, by linarith, by linarith⟩

end MixFoldPair

end SkewGluing
