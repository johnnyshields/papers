/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MixedFold/Slots.lean`. -/
import GluingCore.MixedFold.Confine

/-!
# The phases of the first chart, read modulo `g`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, `eq:gluing-mixed-phases`).

Each phase `x ∈ {t₁, s₁}` of the first chart carries the initial bit `A_x = 1` and, when `x < w₁`,
the terminal bit `A_{N - w₁ + x} = 0` (`SlotOK`).  Combined with the confinement of the deviations
(`Gen.init_conf`, `Gen.term_conf`) this places the class `x mod g` of every phase in `[0, v]`
(`SlotOK.class_le`) and transports the caps to the first and last block: `A_{x mod g} = 1` when
`x mod g ≥ 1` (`SlotOK.init_cap`) and `A_{M g + x mod g} = 0` when `x mod g < v`
(`SlotOK.term_cap`).

Sorry-free.
-/

namespace GluingCore

open PeriodWords

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}
  {P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂} {Ab Bb : ℤ → ℤ} {a b r M v : ℕ}

theorem Gen.Ab_int_mul (hG : P.Gen Ab Bb) (x k : ℤ) : Ab (x + k * (Nat.gcd p Q : ℕ)) = Ab x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : x + ((k : ℤ) + 1) * ((Nat.gcd p Q : ℕ) : ℤ) =
        (x + (k : ℤ) * ((Nat.gcd p Q : ℕ) : ℤ)) + ((Nat.gcd p Q : ℕ) : ℤ) := by ring
    rw [e, hG.Ab_per, ih]
  | pred k ih =>
    have e : x + (-(k : ℤ) - 1) * ((Nat.gcd p Q : ℕ) : ℤ) =
        (x + (-(k : ℤ)) * ((Nat.gcd p Q : ℕ) : ℤ)) - ((Nat.gcd p Q : ℕ) : ℤ) := by ring
    have h := hG.Ab_per (x + (-(k : ℤ) - 1) * ((Nat.gcd p Q : ℕ) : ℤ))
    rw [show x + (-(k : ℤ) - 1) * ((Nat.gcd p Q : ℕ) : ℤ) + ((Nat.gcd p Q : ℕ) : ℤ) =
      x + (-(k : ℤ)) * ((Nat.gcd p Q : ℕ) : ℤ) by ring] at h
    rw [← h, ih]

theorem Gen.Ab_eq_of_dvd (hG : P.Gen Ab Bb) {x y : ℤ} (h : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) :
    Ab x = Ab y := by
  obtain ⟨k, hk⟩ := h
  have : y = x + k * ((Nat.gcd p Q : ℕ) : ℤ) := by linarith
  rw [this, hG.Ab_int_mul]

theorem Gen.Ab_mod (hG : P.Gen Ab Bb) (x : ℤ) : Ab (x % ((Nat.gcd p Q : ℕ) : ℤ)) = Ab x :=
  hG.Ab_eq_of_dvd ⟨x / ((Nat.gcd p Q : ℕ) : ℤ), by
    have := Int.emod_def x ((Nat.gcd p Q : ℕ) : ℤ); linarith⟩

/-- A phase of the first chart with its caps. -/
def SlotOK (_P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) (x : ℤ) : Prop :=
  0 ≤ x ∧ x ≤ w₁ ∧ (1 ≤ x → A x = 1) ∧ (x < w₁ → A ((N : ℤ) - w₁ + x) = 0) ∧ (x = t₁ ∨ x = s₁)

theorem slotOK_t (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) : P.SlotOK t₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have caps := P.c₁.caps_d P.w₁_pos rfl
  exact ⟨ht1, by omega, caps.1, fun _ => caps.2.2.1, Or.inl rfl⟩

theorem slotOK_s (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) : P.SlotOK s₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  have caps := P.c₁.caps_d P.w₁_pos rfl
  exact ⟨by omega, hs2, fun _ => caps.2.1, fun h => caps.2.2.2.1 h, Or.inr rfl⟩

theorem SlotOK.dev_init (hG : P.Gen Ab Bb) {x : ℤ} (hx : P.SlotOK x) (h1 : 1 ≤ x) :
    mixFold_dev A B Ab Bb x = 1 - Ab x := by
  obtain ⟨hx0, hx1, hxA, hxe, hxt⟩ := hx
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  rw [hG.dev_eq P h1 (by omega), hxA h1]

theorem SlotOK.dev_term (hG : P.Gen Ab Bb) {x : ℤ} (hx : P.SlotOK x) (hlt : x < w₁) :
    mixFold_dev A B Ab Bb ((N : ℤ) - w₁ + x) = - Ab ((N : ℤ) - w₁ + x) := by
  obtain ⟨hx0, hx1, hxA, hxe, hxt⟩ := hx
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  rw [hG.dev_eq P (by omega) (by omega), hxe hlt]; ring

theorem Arith.Ab_term (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) (x : ℤ) :
    Ab ((N : ℤ) - w₁ + x) = Ab x := by
  apply hG.Ab_eq_of_dvd
  have hMb : b ≤ M := by have := hA.hM; nlinarith
  have : (N : ℤ) - w₁ = ((M : ℤ) - b) * ((Nat.gcd p Q : ℕ) : ℤ) := by
    have h1 : (N : ℤ) = (M : ℤ) * (Nat.gcd p Q : ℕ) + v := by exact_mod_cast hA.hN
    have h2 : (w₁ : ℤ) = (b : ℤ) * (Nat.gcd p Q : ℕ) + v := by exact_mod_cast hA.hw
    rw [h1, h2]; ring
  exact ⟨-((M : ℤ) - b), by linear_combination (-1 : ℤ) * this⟩

theorem Arith.cast_facts (hA : P.Arith a b r M v) :
    (N : ℤ) = (M : ℤ) * (Nat.gcd p Q : ℕ) + v ∧ (w₁ : ℤ) = (b : ℤ) * (Nat.gcd p Q : ℕ) + v ∧
      (p : ℤ) = (a : ℤ) * (Nat.gcd p Q : ℕ) :=
  ⟨by exact_mod_cast hA.hN, by exact_mod_cast hA.hw, by exact_mod_cast hA.hp⟩

theorem SlotOK.class_le (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {x : ℤ} (hx : P.SlotOK x) :
    x % ((Nat.gcd p Q : ℕ) : ℤ) ≤ v := by
  obtain ⟨hx0, hx1, hxA, hxe, hxt⟩ := id hx
  have hvg := hA.hvg
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  by_cases hxv : x ≤ v
  · rw [Int.emod_eq_of_lt hx0 (by omega)]; exact hxv
  · have h1 : 1 ≤ x := by omega
    have hd := hx.dev_init hG h1
    rw [hG.init_conf hA x (by omega) (by omega)] at hd
    have hAb : Ab x = 1 := by omega
    by_cases hxw : x < w₁
    · have hdt := hx.dev_term hG hxw
      rw [hA.Ab_term hG x, hAb] at hdt
      by_contra hcon
      have hge : (M : ℤ) * (Nat.gcd p Q : ℕ) ≤ (N : ℤ) - w₁ + x := by
        by_contra hlt
        have := hG.term_conf hA ((N : ℤ) - w₁ + x) (by omega) (by omega)
        omega
      have hb : (b : ℤ) * (Nat.gcd p Q : ℕ) ≤ x := by
        have : (N : ℤ) - w₁ = ((M : ℤ) - b) * (Nat.gcd p Q : ℕ) := by rw [cN, cw]; ring
        nlinarith
      have e : x % ((Nat.gcd p Q : ℕ) : ℤ) = x - (b : ℤ) * (Nat.gcd p Q : ℕ) := by
        have h := Int.add_mul_emod_self_right (x - (b : ℤ) * (Nat.gcd p Q : ℕ)) b
          ((Nat.gcd p Q : ℕ) : ℤ)
        rw [show x - (b : ℤ) * (Nat.gcd p Q : ℕ) + (b : ℤ) * (Nat.gcd p Q : ℕ) = x by ring] at h
        rw [h]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      omega
    · have hxe' : x = w₁ := by omega
      rw [hxe', cw, show (b : ℤ) * (Nat.gcd p Q : ℕ) + v = (v : ℤ) + (b : ℤ) * (Nat.gcd p Q : ℕ)
        by ring, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]

theorem Arith.sim_term (hA : P.Arith a b r M v) {y : ℤ} (h1 : (N : ℤ) - p < y)
    (h2 : y ≤ (N : ℤ) - 1) (hs : mixFoldSim p Q s₁ t₁ s₂ t₂ y) :
    y = (N : ℤ) - w₁ + t₁ ∨ y = (N : ℤ) - w₁ + s₁ := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hwp := P.c₁.w_lt
  have hN := P.c₁.two_q_add_w_le
  have hNw : (N : ℤ) - w₁ = (r : ℤ) * p := by
    have : (N : ℤ) = (r : ℤ) * p + w₁ := by exact_mod_cast hA.hNr
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
  have := hs.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact Or.inl (key t₁ ht1 (by omega) h)
  · exact Or.inr (key s₁ (by omega) (by omega) h)

theorem Arith.sim_small {y : ℤ} (hs : mixFoldSim p Q s₁ t₁ s₂ t₂ y) (h0 : 0 ≤ y) (h1 : y < p) :
    y = t₁ ∨ y = s₁ := by
  have := hs.1
  rw [Int.emod_eq_of_lt h0 h1] at this
  simpa using this

theorem class_distinct_phase {g : ℕ} (hnc : t₁ % (g : ℤ) ≠ s₁ % (g : ℤ)) {x y : ℤ}
    (hx : x = t₁ ∨ x = s₁) (hy : y = t₁ ∨ y = s₁) (hxy : x ≠ y) : x % (g : ℤ) ≠ y % (g : ℤ) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact hnc
  · exact fun h => hnc h.symm
  · exact absurd rfl hxy

theorem SlotOK.init_cap (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {x : ℤ} (hx : P.SlotOK x)
    (hnc : t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ≠ s₁ % ((Nat.gcd p Q : ℕ) : ℤ))
    (hρ : 1 ≤ x % ((Nat.gcd p Q : ℕ) : ℤ)) : A (x % ((Nat.gcd p Q : ℕ) : ℤ)) = 1 := by
  obtain ⟨hx0, hx1, hxA, hxe, hxt⟩ := id hx
  have hvg := hA.hvg
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hcl := hx.class_le hG hA
  have hρ0 := Int.emod_nonneg x (show ((Nat.gcd p Q : ℕ) : ℤ) ≠ 0 by omega)
  have hρg := Int.emod_lt_of_pos x (show (0 : ℤ) < ((Nat.gcd p Q : ℕ) : ℤ) by omega)
  by_cases hxv : x ≤ v
  · have e : x % ((Nat.gcd p Q : ℕ) : ℤ) = x := Int.emod_eq_of_lt hx0 (by omega)
    rw [e]; exact hxA (by omega)
  · have hd := hx.dev_init hG (by omega)
    rw [hG.init_conf hA x (by omega) (by omega)] at hd
    have hAb : Ab x = 1 := by omega
    have hsim : ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ (x % ((Nat.gcd p Q : ℕ) : ℤ)) := by
      intro hs
      have hy := Arith.sim_small hs hρ0 (by omega)
      have e : (x % ((Nat.gcd p Q : ℕ) : ℤ)) % ((Nat.gcd p Q : ℕ) : ℤ) =
          x % ((Nat.gcd p Q : ℕ) : ℤ) := Int.emod_emod_of_dvd _ dvd_rfl
      by_cases hxy : x = x % ((Nat.gcd p Q : ℕ) : ℤ)
      · omega
      · exact class_distinct_phase hnc hxt hy hxy e.symm
    rw [hG.A_eq _ hρ (by omega) hsim, hG.Ab_mod, hAb]

theorem SlotOK.term_cap (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {x : ℤ} (hx : P.SlotOK x)
    (hnc : t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ≠ s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (hxw : x < w₁)
    (hρ : x % ((Nat.gcd p Q : ℕ) : ℤ) < v) :
    A ((M : ℤ) * (Nat.gcd p Q : ℕ) + x % ((Nat.gcd p Q : ℕ) : ℤ)) = 0 := by
  obtain ⟨hx0, hx1, hxA, hxe, hxt⟩ := id hx
  have hvg := hA.hvg
  have hN := P.c₁.two_q_add_w_le
  have hwp := P.c₁.w_lt
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  have hρ0 := Int.emod_nonneg x (show ((Nat.gcd p Q : ℕ) : ℤ) ≠ 0 by omega)
  have hNw : (N : ℤ) - w₁ = ((M : ℤ) - b) * (Nat.gcd p Q : ℕ) := by rw [cN, cw]; ring
  have hxdecomp : x = (x / ((Nat.gcd p Q : ℕ) : ℤ)) * (Nat.gcd p Q : ℕ) +
      x % ((Nat.gcd p Q : ℕ) : ℤ) := by
    have := Int.emod_def x ((Nat.gcd p Q : ℕ) : ℤ); linarith
  by_cases hge : (M : ℤ) * (Nat.gcd p Q : ℕ) ≤ (N : ℤ) - w₁ + x
  · -- the terminal position is `M g + ρ`
    have hb : (b : ℤ) * (Nat.gcd p Q : ℕ) ≤ x := by nlinarith
    have e : x % ((Nat.gcd p Q : ℕ) : ℤ) = x - (b : ℤ) * (Nat.gcd p Q : ℕ) := by
      have h := Int.add_mul_emod_self_right (x - (b : ℤ) * (Nat.gcd p Q : ℕ)) b
        ((Nat.gcd p Q : ℕ) : ℤ)
      rw [show x - (b : ℤ) * (Nat.gcd p Q : ℕ) + (b : ℤ) * (Nat.gcd p Q : ℕ) = x by ring] at h
      rw [h]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have : (M : ℤ) * (Nat.gcd p Q : ℕ) + x % ((Nat.gcd p Q : ℕ) : ℤ) = (N : ℤ) - w₁ + x := by
      rw [e, hNw]; ring
    rw [this]; exact hxe hxw
  · have hd := hG.term_conf hA ((N : ℤ) - w₁ + x) (by omega) (by omega)
    rw [hx.dev_term hG hxw, hA.Ab_term hG x] at hd
    have hAb : Ab x = 0 := by omega
    have hsim : ¬ mixFoldSim p Q s₁ t₁ s₂ t₂
        ((M : ℤ) * (Nat.gcd p Q : ℕ) + x % ((Nat.gcd p Q : ℕ) : ℤ)) := by
      intro hs
      have := hA.sim_term (by omega) (by omega) hs
      have hy : ∃ y : ℤ, (y = t₁ ∨ y = s₁) ∧ (M : ℤ) * (Nat.gcd p Q : ℕ) +
          x % ((Nat.gcd p Q : ℕ) : ℤ) = (N : ℤ) - w₁ + y := by
        rcases this with h | h
        · exact ⟨t₁, Or.inl rfl, h⟩
        · exact ⟨s₁, Or.inr rfl, h⟩
      obtain ⟨y, hyt, hy⟩ := hy
      by_cases hxy : x = y
      · rw [← hxy] at hy; omega
      · have hyρ : y = (b : ℤ) * (Nat.gcd p Q : ℕ) + x % ((Nat.gcd p Q : ℕ) : ℤ) := by
          rw [hNw] at hy; nlinarith
        have h1 : y % ((Nat.gcd p Q : ℕ) : ℤ) = x % ((Nat.gcd p Q : ℕ) : ℤ) := by
          have h := Int.add_mul_emod_self_right (x % ((Nat.gcd p Q : ℕ) : ℤ)) b
            ((Nat.gcd p Q : ℕ) : ℤ)
          rw [show (b : ℤ) * (Nat.gcd p Q : ℕ) + x % ((Nat.gcd p Q : ℕ) : ℤ) =
            x % ((Nat.gcd p Q : ℕ) : ℤ) + (b : ℤ) * (Nat.gcd p Q : ℕ) by ring] at hyρ
          rw [hyρ, h, Int.emod_emod_of_dvd _ dvd_rfl]
        exact class_distinct_phase hnc hxt hyt hxy h1.symm
    rw [hG.A_eq _ (by omega) (by omega) hsim]
    have : Ab ((M : ℤ) * (Nat.gcd p Q : ℕ) + x % ((Nat.gcd p Q : ℕ) : ℤ)) = Ab x := by
      rw [← hG.Ab_mod x]
      apply hG.Ab_eq_of_dvd
      exact ⟨-(M : ℤ), by ring⟩
    rw [this, hAb]

end MixFoldPair

end GluingCore
