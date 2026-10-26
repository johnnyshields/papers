import SkewGluing.MixedFold.Deviation

/-!
# The generic words of two case-(d) charts

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`; `lem:gluing-periods` (ii)).

`MixFoldPair.Gen P Ab Bb` says that `Ab`, `Bb` are `g`-periodic bit words with `A = Ab` at every
position of `1, …, N - 1` that is not a simultaneous hole, and `B = Bb` there; `exists_gen`
produces them.  The deviations `A_y - Ab_y` vanish off simultaneous holes
(`Gen.dev_ne_zero_sim`).

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}

/-- The generic words of a pair: `g`-periodic bits `Ab`, `Bb` agreeing with `A`, `B` off the
simultaneous holes. -/
structure Gen (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) (Ab Bb : ℤ → ℤ) : Prop where
  Ab_bit : ∀ x, Ab x = 0 ∨ Ab x = 1
  Ab_per : ∀ x, Ab (x + (Nat.gcd p Q : ℕ)) = Ab x
  Bb_per : ∀ x, Bb (x + (Nat.gcd p Q : ℕ)) = Bb x
  A_eq : ∀ x, 1 ≤ x → x ≤ (N : ℤ) - 1 → ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ x → A x = Ab x
  B_eq : ∀ x, 1 ≤ x → x ≤ (N : ℤ) - 1 → B x = Bb x

theorem exists_gen (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    ∃ Ab Bb : ℤ → ℤ, P.Gen Ab Bb := by
  classical
  have hg := P.g_pos
  set g := Nat.gcd p Q with hgdef
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  have hN := P.c₁.two_q_add_w_le
  have hq := P.c₁.q_pos
  have hgp : g ∣ p := Nat.gcd_dvd_left p Q
  have hgle : g ≤ p := Nat.le_of_dvd hq hgp
  let Ab0 : ℤ → ℤ := fun ρ =>
    if h : ∃ y : ℤ, 1 ≤ y ∧ y ≤ (N : ℤ) - 1 ∧ y % (g : ℤ) = ρ ∧
        ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ y then A h.choose else 0
  let Ab : ℤ → ℤ := fun x => Ab0 (x % (g : ℤ))
  let Bb : ℤ → ℤ := fun x => B ((x - 1) % (g : ℤ) + 1)
  refine ⟨Ab, Bb, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change Ab0 (x % (g : ℤ)) = 0 ∨ Ab0 (x % (g : ℤ)) = 1
    by_cases h : ∃ y : ℤ, 1 ≤ y ∧ y ≤ (N : ℤ) - 1 ∧ y % (g : ℤ) = x % (g : ℤ) ∧
        ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ y
    · simp only [Ab0, h, dite_true]
      obtain ⟨h1, h2, -⟩ := h.choose_spec
      exact P.ok.bitA _ h1 h2
    · left
      simp only [Ab0]
      rw [dite_eq_right_of_eq_false (eq_false h)]
  · intro x
    have e : (x + (g : ℤ)) % (g : ℤ) = x % (g : ℤ) := by simp
    change Ab0 ((x + (g : ℤ)) % (g : ℤ)) = Ab0 (x % (g : ℤ))
    rw [e]
  · intro x
    simp only [Bb]
    have : (x + (g : ℤ) - 1) % (g : ℤ) = (x - 1) % (g : ℤ) := by
      rw [show x + (g : ℤ) - 1 = (x - 1) + g by ring]; simp
    rw [this]
  · intro x hx1 hx2 hsim
    have hex : ∃ y : ℤ, 1 ≤ y ∧ y ≤ (N : ℤ) - 1 ∧ y % (g : ℤ) = x % (g : ℤ) ∧
        ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ y := ⟨x, hx1, hx2, rfl, hsim⟩
    change A x = Ab0 (x % (g : ℤ))
    simp only [Ab0, hex, dite_true]
    obtain ⟨h1, h2, h3, h4⟩ := hex.choose_spec
    exact P.generic_eq ⟨hx1, hx2⟩ ⟨h1, h2⟩ (PeriodWords.dvd_sub_of_emod_eq (by rw [h3])) hsim h4
  · intro x hx1 hx2
    simp only [Bb]
    have hB := P.perB
    have h1 : 1 ≤ (x - 1) % (g : ℤ) + 1 := by
      have := Int.emod_nonneg (x - 1) hgz.ne'; omega
    have h2 : (x - 1) % (g : ℤ) + 1 ≤ (N : ℤ) - 1 := by
      have := Int.emod_lt_of_pos (x - 1) hgz; omega
    refine mixFold_eq_of_gcd_dvd hg hB hx1 hx2 h1 h2 ?_
    have := Int.emod_def (x - 1) (g : ℤ)
    exact ⟨-((x - 1) / g), by linarith⟩

variable (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) {Ab Bb : ℤ → ℤ}

theorem Gen.dev_eq (hG : P.Gen Ab Bb) {y : ℤ} (h1 : 1 ≤ y) (h2 : y ≤ (N : ℤ) - 1) :
    mixFold_dev A B Ab Bb y = A y - Ab y := by
  unfold mixFold_dev
  rw [hG.B_eq y h1 h2]; ring

theorem Gen.dev_ne_zero_sim (hG : P.Gen Ab Bb) {y : ℤ} (h1 : 1 ≤ y) (h2 : y ≤ (N : ℤ) - 1)
    (h : mixFold_dev A B Ab Bb y ≠ 0) : mixFoldSim p Q s₁ t₁ s₂ t₂ y := by
  by_contra hs
  apply h
  rw [hG.dev_eq P h1 h2, hG.A_eq y h1 h2 hs]; ring

theorem Gen.Bb_mul (hG : P.Gen Ab Bb) (x : ℤ) (k : ℕ) : Bb (x + k * (Nat.gcd p Q : ℕ)) = Bb x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : x + ((k + 1 : ℕ) : ℤ) * ((Nat.gcd p Q : ℕ) : ℤ) =
        (x + (k : ℤ) * ((Nat.gcd p Q : ℕ) : ℤ)) + ((Nat.gcd p Q : ℕ) : ℤ) := by push_cast; ring
    rw [e, hG.Bb_per, ih]

theorem Gen.Ab_mul (hG : P.Gen Ab Bb) (x : ℤ) (k : ℕ) : Ab (x + k * (Nat.gcd p Q : ℕ)) = Ab x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : x + ((k + 1 : ℕ) : ℤ) * ((Nat.gcd p Q : ℕ) : ℤ) =
        (x + (k : ℤ) * ((Nat.gcd p Q : ℕ) : ℤ)) + ((Nat.gcd p Q : ℕ) : ℤ) := by push_cast; ring
    rw [e, hG.Ab_per, ih]

theorem Gen.symm (hG : P.Gen Ab Bb) : P.symm.Gen Ab Bb := by
  have e : Nat.gcd Q p = Nat.gcd p Q := Nat.gcd_comm Q p
  refine ⟨hG.Ab_bit, ?_, ?_, ?_, hG.B_eq⟩
  · intro x; rw [e]; exact hG.Ab_per x
  · intro x; rw [e]; exact hG.Bb_per x
  · intro x h1 h2 hs
    exact hG.A_eq x h1 h2 (fun h => hs ⟨h.2, h.1⟩)

end MixFoldPair

end SkewGluing
