/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MixedFold/Facts.lean`. -/
import GluingCore.MixedFold.Heights

/-!
# The word data of the period-`g` root

Formalizes `shields-2026-skew-factor-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`: `eq:gluing-mixed-phases`, the pinches, and the generic words).

`MixFoldFold A B N g M v α β` is what the parent's bit words satisfy once the two case-(d) charts
are folded to period `g`: `N = M g + v` with `0 < v < g`, `M ≥ 2`; the exceptional classes are
`α < β ≤ v` (modulo `g`), `B` has period `g`, `A` has period `g` outside the classes `α`, `β`;
the caps `A_α = 1`, `A_β = 1`, `A_{M g + α} = 0`, `A_{M g + β} = 0`; `B_v = 1`, `B_g = 0`;
the heights `H_v = H_{g-1} = H_{N-g} = 1`; the block relation
`H_{g+v} = H_v + A_{g+α} + A_{g+β} - 1`; and `A_{M g} = 1` when `α ≥ 1`, `A_v = 0` when `β < v`.
`mixFold_fold_facts` proves it for the words of a pair of charts.

Sorry-free.
-/

namespace GluingCore

open PeriodWords

/-- The word data of the folded root. -/
structure MixFoldFold (A B : ℤ → ℤ) (N g M v : ℕ) (α β : ℤ) : Prop where
  hN : N = M * g + v
  hv0 : 0 < v
  hvg : v < g
  hM : 2 ≤ M
  hα : 0 ≤ α
  hαβ : α < β
  hβv : β ≤ v
  perB : PeriodWords.PeriodExcept (N - 1) g ∅ B
  perA : ∀ x : ℤ, 1 ≤ x → x + g ≤ (N : ℤ) - 1 → x % (g : ℤ) ≠ α → x % (g : ℤ) ≠ β →
    A x = A (x + g)
  capα : 1 ≤ α → A α = 1
  capβ : A β = 1
  termα : A ((M : ℤ) * g + α) = 0
  termβ : β < v → A ((M : ℤ) * g + β) = 0
  Bv : B v = 1
  Bg : B g = 0
  Hv : mixFold_ht A B v = 1
  Hg : mixFold_ht A B (g - 1) = 1
  HNg : mixFold_ht A B (N - g) = 1
  block : mixFold_ht A B (g + v) = mixFold_ht A B v + (A ((g : ℤ) + α) + A ((g : ℤ) + β) - 1)
  Amg : 1 ≤ α → A ((M : ℤ) * g) = 1
  Av : β < v → A v = 0

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}
  {P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂} {Ab Bb : ℤ → ℤ} {a b r M v : ℕ}

theorem nonsim_of_class (hg : Nat.gcd p Q ∣ p) {y : ℤ}
    (h1 : y % ((Nat.gcd p Q : ℕ) : ℤ) ≠ t₁ % ((Nat.gcd p Q : ℕ) : ℤ))
    (h2 : y % ((Nat.gcd p Q : ℕ) : ℤ) ≠ s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) :
    ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ y := by
  intro hs
  have := hs.1
  have e : (y % (p : ℤ)) % ((Nat.gcd p Q : ℕ) : ℤ) = y % ((Nat.gcd p Q : ℕ) : ℤ) :=
    Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 hg)
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · rw [h] at e; exact h1 e.symm
  · rw [h] at e; exact h2 e.symm

theorem class_of_sim (hg : Nat.gcd p Q ∣ p) {y : ℤ} (hs : mixFoldSim p Q s₁ t₁ s₂ t₂ y) :
    y % ((Nat.gcd p Q : ℕ) : ℤ) = t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ∨
      y % ((Nat.gcd p Q : ℕ) : ℤ) = s₁ % ((Nat.gcd p Q : ℕ) : ℤ) := by
  by_contra h
  push Not at h
  exact nonsim_of_class hg h.1 h.2 hs

theorem Gen.block_phases (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v)
    (hnc : t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ≠ s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) :
    mixFold_ht A B (Nat.gcd p Q + v) = mixFold_ht A B v +
      (A ((Nat.gcd p Q : ℕ) + t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) +
        A ((Nat.gcd p Q : ℕ) + s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) - 1) := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  have hvg := hA.hvg
  have hN := P.c₁.two_q_add_w_le
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hg := P.g_pos
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  have hcl_t := (slotOK_t P).class_le hG hA
  have hcl_s := (slotOK_s P).class_le hG hA
  have hMge : 2 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hMg : (2 : ℤ) * (Nat.gcd p Q : ℕ) ≤ (M : ℤ) * (Nat.gcd p Q : ℕ) := by
    have : (2 : ℤ) ≤ M := by exact_mod_cast hMge
    nlinarith
  have hρt0 := Int.emod_nonneg t₁ (show ((Nat.gcd p Q : ℕ) : ℤ) ≠ 0 by omega)
  have hρs0 := Int.emod_nonneg s₁ (show ((Nat.gcd p Q : ℕ) : ℤ) ≠ 0 by omega)
  have hsplit := mixFold_devSum_add' A B Ab Bb v (Nat.gcd p Q)
  have hg1 := mixFold_gen_ht_add (Ab := Ab) (Bb := Bb) (g := Nat.gcd p Q) hG.Ab_per hG.Bb_per v
  rw [hΔ] at hg1
  have uniq : ∀ y ρ : ℤ, y % ((Nat.gcd p Q : ℕ) : ℤ) = ρ → 0 ≤ ρ → ρ ≤ v → (v : ℤ) + 1 ≤ y →
      y ≤ (v : ℤ) + (Nat.gcd p Q : ℕ) → y = (Nat.gcd p Q : ℕ) + ρ := by
    intro y ρ hy hρ0 hρv h1 h2
    have hd : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - (((Nat.gcd p Q : ℕ) : ℤ) + ρ) := by
      have e1 : (((Nat.gcd p Q : ℕ) : ℤ) + ρ) % ((Nat.gcd p Q : ℕ) : ℤ) = ρ := by
        rw [Int.add_emod, Int.emod_self, zero_add, Int.emod_emod_of_dvd _ dvd_rfl,
          Int.emod_eq_of_lt hρ0 (by omega)]
      exact PeriodWords.dvd_sub_of_emod_eq (by rw [hy, e1])
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  have hW := mixFold_winSum_pair A B Ab Bb v (Nat.gcd p Q)
    ((Nat.gcd p Q : ℕ) + t₁ % ((Nat.gcd p Q : ℕ) : ℤ))
    ((Nat.gcd p Q : ℕ) + s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun y hy1 hy2 hne1 hne2 => by
      by_contra h
      have hs := hG.dev_ne_zero_sim P (by omega) (by omega) h
      rcases class_of_sim (Nat.gcd_dvd_left p Q) hs with h' | h'
      · exact hne1 (uniq y _ h' hρt0 hcl_t hy1 hy2)
      · exact hne2 (uniq y _ h' hρs0 hcl_s hy1 hy2))
  rw [hG.dev_eq P (by omega) (by omega), hG.dev_eq P (by omega) (by omega)] at hW
  have hq1 : Ab ((Nat.gcd p Q : ℕ) + t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) = Ab t₁ := by
    rw [add_comm, hG.Ab_per, hG.Ab_mod]
  have hq2 : Ab ((Nat.gcd p Q : ℕ) + s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) = Ab s₁ := by
    rw [add_comm, hG.Ab_per, hG.Ab_mod]
  rw [hq1, hq2] at hW
  have hsum := hG.Ab_phase_sum hA
  have e : v + Nat.gcd p Q = Nat.gcd p Q + v := by ring
  rw [mixFold_ht_eq_add_dev A B Ab Bb (Nat.gcd p Q + v), mixFold_ht_eq_add_dev A B Ab Bb v,
    ← e, hg1]
  rw [e] at hsplit
  rw [← e] at hsplit
  linarith

theorem Arith.w1_mod (hA : P.Arith a b r M v) :
    (w₁ : ℤ) % ((Nat.gcd p Q : ℕ) : ℤ) = v := by
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  have hvg := hA.hvg
  rw [cw, show (b : ℤ) * (Nat.gcd p Q : ℕ) + v = (v : ℤ) + (b : ℤ) * (Nat.gcd p Q : ℕ) by ring,
    Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]

theorem SlotOK.caps (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {x : ℤ} (hx : P.SlotOK x)
    (hnc : t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ≠ s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) :
    (1 ≤ x % ((Nat.gcd p Q : ℕ) : ℤ) → A (x % ((Nat.gcd p Q : ℕ) : ℤ)) = 1) ∧
      (x % ((Nat.gcd p Q : ℕ) : ℤ) < v →
        A ((M : ℤ) * (Nat.gcd p Q : ℕ) + x % ((Nat.gcd p Q : ℕ) : ℤ)) = 0) := by
  refine ⟨fun h => hx.init_cap hG hA hnc h, fun h => ?_⟩
  have hxw : x < w₁ := by
    obtain ⟨hx0, hx1, -⟩ := hx
    by_contra hcon
    have : x = w₁ := by omega
    rw [this, hA.w1_mod] at h
    omega
  exact hx.term_cap hG hA hnc hxw h

theorem Gen.fold_facts (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    ∃ α β : ℤ, MixFoldFold A B N (Nat.gcd p Q) M v α β := by
  obtain ⟨hΔ, hI, -⟩ := hG.drift
  have hnc := P.noncollide.1
  have hg := P.g_pos
  have hvg := hA.hvg
  have hN := P.c₁.two_q_add_w_le
  have hgz : (0 : ℤ) < ((Nat.gcd p Q : ℕ) : ℤ) := by exact_mod_cast hg
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  have hMge : 2 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hcl_t := (slotOK_t P).class_le hG hA
  have hcl_s := (slotOK_s P).class_le hG hA
  have hρt0 := Int.emod_nonneg t₁ hgz.ne'
  have hρs0 := Int.emod_nonneg s₁ hgz.ne'
  have ct := (slotOK_t P).caps hG hA hnc
  have cs := (slotOK_s P).caps hG hA hnc
  have hsum := hG.Ab_phase_sum hA
  have hMg : (2 : ℤ) * (Nat.gcd p Q : ℕ) ≤ (M : ℤ) * (Nat.gcd p Q : ℕ) := by
    have : (2 : ℤ) ≤ M := by exact_mod_cast hMge
    nlinarith
  have hNv : (v : ℤ) + 1 ≤ (N : ℤ) - 1 := by omega
  refine ⟨min (t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)),
    max (t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)), ?_⟩
  have hcases : (min (t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) =
      t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ∧ max (t₁ % ((Nat.gcd p Q : ℕ) : ℤ))
      (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) = s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) ∨
      (min (t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) =
      s₁ % ((Nat.gcd p Q : ℕ) : ℤ) ∧ max (t₁ % ((Nat.gcd p Q : ℕ) : ℤ))
      (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) = t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) := by
    rcases le_total (t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (s₁ % ((Nat.gcd p Q : ℕ) : ℤ))
      with h | h
    · exact Or.inl ⟨min_eq_left h, max_eq_right h⟩
    · exact Or.inr ⟨min_eq_right h, max_eq_left h⟩
  set α := min (t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) with hα
  set β := max (t₁ % ((Nat.gcd p Q : ℕ) : ℤ)) (s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) with hβ
  have hαβ : α < β := lt_of_le_of_ne (min_le_max) (by
    intro h
    apply hnc
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  have hαmem : α = t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ∨ α = s₁ % ((Nat.gcd p Q : ℕ) : ℤ) := by
    rcases hcases with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hβmem : β = t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ∨ β = s₁ % ((Nat.gcd p Q : ℕ) : ℤ) := by
    rcases hcases with ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp [h2]
  have hβv : β ≤ v := by rcases hβmem with h | h <;> omega
  have hα0 : 0 ≤ α := by rcases hαmem with h | h <;> omega
  have hcap1 : ∀ ρ : ℤ, (ρ = t₁ % ((Nat.gcd p Q : ℕ) : ℤ) ∨ ρ = s₁ % ((Nat.gcd p Q : ℕ) : ℤ)) →
      (1 ≤ ρ → A ρ = 1) ∧ (ρ < v → A ((M : ℤ) * (Nat.gcd p Q : ℕ) + ρ) = 0) := by
    intro ρ hρ
    rcases hρ with rfl | rfl
    · exact ct
    · exact cs
  refine ⟨hA.hN, hA.hv0, hvg, hMge, hα0, hαβ, hβv, P.perB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro x hx1 hx2 hxα hxβ
    have hn1 : x % ((Nat.gcd p Q : ℕ) : ℤ) ≠ t₁ % ((Nat.gcd p Q : ℕ) : ℤ) := by
      intro h; rcases hcases with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
    have hn2 : x % ((Nat.gcd p Q : ℕ) : ℤ) ≠ s₁ % ((Nat.gcd p Q : ℕ) : ℤ) := by
      intro h; rcases hcases with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega
    have e : (x + ((Nat.gcd p Q : ℕ) : ℤ)) % ((Nat.gcd p Q : ℕ) : ℤ) =
        x % ((Nat.gcd p Q : ℕ) : ℤ) := by simp
    rw [hG.A_eq x hx1 (by omega) (nonsim_of_class (Nat.gcd_dvd_left p Q) hn1 hn2),
      hG.A_eq (x + (Nat.gcd p Q : ℕ)) (by omega) (by omega)
        (nonsim_of_class (Nat.gcd_dvd_left p Q) (by rw [e]; exact hn1) (by rw [e]; exact hn2)),
      hG.Ab_per]
  · intro h1; exact (hcap1 α hαmem).1 h1
  · exact (hcap1 β hβmem).1 (by omega)
  · exact (hcap1 α hαmem).2 (by omega)
  · intro h; exact (hcap1 β hβmem).2 h
  · rw [hG.B_eq v (by have := hA.hv0; omega) (by omega)]
    exact hG.Bb_v hA
  · have := hG.B_eq (Nat.gcd p Q : ℕ) (by omega) (by
      have := P.c₁.w_lt; have := hA.hp; have := hA.ha
      have : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
      omega)
    rw [this]; exact hG.Bb_g' hA
  · exact hG.ht_v hA
  · exact hG.ht_pred_g hA
  · exact hG.ht_Ng hA
  · have := hG.block_phases hA hnc
    rw [this]
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; ring
  · intro h1
    have hρt1 : 1 ≤ t₁ % ((Nat.gcd p Q : ℕ) : ℤ) := by rcases hαmem with h | h <;> omega
    have hρs1 : 1 ≤ s₁ % ((Nat.gcd p Q : ℕ) : ℤ) := by rcases hαmem with h | h <;> omega
    have ht1 : 1 ≤ t₁ := by
      by_contra hcon
      have : t₁ = 0 := by obtain ⟨_, hh⟩ := (slotOK_t P); omega
      rw [this] at hρt1; simp at hρt1
    have hAb : Ab (Nat.gcd p Q : ℕ) = 1 := by
      rw [← hI]; unfold initMass; simp only [ht1, ite_true]; omega
    have hns : ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ ((M : ℤ) * (Nat.gcd p Q : ℕ)) := by
      apply nonsim_of_class (Nat.gcd_dvd_left p Q)
      · rw [Int.mul_emod_left]; omega
      · rw [Int.mul_emod_left]; omega
    rw [hG.A_eq _ (by nlinarith) (by nlinarith) hns, ← hAb]
    apply hG.Ab_eq_of_dvd
    exact ⟨1 - (M : ℤ), by ring⟩
  · intro h1
    have hρt : t₁ % ((Nat.gcd p Q : ℕ) : ℤ) < v := by rcases hβmem with h | h <;> omega
    have hρs : s₁ % ((Nat.gcd p Q : ℕ) : ℤ) < v := by rcases hβmem with h | h <;> omega
    have hsw : s₁ < w₁ := by
      by_contra hcon
      have : s₁ = w₁ := by obtain ⟨_, _, hh⟩ := (slotOK_s P) ; omega
      rw [this, hA.w1_mod] at hρs; omega
    have htm := hG.term_mass hA
    simp only [hsw, ite_true] at htm
    have hAbv : Ab (v : ℤ) = 0 := by omega
    have hns : ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ (v : ℤ) := by
      apply nonsim_of_class (Nat.gcd_dvd_left p Q)
      · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
      · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
    rw [hG.A_eq _ (by omega) (by omega) hns, hAbv]

end MixFoldPair

/-- **The word data of the folded root.**  Two case-(d) charts of nondividing periods with positive
remainder modulo `g = gcd p Q` give the data `MixFoldFold` on the words of the parent. -/
theorem MixFoldPair.fold_facts {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}
    (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    ∃ M v : ℕ, ∃ α β : ℤ, MixFoldFold A B N (Nat.gcd p Q) M v α β := by
  obtain ⟨Ab, Bb, hG⟩ := P.exists_gen
  obtain ⟨a, b, r, M, v, hA⟩ := P.exists_arith
  obtain ⟨α, β, h⟩ := hG.fold_facts hA
  exact ⟨M, v, α, β, h⟩

end GluingCore
