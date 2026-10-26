import SkewGluing.MixedFold.Legal

/-!
# The period-`g` inner

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`: "construct `G` from the first and last `g` diagonals").

From the word data `MixFoldFold` of a parent, the inner `G = mixFoldInner A B g M v` is the
connected skew diagram whose words are those of the parent on the positions `1, …, v` and those of
its last window `(N - g, N - 1]` on `v + 1, …, g + v - 1`.  Its first `g - 1` words are those of
the parent (`MixFoldFold.first_words`), its heights are the parent's heights at the same positions
(`MixFoldFold.heightWord_first`) and at the last window (`MixFoldFold.heightWord_last`), and it
satisfies the diagonal data `MixFoldDiag` of a case-(d) mark of period `g`, width `v` and phases
`(β, α)` (`MixFoldFold.diag`).

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

/-- The first-row word of the inner: the parent's word on `1, …, v`, its last-window word beyond. -/
def mixFoldGA (A : ℤ → ℤ) (g M v : ℕ) : ℕ → ℤ := fun k =>
  if k ≤ v then A k else A (((M - 1) * g + k : ℕ) : ℤ)

/-- The last-row word of the inner. -/
def mixFoldGB (B : ℤ → ℤ) (g M v : ℕ) : ℕ → ℤ := fun k =>
  if k ≤ v then B k else B (((M - 1) * g + k : ℕ) : ℤ)

/-- The period-`g` inner of the folded root. -/
def mixFoldInner (A B : ℤ → ℤ) (g M v : ℕ) : Diagram :=
  fromBits (g + v) (mixFoldGA A g M v) (mixFoldGB B g M v)

namespace MixFoldFold

variable {A B : ℤ → ℤ} {N g M v : ℕ} {α β : ℤ}

theorem perA_iter (hF : MixFoldFold A B N g M v α β) : ∀ (j : ℕ) (x : ℤ), 1 ≤ x →
    x + j * g ≤ (N : ℤ) - 1 → x % (g : ℤ) ≠ α → x % (g : ℤ) ≠ β →
    A x = A (x + j * g) := by
  intro j
  induction j with
  | zero => intro x _ _ _ _; simp
  | succ j ih =>
    intro x h1 h2 h3 h4
    have hg : 0 < g := by have := hF.hv0; have := hF.hvg; omega
    have e : x + ((j + 1 : ℕ) : ℤ) * g = (x + j * g) + g := by push_cast; ring
    rw [e] at h2 ⊢
    have hm : (x + (j : ℤ) * g) % (g : ℤ) = x % (g : ℤ) := by
      rw [Int.add_emod, Int.mul_emod_left, add_zero, Int.emod_emod_of_dvd _ dvd_rfl]
    rw [ih x h1 (by omega) h3 h4]
    exact hF.perA (x + j * g) (by nlinarith) (by omega)
      (by rw [hm]; exact h3) (by rw [hm]; exact h4)

theorem perB_iter (hF : MixFoldFold A B N g M v α β) (j : ℕ) (x : ℤ) (h1 : 1 ≤ x)
    (h2 : x + j * g ≤ (N : ℤ) - 1) : B x = B (x + j * g) := by
  have hg : 0 < g := by have := hF.hv0; have := hF.hvg; omega
  have := hF.hM
  refine mixFold_eq_of_gcd_dvd hg hF.perB h1 (by nlinarith [Nat.zero_le (j * g)]) (by nlinarith)
    h2 ⟨j, by ring⟩

theorem first_words (hF : MixFoldFold A B N g M v α β) {k : ℕ} (h1 : 1 ≤ k) (h2 : k + 1 ≤ g) :
    mixFoldGA A g M v k = A k ∧ mixFoldGB B g M v k = B k := by
  have hM := hF.hM
  have hN := hF.hN
  have hv0 := hF.hv0
  have hvg := hF.hvg
  by_cases hk : k ≤ v
  · simp [mixFoldGA, mixFoldGB, hk]
  · have e : ((((M - 1) * g + k : ℕ)) : ℤ) = (k : ℤ) + ((M - 1 : ℕ) : ℤ) * g := by push_cast; ring
    have hle : (k : ℤ) + ((M - 1 : ℕ) : ℤ) * g ≤ (N : ℤ) - 1 := by
      have : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
      rw [this, hN]; push_cast; nlinarith
    refine ⟨?_, ?_⟩
    · simp only [mixFoldGA, hk, ite_false, e]
      have hαβ := hF.hαβ
      have hβv := hF.hβv
      have hcl : (k : ℤ) % (g : ℤ) = k := Int.emod_eq_of_lt (by omega) (by omega)
      exact (hF.perA_iter (M - 1) k (by omega) hle (by rw [hcl]; omega) (by rw [hcl]; omega)).symm
    · simp only [mixFoldGB, hk, ite_false, e]
      exact (hF.perB_iter (M - 1) k (by omega) hle).symm

theorem heightWord_first (hF : MixFoldFold A B N g M v α β) :
    ∀ k : ℕ, k + 1 ≤ g →
      heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) k = mixFold_ht A B k := by
  intro k
  induction k with
  | zero => intro _; simp [heightWord, mixFold_ht]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    rw [heightWord_succ, mixFold_ht_succ, h1]
    obtain ⟨e1, e2⟩ := hF.first_words (k := k + 1) (by omega) hk
    rw [e1, e2]
    push_cast
    ring

theorem heightWord_last (hF : MixFoldFold A B N g M v α β) :
    ∀ k : ℕ, v ≤ k → k + 1 ≤ g + v →
      heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) k =
        mixFold_ht A B ((M - 1) * g + k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    have hvg := hF.hvg
    rw [hF.heightWord_first v (by omega), hF.Hv]
    have : (M - 1) * g + v = N - g := by
      have := hF.hN; have := hF.hM
      have h2 : (M - 1) * g + g = M * g := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    rw [this, hF.HNg]
  | succ k hk ih =>
    intro hk2
    have h1 := ih (by omega)
    rw [heightWord_succ, h1]
    have e : (M - 1) * g + (k + 1) = ((M - 1) * g + k) + 1 := by ring
    rw [e, mixFold_ht_succ]
    simp only [mixFoldGA, mixFoldGB, show ¬ (k + 1 ≤ v) by omega, ite_false]
    rw [e]
    push_cast
    ring

theorem isBitData (hF : MixFoldFold A B N g M v α β)
    (hbd : IsBitData N (fun k : ℕ => A k) (fun k : ℕ => B k)) :
    IsBitData (g + v) (mixFoldGA A g M v) (mixFoldGB B g M v) := by
  obtain ⟨hN0, hbits, hpos, hlast⟩ := hbd
  have hM := hF.hM
  have hNN := hF.hN
  have hv0 := hF.hv0
  have hvg := hF.hvg
  have hMg : (M - 1) * g + g = M * g := by
    rw [← Nat.succ_mul]; congr 1; omega
  refine ⟨by omega, fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
  · by_cases hk : k ≤ v
    · simp only [mixFoldGA, mixFoldGB, hk, ite_true]
      exact hbits k hk1 (by omega)
    · simp only [mixFoldGA, mixFoldGB, hk, ite_false]
      exact hbits _ (by omega) (by omega)
  · by_cases hk1 : k + 1 ≤ g
    · rw [hF.heightWord_first k hk1]
      exact hpos k (by omega)
    · rw [hF.heightWord_last k (by omega) (by omega)]
      exact hpos _ (by omega)
  · have : g + v - 1 + 1 ≤ g + v := by omega
    rw [hF.heightWord_last (g + v - 1) (by omega) this]
    have e : (M - 1) * g + (g + v - 1) = N - 1 := by omega
    rw [e]
    exact hlast

theorem GB_per (hF : MixFoldFold A B N g M v α β) {m : ℕ} (h1 : 1 ≤ m) (h2 : m + 1 ≤ v) :
    mixFoldGB B g M v m = mixFoldGB B g M v (m + g) := by
  have hM := hF.hM
  have hNN := hF.hN
  have hvg := hF.hvg
  have e : (((M - 1) * g + (m + g) : ℕ) : ℤ) = (m : ℤ) + (M : ℤ) * g := by
    have : (M - 1) * g + g = M * g := by rw [← Nat.succ_mul]; congr 1; omega
    have h3 : (M - 1) * g + (m + g) = m + M * g := by omega
    rw [h3]; push_cast; ring
  simp only [mixFoldGB, show m ≤ v by omega, ite_true, show ¬ (m + g ≤ v) by omega, ite_false, e]
  have := hF.perB_iter M m (by omega) (by rw [hNN]; push_cast; nlinarith)
  exact this

theorem GA_per (hF : MixFoldFold A B N g M v α β) {m : ℕ} (h1 : 1 ≤ m) (h2 : m + 1 ≤ v)
    (hα : (m : ℤ) ≠ α) (hβ : (m : ℤ) ≠ β) :
    mixFoldGA A g M v m = mixFoldGA A g M v (m + g) := by
  have hM := hF.hM
  have hNN := hF.hN
  have hvg := hF.hvg
  have e : (((M - 1) * g + (m + g) : ℕ) : ℤ) = (m : ℤ) + (M : ℤ) * g := by
    have h3 : (M - 1) * g + (m + g) = m + M * g := by
      have : (M - 1) * g + g = M * g := by rw [← Nat.succ_mul]; congr 1; omega
      omega
    rw [h3]; push_cast; ring
  simp only [mixFoldGA, show m ≤ v by omega, ite_true, show ¬ (m + g ≤ v) by omega, ite_false, e]
  have hcl : (m : ℤ) % (g : ℤ) = m := Int.emod_eq_of_lt (by omega) (by omega)
  exact hF.perA_iter M m (by omega) (by rw [hNN]; push_cast; nlinarith) (by rw [hcl]; exact hα)
    (by rw [hcl]; exact hβ)

theorem GA_slots (hF : MixFoldFold A B N g M v α β) :
    (1 ≤ α → mixFoldGA A g M v α.toNat = 1) ∧ mixFoldGA A g M v β.toNat = 1 ∧
      mixFoldGA A g M v (g + α.toNat) = 0 ∧
      (β < v → mixFoldGA A g M v (g + β.toNat) = 0) ∧
      mixFoldGA A g M v g = (if 1 ≤ α then 1 else 0) ∧ mixFoldGB B g M v g = 0 ∧
      mixFoldGB B g M v v = 1 := by
  have hM := hF.hM
  have hNN := hF.hN
  have hvg := hF.hvg
  have hαβ := hF.hαβ
  have hβv := hF.hβv
  have hα0 := hF.hα
  have hMg : (M - 1) * g + g = M * g := by rw [← Nat.succ_mul]; congr 1; omega
  have hαn : ((α.toNat : ℕ) : ℤ) = α := Int.toNat_of_nonneg hα0
  have hβn : ((β.toNat : ℕ) : ℤ) = β := Int.toNat_of_nonneg (by omega)
  refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_, ?_, ?_, ?_⟩
  · simp only [mixFoldGA, show α.toNat ≤ v by omega, ite_true, hαn]
    exact hF.capα h1
  · simp only [mixFoldGA, show β.toNat ≤ v by omega, ite_true, hβn]
    exact hF.capβ
  · have e : (((M - 1) * g + (g + α.toNat) : ℕ) : ℤ) = (M : ℤ) * g + α := by
      have h3 : (M - 1) * g + (g + α.toNat) = M * g + α.toNat := by omega
      rw [h3]; push_cast; rw [hαn]
    simp only [mixFoldGA, show ¬ (g + α.toNat ≤ v) by omega, ite_false, e]
    exact hF.termα
  · have e : (((M - 1) * g + (g + β.toNat) : ℕ) : ℤ) = (M : ℤ) * g + β := by
      have h3 : (M - 1) * g + (g + β.toNat) = M * g + β.toNat := by omega
      rw [h3]; push_cast; rw [hβn]
    simp only [mixFoldGA, show ¬ (g + β.toNat ≤ v) by omega, ite_false, e]
    exact hF.termβ h1
  · have e : (((M - 1) * g + g : ℕ) : ℤ) = (M : ℤ) * g := by rw [hMg]; push_cast; ring
    simp only [mixFoldGA, show ¬ (g ≤ v) by omega, ite_false, e]
    by_cases h1 : 1 ≤ α
    · simp only [h1, ite_true]; exact hF.Amg h1
    · have : α = 0 := by omega
      simp only [h1, ite_false]
      have := hF.termα
      rw [‹α = 0›] at this
      simpa using this
  · have e : (((M - 1) * g + g : ℕ) : ℤ) = (M : ℤ) * g := by rw [hMg]; push_cast; ring
    simp only [mixFoldGB, show ¬ (g ≤ v) by omega, ite_false, e]
    have := hF.perB_iter (M - 1) g (by omega) (by rw [hNN]; push_cast; omega)
    rw [hF.Bg] at this
    have e2 : (g : ℤ) + ((M - 1 : ℕ) : ℤ) * g = (M : ℤ) * g := by
      have : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
      rw [this]; ring
    rw [e2] at this
    exact this.symm
  · simp only [mixFoldGB, le_refl, ite_true]
    exact hF.Bv

theorem bitsLo_se (hF : MixFoldFold A B N g M v α β) :
    ∀ n : ℕ, n + 1 ≤ v → bitsLo (mixFoldGB B g M v) (n + g) =
      bitsLo (mixFoldGB B g M v) n + bitsLo (mixFoldGB B g M v) g := by
  intro n
  induction n with
  | zero => intro _; simp [bitsLo]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have e : n + 1 + g = (n + g) + 1 := by ring
    rw [e, bitsLo_succ, bitsLo_succ, h1]
    have := hF.GB_per (m := n + 1) (by omega) hn
    rw [e] at this
    rw [← this]
    ring

/-- The heights of the inner at `g - 1`, `g`, `v`. -/
theorem heights_G (hF : MixFoldFold A B N g M v α β) :
    heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) v = 1 ∧
      heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) (g - 1) = 1 ∧
      heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) g = 1 + (if 1 ≤ α then 1 else 0) := by
  have hvg := hF.hvg
  have hv0 := hF.hv0
  obtain ⟨-, -, -, -, h5, h6, -⟩ := hF.GA_slots
  refine ⟨?_, ?_, ?_⟩
  · rw [hF.heightWord_first v (by omega)]; exact hF.Hv
  · rw [hF.heightWord_first (g - 1) (by omega)]; exact hF.Hg
  · have h1 : heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) (g - 1) = 1 := by
      rw [hF.heightWord_first (g - 1) (by omega)]; exact hF.Hg
    have := heightWord_succ (mixFoldGA A g M v) (mixFoldGB B g M v) (g - 1)
    have e2 : g - 1 + 1 = g := by omega
    rw [e2] at this
    rw [this, h1, h5, h6]; ring

theorem bitsLo_tails (hF : MixFoldFold A B N g M v α β) :
    ∀ n : ℕ, n + 1 ≤ v → bitsLo (mixFoldGA A g M v) (n + g) =
      bitsLo (mixFoldGA A g M v) n + bitsLo (mixFoldGB B g M v) g +
        (if (n : ℤ) < α then -1 else if (n : ℤ) < β then 0 else 1) := by
  intro n
  have hαβ := hF.hαβ
  have hβv := hF.hβv
  have hα0 := hF.hα
  have hvg := hF.hvg
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hF.GA_slots
  have hαn : ((α.toNat : ℕ) : ℤ) = α := Int.toNat_of_nonneg hα0
  have hβn : ((β.toNat : ℕ) : ℤ) = β := Int.toNat_of_nonneg (by omega)
  induction n with
  | zero =>
    intro _
    obtain ⟨-, -, hHg⟩ := hF.heights_G
    have hb := bitsLo_add_heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) g
    rw [hHg] at hb
    have hβ0 : (0 : ℤ) < β := by omega
    have hT : (if ((0 : ℕ) : ℤ) < α then -1 else if ((0 : ℕ) : ℤ) < β then 0 else 1) =
        -(if 1 ≤ α then 1 else 0 : ℤ) := by
      push_cast
      split_ifs <;> omega
    have hb0 : bitsLo (mixFoldGA A g M v) 0 = 0 := by simp [bitsLo]
    rw [zero_add, hT, hb0]
    linarith
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have e : n + 1 + g = (n + g) + 1 := by ring
    rw [e, bitsLo_succ, bitsLo_succ, h1]
    have hm : (n + 1 : ℕ) + 1 ≤ v + 1 := by omega
    by_cases hA : ((n + 1 : ℕ) : ℤ) = α
    · have hn1 : n + 1 = α.toNat := by omega
      have a1 := s1 (by omega)
      have a2 := s3
      rw [← hn1] at a1 a2
      have e2 : n + g + 1 = g + (n + 1) := by ring
      rw [e2, a2, a1]
      push_cast at hA ⊢
      have c1 : ¬ ((n : ℤ) + 1 < α) := by omega
      have c2 : (n : ℤ) < α := by omega
      have c3 : (n : ℤ) + 1 < β := by omega
      simp only [c1, c2, c3, ite_true, ite_false]
      ring
    · by_cases hB : ((n + 1 : ℕ) : ℤ) = β
      · have hn1 : n + 1 = β.toNat := by omega
        have a1 := s2
        have hbv : β < v := by omega
        have a2 := s4 hbv
        rw [← hn1] at a1 a2
        have e2 : n + g + 1 = g + (n + 1) := by ring
        rw [e2, a2, a1]
        push_cast at hB hA ⊢
        have c1 : ¬ ((n : ℤ) + 1 < α) := by omega
        have c2 : ¬ ((n : ℤ) < α) := by omega
        have c3 : ¬ ((n : ℤ) + 1 < β) := by omega
        have c4 : (n : ℤ) < β := by omega
        simp only [c1, c2, c3, c4, ite_true, ite_false]
        ring
      · have := hF.GA_per (m := n + 1) (by omega) hn hA hB
        have e2 : n + g + 1 = (n + 1) + g := by ring
        rw [e2, ← this]
        push_cast at hA hB ⊢
        have c1 : ((n : ℤ) + 1 < α) ↔ ((n : ℤ) < α) := by omega
        have c2 : ((n : ℤ) + 1 < β) ↔ ((n : ℤ) < β) := by omega
        simp only [c1, c2]
        ring

/-- **The diagonal data of the inner.**  The inner `G` has the diagonal data of a case-(d) mark of
period `g`, width `v`, phases `(s, t) = (β, α)` and row shift `Σ`-form `bitsLo GB g`. -/
theorem diag (hF : MixFoldFold A B N g M v α β)
    (hbd : IsBitData N (fun k : ℕ => A k) (fun k : ℕ => B k)) :
    MixFoldDiag (mixFoldInner A B g M v) g v (bitsLo (mixFoldGB B g M v) g) β α := by
  have hG := hF.isBitData hbd
  have hvg := hF.hvg
  have hv0 := hF.hv0
  have hαβ := hF.hαβ
  have hβv := hF.hβv
  have hα0 := hF.hα
  obtain ⟨hH1, hH2, hH3⟩ := hF.heights_G
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hF.GA_slots
  have hdlo : ∀ n : ℕ, n < g + v → diagLo (mixFoldInner A B g M v) n =
      bitsLo (mixFoldGA A g M v) n := fun n hn => diagLo_fromBits hG hn
  have hdhi : ∀ n : ℕ, n < g + v → diagHi (mixFoldInner A B g M v) n =
      bitsLo (mixFoldGB B g M v) n := fun n hn => diagHi_fromBits hG hn
  have hsing : ∀ n : ℕ, n < g + v →
      heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) n = 1 →
      diagLo (mixFoldInner A B g M v) n = diagHi (mixFoldInner A B g M v) n := by
    intro n hn hh
    rw [hdlo n hn, hdhi n hn]
    have := bitsLo_add_heightWord (mixFoldGA A g M v) (mixFoldGB B g M v) n
    rw [hh] at this
    linarith
  have hαn : ((α.toNat : ℕ) : ℤ) = α := Int.toNat_of_nonneg hα0
  have hβn : ((β.toNat : ℕ) : ℤ) = β := Int.toNat_of_nonneg (by omega)
  refine ⟨isConnectedSkew_fromBits hG, minContent_fromBits hG, ?_, by omega, hvg, hα0, hαβ, hβv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := span_fromBits hG
    unfold mixFoldInner
    rw [this]; push_cast; ring
  · intro a h0 h1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have e : (n : ℤ) + (g : ℤ) = ((n + g : ℕ) : ℤ) := by push_cast; ring
    rw [e, hdhi (n + g) (by omega), hdhi n (by omega)]
    exact hF.bitsLo_se n (by omega)
  · intro a h0 h1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have e : (n : ℤ) + (g : ℤ) = ((n + g : ℕ) : ℤ) := by push_cast; ring
    rw [e, hdlo (n + g) (by omega), hdlo n (by omega)]
    exact hF.bitsLo_tails n (by omega)
  · exact hsing v (by omega) hH1
  · have e : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ) := by omega
    rw [e]
    exact hsing (g - 1) (by omega) hH2
  · -- the cap `A_β = 1`
    have hn1 : 1 ≤ β.toNat := by omega
    have e1 : β - 1 = ((β.toNat - 1 : ℕ) : ℤ) := by omega
    have hb : diagLo (mixFoldInner A B g M v) β = bitsLo (mixFoldGA A g M v) β.toNat := by
      have := hdlo β.toNat (by omega); rwa [hβn] at this
    rw [hb, e1, hdlo (β.toNat - 1) (by omega)]
    have := bitsLo_succ (mixFoldGA A g M v) (β.toNat - 1)
    have e2 : β.toNat - 1 + 1 = β.toNat := by omega
    rw [e2] at this
    rw [this, s2]; ring
  · intro h0
    rw [h0] at *
    have e : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ) := by omega
    rw [e, hdhi (g - 1) (by omega), hdhi g (by omega)]
    have := bitsLo_succ (mixFoldGB B g M v) (g - 1)
    have e2 : g - 1 + 1 = g := by omega
    rw [e2] at this
    rw [this, s6]; ring
  · intro h1
    have hn1 : 1 ≤ α.toNat := by omega
    have e1 : (g : ℤ) + α - 1 = ((g + α.toNat - 1 : ℕ) : ℤ) := by omega
    have e2 : (g : ℤ) + α = ((g + α.toNat : ℕ) : ℤ) := by omega
    rw [e1, e2, hdlo (g + α.toNat - 1) (by omega), hdlo (g + α.toNat) (by omega)]
    have := bitsLo_succ (mixFoldGA A g M v) (g + α.toNat - 1)
    have e3 : g + α.toNat - 1 + 1 = g + α.toNat := by omega
    rw [e3] at this
    rw [this, s3]; ring

end MixFoldFold

end SkewGluing
