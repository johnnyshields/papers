import SkewGluing.MixedFold
import SkewGluing.OrdinaryDrift

/-!
# Heights of the folded marks of two case-(d) roots, exactly

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, `eq:gluing-mixed-phases`, `eq:gluing-mixed-heights`,
`eq:gluing-original-mixed-mark`).

In the setting of two case-(d) roots (`MixFoldPair`, generic words `Ab`, `Bb`, `MixFoldPair.Arith`),
let `z`, `o` be the phases of the first chart whose generic slot bits are zero and one.  This file
proves, on the words of the parent:

* the parent heights on the first `p` diagonals are the generic heights plus `1_{z ≥ 1, z ≤ n}`
  (`Gen.ht_first`) and, on the block after `M g`, the generic heights plus `1_{z ≥ 1}` minus the
  terminal deficit (`Gen.ht_last`);
* the concentration of the phases, `eq:gluing-mixed-phases` (`Gen.phases_exact`);
* the heights of the inner `G` on the lower and upper marked diagonals and the common retained
  heights `eq:gluing-mixed-heights` (`Gen.inner_heights`).

For the original chart, `mixFold_original_mark_heights` is `eq:gluing-original-mixed-mark`: the
heights of the lower mark `W₋` of the first root.

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}
  {P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂} {Ab Bb : ℤ → ℤ} {a b r M v : ℕ}

/-- The two phases of the first chart carry the generic slot bits zero and one:
`Ab z = 0`, `Ab o = 1`. -/
theorem Gen.exists_zero_one_phases (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    ∃ z o : ℤ, ((z = t₁ ∧ o = s₁) ∨ (z = s₁ ∧ o = t₁)) ∧ Ab z = 0 ∧ Ab o = 1 := by
  have hsum := hG.Ab_phase_sum hA
  rcases hG.Ab_bit t₁ with h1 | h1
  · exact ⟨t₁, s₁, Or.inl ⟨rfl, rfl⟩, h1, by omega⟩
  · exact ⟨s₁, t₁, Or.inr ⟨rfl, rfl⟩, by omega, h1⟩

/-- The deviation of the parent from the generic words on the first `p` diagonals sits at the two
phases. -/
theorem Gen.dev_first (hG : P.Gen Ab Bb) {y : ℤ} (h1 : 1 ≤ y) (h2 : y ≤ (p : ℤ) - 1) :
    mixFold_dev A B Ab Bb y =
      (if y = t₁ then 1 - Ab t₁ else 0) + (if y = s₁ then 1 - Ab s₁ else 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  by_cases ht : y = t₁
  · have hne : y ≠ s₁ := by omega
    rw [ht, hG.dev_t (by omega)]
    simp only [ht, ite_true] at hne ⊢
    have : t₁ ≠ s₁ := by omega
    simp [this]
  · by_cases hs : y = s₁
    · rw [hs, hG.dev_s]
      have : s₁ ≠ t₁ := by omega
      simp [this]
    · simp only [ht, hs, ite_false, add_zero]
      by_contra hne
      rcases hG.init_support h1 h2 hne with h | h
      · exact ht h
      · exact hs h

/-- The sum of the deviations over the first `n < p` positions. -/
theorem Gen.devSum_first (hG : P.Gen Ab Bb) {n : ℕ} (hn : (n : ℤ) ≤ (p : ℤ) - 1) :
    mixFold_devSum A B Ab Bb n =
      (if 1 ≤ t₁ ∧ t₁ ≤ (n : ℤ) then 1 - Ab t₁ else 0) +
        (if s₁ ≤ (n : ℤ) then 1 - Ab s₁ else 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  induction n with
  | zero =>
    have h1 : ¬ (1 ≤ t₁ ∧ t₁ ≤ ((0 : ℕ) : ℤ)) := by push_cast; omega
    have h2 : ¬ (s₁ ≤ ((0 : ℕ) : ℤ)) := by push_cast; omega
    rw [mixFold_devSum, Finset.range_zero, Finset.sum_empty,
      ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h2),
      add_zero]
  | succ n ih =>
    rw [mixFold_devSum_succ, ih (by omega), hG.dev_first (by omega) (by omega)]
    push_cast
    split_ifs <;> omega

/-- The parent heights on the first `p` diagonals: the generic heights plus `1_{z ≥ 1, z ≤ n}`,
where `z` is the phase whose generic slot bit is zero. -/
theorem Gen.ht_first (hG : P.Gen Ab Bb) {z o : ℤ}
    (hzo : (z = t₁ ∧ o = s₁) ∨ (z = s₁ ∧ o = t₁)) (hz : Ab z = 0) (ho : Ab o = 1) {n : ℕ}
    (hn : (n : ℤ) ≤ (p : ℤ) - 1) :
    mixFold_ht A B n = mixFold_ht Ab Bb n + (if 1 ≤ z ∧ z ≤ (n : ℤ) then 1 else 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hG.devSum_first hn]
  rcases hzo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> split_ifs <;> omega

/-- The deviation of the parent from the generic words on the last block: at the two terminal
positions `N - w₁ + t₁`, `N - w₁ + s₁`. -/
theorem Gen.dev_last (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {y : ℤ}
    (h1 : (M : ℤ) * ((Nat.gcd p Q : ℕ) : ℤ) ≤ y) (h2 : y ≤ (N : ℤ) - 1) :
    mixFold_dev A B Ab Bb y =
      (if y = (N : ℤ) - w₁ + t₁ then -Ab t₁ else 0) +
        (if y = (N : ℤ) - w₁ + s₁ then -Ab s₁ else 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  have hvg := hA.hvg
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hwp := P.c₁.w_lt
  have hgp' : ((Nat.gcd p Q : ℕ) : ℤ) ≤ (p : ℤ) := by exact_mod_cast hgp
  have hlow : (N : ℤ) - p < y := by omega
  by_cases ht : y = (N : ℤ) - w₁ + t₁
  · have hne : y ≠ (N : ℤ) - w₁ + s₁ := by omega
    rw [ht, hG.dev_et, hA.Ab_term hG t₁]
    have : (N : ℤ) - w₁ + t₁ ≠ (N : ℤ) - w₁ + s₁ := by omega
    simp [this]
  · by_cases hs : y = (N : ℤ) - w₁ + s₁
    · rw [hs, hG.dev_es (by omega), hA.Ab_term hG s₁]
      have : (N : ℤ) - w₁ + s₁ ≠ (N : ℤ) - w₁ + t₁ := by omega
      simp [this]
    · simp only [ht, hs, ite_false, add_zero]
      by_contra hne
      rcases hG.term_support hA hlow h2 hne with h | h
      · exact ht h
      · exact hs h

/-- `devSum (N - p) = Ab_g`: the first singleton height at `N - p` and zero drift. -/
theorem Gen.devSum_Np (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) :
    mixFold_devSum A B Ab Bb (N - p) = Ab (Nat.gcd p Q : ℕ) := by
  have h2 := P.x₁.single_Nq
  rw [mixFold_ht_eq_add_dev A B Ab Bb, hG.ht_gen_Np hA] at h2
  linarith

/-- The deviation sum up to `M g - 1 + k`, `k ≤ v`, is `Ab_g` minus the terminal deficits at the
positions `M g, …, M g + k - 1`. -/
theorem Gen.devSum_last (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {k : ℕ} (hk : k ≤ v) :
    mixFold_devSum A B Ab Bb (M * Nat.gcd p Q - 1 + k) =
      Ab (Nat.gcd p Q : ℕ) -
        (if 0 ≤ t₁ - b * (Nat.gcd p Q : ℕ) ∧ t₁ - b * (Nat.gcd p Q : ℕ) ≤ (k : ℤ) - 1
          then Ab t₁ else 0) -
        (if 0 ≤ s₁ - b * (Nat.gcd p Q : ℕ) ∧ s₁ - b * (Nat.gcd p Q : ℕ) ≤ (k : ℤ) - 1
          then Ab s₁ else 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  have hvg := hA.hvg
  have hg := P.g_pos
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hMg : 1 ≤ M * Nat.gcd p Q := by nlinarith
  have hMgz : ((M * Nat.gcd p Q - 1 : ℕ) : ℤ) = (M : ℤ) * (Nat.gcd p Q : ℕ) - 1 := by
    push_cast [Nat.cast_sub hMg]; ring
  have hNMg : M * Nat.gcd p Q + v = N := hA.hN.symm
  have hpN : p ≤ N := by have := P.c₁.two_q_add_w_le; omega
  induction k with
  | zero =>
    have hle : N - p ≤ M * Nat.gcd p Q - 1 := by omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
    rw [add_zero, hj, mixFold_devSum_add', hG.devSum_Np hA,
      mixFold_winSum_zero A B Ab Bb _ _ (fun y hy1 hy2 => ?_)]
    · push_cast
      split_ifs <;> omega
    · apply hG.term_conf hA y
      · have : ((N - p : ℕ) : ℤ) = (N : ℤ) - p := Nat.cast_sub hpN
        omega
      · have : ((N - p : ℕ) : ℤ) + (j : ℤ) = ((M * Nat.gcd p Q - 1 : ℕ) : ℤ) := by
          rw [hj]; push_cast; ring
        omega
  | succ k ih =>
    have e : M * Nat.gcd p Q - 1 + (k + 1) = (M * Nat.gcd p Q - 1 + k) + 1 := by ring
    rw [e, mixFold_devSum_succ, ih (by omega)]
    have hy : (((M * Nat.gcd p Q - 1 + k : ℕ) : ℤ) + 1) = (M : ℤ) * (Nat.gcd p Q : ℕ) + k := by
      push_cast [Nat.cast_sub hMg]; ring
    rw [hy, hG.dev_last hA (by omega) (by omega)]
    have hNw : (N : ℤ) - w₁ = (M : ℤ) * (Nat.gcd p Q : ℕ) - b * (Nat.gcd p Q : ℕ) := by
      rw [cN, cw]; ring
    push_cast
    split_ifs <;> omega

/-- The initial mass is `1_{z ≥ 1}`: `Ab_g = C_0 = 1_{τ > 0}`. -/
theorem Gen.Ab_g_eq (hG : P.Gen Ab Bb) {z o : ℤ}
    (hzo : (z = t₁ ∧ o = s₁) ∨ (z = s₁ ∧ o = t₁)) (hz : Ab z = 0) (ho : Ab o = 1) :
    Ab (Nat.gcd p Q : ℕ) = if 1 ≤ z then 1 else 0 := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  have h := hG.drift.2.1
  unfold initMass at h
  rw [← h]
  rcases hzo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> split_ifs <;> omega

/-- **The parent heights on the last block.**  For `0 ≤ k < w_g`, the height at `M g + k` is the
generic height plus `1_{z ≥ 1}` minus the terminal deficit at the position `o - b g`. -/
theorem Gen.ht_last (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {z o : ℤ}
    (hzo : (z = t₁ ∧ o = s₁) ∨ (z = s₁ ∧ o = t₁)) (hz : Ab z = 0) (ho : Ab o = 1) {k : ℕ}
    (hk : k < v) :
    mixFold_ht A B (M * Nat.gcd p Q + k) = mixFold_ht Ab Bb k + (if 1 ≤ z then 1 else 0) -
      (if 0 ≤ o - b * (Nat.gcd p Q : ℕ) ∧ o - b * (Nat.gcd p Q : ℕ) ≤ (k : ℤ) then 1 else 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  have hg := P.g_pos
  have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hMg : 1 ≤ M * Nat.gcd p Q := by nlinarith
  have e : M * Nat.gcd p Q + k = (M * Nat.gcd p Q - 1 + (k + 1)) := by omega
  rw [e, mixFold_ht_eq_add_dev A B Ab Bb, hG.devSum_last hA (by omega)]
  have e2 : M * Nat.gcd p Q - 1 + (k + 1) = k + M * Nat.gcd p Q := by omega
  rw [e2, mixFold_gen_ht_mul hG.Ab_per hG.Bb_per, hG.drift.1, hG.Ab_g_eq hzo hz ho]
  push_cast
  rcases hzo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> split_ifs <;> omega

/-- **`eq:gluing-mixed-phases`, exactly.**  With `z`, `o` the phases whose generic slot bits are
zero and one, `τ = z` and `σ = o - b g`, `C_j = Ab_j - Bb_j`:
`0 ≤ τ ≤ w_g`, `0 ≤ σ ≤ w_g`, `τ ≠ σ` (so `α = min (τ, σ) < β = max (τ, σ)`, hence
`0 ≤ α < β ≤ w_g`), `C_0 = 1_{τ > 0}` and `-C_{w_g} = 1_{σ < w_g}`. -/
theorem Gen.phases_exact (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {z o : ℤ}
    (hzo : (z = t₁ ∧ o = s₁) ∨ (z = s₁ ∧ o = t₁)) (hz : Ab z = 0) (ho : Ab o = 1) :
    0 ≤ z ∧ z ≤ v ∧ (b : ℤ) * (Nat.gcd p Q : ℕ) ≤ o ∧ o ≤ (b : ℤ) * (Nat.gcd p Q : ℕ) + v ∧
      z ≠ o - (b : ℤ) * (Nat.gcd p Q : ℕ) ∧
      Ab 0 - Bb 0 = (if 0 < z then 1 else 0) ∧
      Bb (v : ℤ) - Ab (v : ℤ) = (if o - (b : ℤ) * (Nat.gcd p Q : ℕ) < v then 1 else 0) := by
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := P.c₁.phases P.w₁_pos
  have hlt := hts (Or.inr rfl)
  obtain ⟨cN, cw, cp⟩ := hA.cast_facts
  have hvg := hA.hvg
  have hg := P.g_pos
  have hgz : (0 : ℤ) < ((Nat.gcd p Q : ℕ) : ℤ) := by exact_mod_cast hg
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  have hgp' : ((Nat.gcd p Q : ℕ) : ℤ) ≤ (p : ℤ) := by exact_mod_cast hgp
  have hwp := P.c₁.w_lt
  have hN := P.c₁.two_q_add_w_le
  have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hMge : 2 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
  have hMgz : (2 : ℤ) * (Nat.gcd p Q : ℕ) ≤ (M : ℤ) * (Nat.gcd p Q : ℕ) := by
    have : (2 : ℤ) ≤ M := by exact_mod_cast hMge
    nlinarith
  have hzmem : z = t₁ ∨ z = s₁ := by rcases hzo with h | h <;> omega
  have homem : o = t₁ ∨ o = s₁ := by rcases hzo with h | h <;> omega
  -- the initial deviation at `z` forces `z ≤ w_g`
  have hz0 : 0 ≤ z := by omega
  have hzv : z ≤ v := by
    by_contra hcon
    have h1 : 1 ≤ z := by omega
    have hdev : mixFold_dev A B Ab Bb z = 1 := by
      rcases hzmem with rfl | rfl
      · rw [hG.dev_t h1, hz]; ring
      · rw [hG.dev_s, hz]; ring
    have := hG.init_conf hA z (by omega) (by omega)
    omega
  -- the terminal deviation at `o` forces `o ≥ b g`
  have hobg : (b : ℤ) * (Nat.gcd p Q : ℕ) ≤ o := by
    by_cases hlt' : o < w₁
    · by_contra hcon
      have hdev : mixFold_dev A B Ab Bb ((N : ℤ) - w₁ + o) = -1 := by
        rcases homem with rfl | rfl
        · rw [hG.dev_et, hA.Ab_term hG, ho]
        · rw [hG.dev_es hlt', hA.Ab_term hG, ho]
      have := hG.term_conf hA ((N : ℤ) - w₁ + o) (by omega) (by omega)
      omega
    · have : o = w₁ := by omega
      omega
  have hov : o ≤ (b : ℤ) * (Nat.gcd p Q : ℕ) + v := by omega
  refine ⟨hz0, hzv, hobg, hov, ?_, ?_, ?_⟩
  · intro hzs
    have hnc := P.noncollide.1
    have hzmod : z % ((Nat.gcd p Q : ℕ) : ℤ) = z := Int.emod_eq_of_lt hz0 (by omega)
    have homod : o % ((Nat.gcd p Q : ℕ) : ℤ) = o - (b : ℤ) * (Nat.gcd p Q : ℕ) := by
      have e : o = (o - (b : ℤ) * (Nat.gcd p Q : ℕ)) + (b : ℤ) * (Nat.gcd p Q : ℕ) := by ring
      conv_lhs => rw [e]
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
    apply hnc
    rcases hzo with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2, hzmod, homod, hzs]
    · rw [← h1, ← h2, hzmod, homod, hzs]
  · have h1 := hG.Ab_per 0
    have h2 := hG.Bb_g' hA
    have h3 := hG.Bb_per 0
    simp only [zero_add] at h1 h3
    rw [← h1, ← h3, h2, hG.Ab_g_eq hzo hz ho]
    split_ifs <;> omega
  · have hBv := hG.Bb_v hA
    have htm := hG.term_mass hA
    rw [hBv]
    rcases hzo with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hz <;> rw [h2] at ho ⊢ <;>
      split_ifs at htm ⊢ <;> omega

/-- **`eq:gluing-mixed-heights`, exactly.**  Let `G` be the period-`g` inner of the fold
(`mixFoldInner`), `τ = z`, `σ = o - b g`, `α = min (τ, σ)`, `β = max (τ, σ)`, and
`H⁰_k = mixFold_ht Ab Bb k` the generic heights.  For `0 ≤ k < w_g`, the heights of the lower and
the upper marked diagonal of `G` before deletion are
`L_k = H⁰_k + 1_{τ>0, k≥τ}` and `U_k = H⁰_k + 1_{τ>0} - 1_{σ<w_g, k≥σ}`, and the retained heights
agree:
`L_k - 1_{k≥β} = U_k - 1_{k<α} = H⁰_k + 1_{τ>0, k≥τ} - 1_{k≥σ}` if `τ < σ`, and `H⁰_k` if
`τ > σ`.  The heights are read as `heightWord` of the words of `G`.

**Differs from the paper's route.**  The retained heights are stated as the heights of `G` minus
the indicators of the deleted cells, not as the heights of the retained cell sets, because the
mark of the Lean construction is the full intersection `G ∩ (G - v)`. -/
theorem Gen.inner_heights (hG : P.Gen Ab Bb) (hA : P.Arith a b r M v) {z o : ℤ}
    (hzo : (z = t₁ ∧ o = s₁) ∨ (z = s₁ ∧ o = t₁)) (hz : Ab z = 0) (ho : Ab o = 1) {k : ℕ}
    (hk : k < v) :
    let τ := z
    let σ := o - (b : ℤ) * (Nat.gcd p Q : ℕ)
    let α := min τ σ
    let β := max τ σ
    let H0 := mixFold_ht Ab Bb k
    let L := heightWord (mixFoldGA A (Nat.gcd p Q) M v) (mixFoldGB B (Nat.gcd p Q) M v) k
    let U := heightWord (mixFoldGA A (Nat.gcd p Q) M v) (mixFoldGB B (Nat.gcd p Q) M v)
      (Nat.gcd p Q + k)
    L = H0 + (if 0 < τ ∧ τ ≤ (k : ℤ) then 1 else 0) ∧
    U = H0 + (if 0 < τ then 1 else 0) - (if σ < v ∧ σ ≤ (k : ℤ) then 1 else 0) ∧
    L - (if β ≤ (k : ℤ) then 1 else 0) = U - (if (k : ℤ) < α then 1 else 0) ∧
    L - (if β ≤ (k : ℤ) then 1 else 0) =
      (if τ < σ then H0 + (if 0 < τ ∧ τ ≤ (k : ℤ) then 1 else 0) - (if σ ≤ (k : ℤ) then 1 else 0)
        else H0) := by
  intro τ σ α β H0 L U
  obtain ⟨α', β', hF⟩ := hG.fold_facts hA
  have hvg := hA.hvg
  have hgp : Nat.gcd p Q ≤ p := Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left p Q)
  obtain ⟨hz0, hzv, hobg, hov, hne, -, -⟩ := hG.phases_exact hA hzo hz ho
  have hL : L = mixFold_ht A B k := hF.heightWord_first k (by omega)
  have hU : U = mixFold_ht A B (M * Nat.gcd p Q + k) := by
    have := hF.heightWord_last (Nat.gcd p Q + k) (by omega) (by omega)
    have hM1 : 1 ≤ M := by have := hA.hM; have := hA.hr; have := hA.ha; nlinarith
    have e : (M - 1) * Nat.gcd p Q + (Nat.gcd p Q + k) = M * Nat.gcd p Q + k := by
      have : (M - 1) * Nat.gcd p Q + Nat.gcd p Q = M * Nat.gcd p Q := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    rw [e] at this
    exact this
  have h1 := hG.ht_first hzo hz ho (n := k) (by omega)
  have h2 := hG.ht_last hA hzo hz ho hk
  rw [hL, h1] at *
  rw [hU, h2] at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [α, β, σ, τ] at * <;>
    split_ifs <;> omega

end MixFoldPair

namespace Chart

/-- **The parent heights on the first band, case (d).**  For a proper legal chart of case (d)
with a nonempty mark and phases `s`, `t`, the height of the parent at the content `z < w` is the
height of the lower mark `W₋` plus one from the residue `s` on. -/
theorem IsProperLegal.mixFold_ht_first_band {χ : Chart} {F : Diagram} (h : χ.IsProperLegal)
    (hF : χ.IsChartOf F) (hd : χ.ω.case = .d) (hW : χ.ω.W.Nonempty) {s t : ℤ}
    (hph : χ.ω.IsPhases s t) (z : ℕ) (hz : z < χ.ω.width) :
    mixFold_ht (wordA F) (wordB F) z =
      height χ.ω.W (minContent χ.ω.E + z) + (if s ≤ (z : ℤ) then 1 else 0) := by
  obtain ⟨t0, rfl⟩ := hF
  have hl : χ.ω.IsLegalNonempty := ⟨h.2.2.2, hW⟩
  have hD := h.1
  have hP : IsConnectedSkew (χ.ω.compose χ.D) := h.2.2.2.isConnectedSkew_compose hD
  have hD2 := two_le_span_of_two_le_card h.1 h.2.1
  have hspan := hl.span_compose_nat hD
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have hlt := hl.phases_lt (Or.inr hd) hph
  have hqn : (χ.ω.period.toNat : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by omega)
  have hwz : χ.ω.widthZ = (χ.ω.width : ℤ) := rfl
  have hzs : z < span (χ.ω.compose χ.D) := by
    have := Nat.mul_le_mul_right χ.ω.period.toNat hD2
    omega
  have hmM : minContent χ.D ≤ maxContent χ.D := minContent_le (maxContent_mem hD.2.1)
  change mixFold_ht (wordA (translate t0 (χ.ω.compose χ.D)))
      (wordB (translate t0 (χ.ω.compose χ.D))) z = _
  rw [mixFold_ht_congr (A' := wordA (χ.ω.compose χ.D)) (B' := wordB (χ.ω.compose χ.D))
    (fun k hk1 hk2 => ⟨wordA_translate hP t0 hk1 (by omega), wordB_translate hP t0 hk1 (by omega)⟩),
    mixFold_ht_eq_height hP hzs, hl.minContent_compose' hD]
  have hprof := MarkedInner.mix_height_marked hl hD hd hph hlt (J := minContent χ.D) (a := (z : ℤ))
    (by omega) (by omega) ⟨le_refl _, by omega⟩
  have e : minContent χ.ω.E + minContent χ.D * χ.ω.period + (z : ℤ) =
      minContent χ.ω.E + (minContent χ.D * χ.ω.period + (z : ℤ)) := by ring
  rw [e, hprof]
  have hends := MarkedInner.D_ends hD
  unfold profM profS
  have hs1 : minContent χ.D - 1 < minContent χ.D := by omega
  have e1 : ¬ (minContent χ.D ≤ minContent χ.D - 1 ∧ minContent χ.D - 1 ≤ maxContent χ.D) := by
    omega
  have e3 : minContent χ.D ≤ minContent χ.D ∧ minContent χ.D ≤ maxContent χ.D := ⟨le_refl _, hmM⟩
  simp only [e1, e3, and_self, ite_false, ite_true]
  rw [← hends.1]
  obtain ⟨hs1', hs2', ht1', ht2', -, -⟩ := id hph
  split_ifs <;> omega

end Chart

/-- **`eq:gluing-original-mixed-mark`, exactly.**  Two case-(d) proper legal roots `χ₁`, `χ₂` of
one parent `F`, of nondividing periods with `g = gcd (p, Q) > 1`: there are phases `s`, `t` of the
first mark, the word data `P` of the pair, generic words `Ab`, `Bb`, and the phases `z`, `o` of
the first chart whose generic slot bits are zero and one, such that the lower mark `W₋` of the
first root has the heights
`H_{W₋}(r) = H⁰_{r mod g} + 1_{z>0, r≥z} - 1_{r≥s}`  for `0 ≤ r < w`,
where `H⁰_j = mixFold_ht Ab Bb j` is the generic height `1 + ∑_{i=1}^j C_i`. -/
theorem mixFold_original_mark_heights {F : Diagram} {χ₁ χ₂ : Chart} (T : TwoRoots F χ₁ χ₂)
    (_hg : 1 < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) (h₁ : χ₁.ω.case = .d)
    (h₂ : χ₂.ω.case = .d) :
    ∃ (s t s₂ t₂ : ℤ) (P : MixFoldPair (wordA F) (wordB F) (span F) χ₁.ω.period.toNat
      χ₂.ω.period.toNat χ₁.ω.width χ₂.ω.width s t s₂ t₂) (Ab Bb : ℤ → ℤ),
      χ₁.ω.IsPhases s t ∧ P.Gen Ab Bb ∧
      ∃ z o : ℤ, ((z = t ∧ o = s) ∨ (z = s ∧ o = t)) ∧ Ab z = 0 ∧ Ab o = 1 ∧
        ∀ r : ℕ, r < χ₁.ω.width →
          height χ₁.ω.W (minContent χ₁.ω.E + r) =
            mixFold_ht Ab Bb (r % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) +
              (if 0 < z ∧ z ≤ (r : ℤ) then 1 else 0) - (if s ≤ (r : ℤ) then 1 else 0) := by
  have hrem : 0 < span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat := by
    by_contra hcon
    exact (TwoRoots.mixed_pairs_remainder_zero T (by omega)).1 (Or.inr h₁)
  have hFc : IsConnectedSkew F := by
    obtain ⟨v, hv⟩ := T.chart₁
    rw [hv]
    exact isConnectedSkew_translate v (T.proper₁.2.2.2.isConnectedSkew_compose T.proper₁.1)
  obtain ⟨s₂, t₂, c₂, x₂, hw₂⟩ := mixFold_chart_data T.proper₂ T.chart₂ h₂
  -- the first chart, with phases kept
  have hw₁ := TwoRoots.width_pos_of_mixed T.proper₁ (Or.inr h₁)
  have hW : χ₁.ω.W.Nonempty := by
    by_contra hcon
    have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
    omega
  have hl : χ₁.ω.IsLegalNonempty := ⟨T.proper₁.2.2.2, hW⟩
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := id hph
  have hcod := ((T.proper₁.mixFoldCoding_of_chartOf T.chart₁).2 s t hW hph)
  rw [h₁] at hcod
  have hP : IsConnectedSkew χ₁.parent := T.proper₁.2.2.2.isConnectedSkew_compose T.proper₁.1
  obtain ⟨v0, hv0⟩ := T.chart₁
  have hspan : span F = span χ₁.parent := by rw [hv0, span_translate]
  have hD2 : 2 ≤ span χ₁.D := two_le_span_of_two_le_card T.proper₁.1 T.proper₁.2.1
  have hx := hl.mixFold_extra T.proper₁.1 hD2 h₁ hph
  have hx' : MixFoldExtra (wordA χ₁.parent) (wordB χ₁.parent) (span F) χ₁.ω.period.toNat
      χ₁.ω.width s t := by
    rw [hspan]; exact hx
  have hwq := hcod.w_lt
  have hN := hcod.two_q_add_w_le
  have x₁ : MixFoldExtra (wordA F) (wordB F) (span F) χ₁.ω.period.toNat χ₁.ω.width s t := by
    refine hx'.of_agree hcod.q_pos hs1 hs2 ht1 ht2 (fun k h1 h2 => ?_) (fun k h1 h2 => ?_)
      (by omega)
    · rw [hv0]
      exact (wordA_translate hP v0 h1 (by rw [← hspan]; omega)).symm
    · rw [hv0]
      exact (wordB_translate hP v0 h1 (by rw [← hspan]; omega)).symm
  have P : MixFoldPair (wordA F) (wordB F) (span F) χ₁.ω.period.toNat χ₂.ω.period.toNat
      χ₁.ω.width χ₂.ω.width s t s₂ t₂ :=
    ⟨hcod, c₂, x₁, x₂, MixFoldWordsOK.of_isConnectedSkew hFc, hw₁, hw₂, T.not_dvd₁, T.not_dvd₂,
      hrem⟩
  obtain ⟨Ab, Bb, hG⟩ := P.exists_gen
  obtain ⟨a, b, r, M, v, hA⟩ := P.exists_arith
  obtain ⟨z, o, hzo, hz, ho⟩ := hG.exists_zero_one_phases hA
  refine ⟨s, t, s₂, t₂, P, Ab, Bb, hph, hG, z, o, hzo, hz, ho, fun r hr => ?_⟩
  have hfb := T.proper₁.mixFold_ht_first_band ⟨v0, hv0⟩ h₁ hW hph r hr
  have hgp : Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ≤ χ₁.ω.period.toNat :=
    Nat.le_of_dvd P.p_pos (Nat.gcd_dvd_left _ _)
  have hht := hG.ht_first hzo hz ho (n := r) (by omega)
  have hmod : mixFold_ht Ab Bb r = mixFold_ht Ab Bb (r % Nat.gcd χ₁.ω.period.toNat
      χ₂.ω.period.toNat) := by
    have := mixFold_gen_ht_mul hG.Ab_per hG.Bb_per (r % Nat.gcd χ₁.ω.period.toNat
      χ₂.ω.period.toNat) (r / Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat)
    rw [hG.drift.1, Nat.mod_add_div'] at this
    simpa using this
  rw [hmod] at hht
  rw [hht] at hfb
  split_ifs at hfb ⊢ <;> omega

/-- The height of the diagonal `n` of a diagram given by bit words is the height word. -/
theorem mixFold_height_fromBits {N : ℕ} {A B : ℕ → ℤ} (h : IsBitData N A B) {n : ℕ} (hn : n < N) :
    height (fromBits N A B) (n : ℤ) = heightWord A B n := by
  unfold height
  rw [diagHi_fromBits h hn, diagLo_fromBits h hn]
  have := bitsLo_add_heightWord A B n
  omega

/-- **`eq:gluing-mixed-heights`, on the inner `G` of the fold.**  Two case-(d) proper legal roots
of one parent `F`, of nondividing periods with `g = gcd (p, Q) > 1`; write `N_F = M g + w_g`,
`w = b g + w_g`, `G = mixFoldInner` the period-`g` inner built from the first and last `g`
diagonals of `F`, `τ = z`, `σ = o - b g`, `α = min (τ, σ)`, `β = max (τ, σ)`, `H⁰_k` the generic
heights.  For `0 ≤ k < w_g` the heights of the lower and upper marked diagonals of `G` are
`L_k = H⁰_k + 1_{τ>0, k≥τ}` and `U_k = H⁰_k + 1_{τ>0} - 1_{σ<w_g, k≥σ}`, and
`L_k - 1_{k≥β} = U_k - 1_{k<α}` equals `H⁰_k + 1_{τ>0, k≥τ} - 1_{k≥σ}` if `τ < σ` and `H⁰_k`
otherwise.

**Differs from the paper's route.**  The retained heights are stated as the heights of `G` minus
the indicators of the deleted cells, not as the heights of the retained cell sets, because the
mark of the Lean construction is the full intersection `G ∩ (G - v)`. -/
theorem mixFold_inner_heights {F : Diagram} {χ₁ χ₂ : Chart} (T : TwoRoots F χ₁ χ₂)
    (hg : 1 < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) (h₁ : χ₁.ω.case = .d)
    (h₂ : χ₂.ω.case = .d) :
    ∃ (s t s₂ t₂ : ℤ) (P : MixFoldPair (wordA F) (wordB F) (span F) χ₁.ω.period.toNat
      χ₂.ω.period.toNat χ₁.ω.width χ₂.ω.width s t s₂ t₂) (Ab Bb : ℤ → ℤ) (b M v : ℕ)
      (z o : ℤ), P.Gen Ab Bb ∧ ((z = t ∧ o = s) ∨ (z = s ∧ o = t)) ∧ Ab z = 0 ∧ Ab o = 1 ∧
      span F = M * Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat + v ∧
      χ₁.ω.width = b * Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat + v ∧
      0 < v ∧ v < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
      ∀ k : ℕ, k < v →
        let g := Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat
        let G := mixFoldInner (wordA F) (wordB F) g M v
        let τ := z
        let σ := o - (b : ℤ) * g
        let α := min τ σ
        let β := max τ σ
        let H0 := mixFold_ht Ab Bb k
        let L := height G (k : ℤ)
        let U := height G ((g + k : ℕ) : ℤ)
        L = H0 + (if 0 < τ ∧ τ ≤ (k : ℤ) then 1 else 0) ∧
        U = H0 + (if 0 < τ then 1 else 0) - (if σ < v ∧ σ ≤ (k : ℤ) then 1 else 0) ∧
        L - (if β ≤ (k : ℤ) then 1 else 0) = U - (if (k : ℤ) < α then 1 else 0) ∧
        L - (if β ≤ (k : ℤ) then 1 else 0) =
          (if τ < σ then
            H0 + (if 0 < τ ∧ τ ≤ (k : ℤ) then 1 else 0) - (if σ ≤ (k : ℤ) then 1 else 0)
            else H0) := by
  obtain ⟨s, t, s₂, t₂, P, Ab, Bb, hph, hG, z, o, hzo, hz, ho, -⟩ :=
    mixFold_original_mark_heights T hg h₁ h₂
  obtain ⟨a, b, r, M, v, hA⟩ := P.exists_arith
  have hFc : IsConnectedSkew F := by
    obtain ⟨v, hv⟩ := T.chart₁
    rw [hv]
    exact isConnectedSkew_translate v (T.proper₁.2.2.2.isConnectedSkew_compose T.proper₁.1)
  have hbd : IsBitData (span F) (fun k : ℕ => wordA F k) (fun k : ℕ => wordB F k) :=
    isBitData_of_isConnectedSkew hFc
  obtain ⟨α', β', hF⟩ := hG.fold_facts hA
  have hGbd := hF.isBitData hbd
  refine ⟨s, t, s₂, t₂, P, Ab, Bb, b, M, v, z, o, hG, hzo, hz, ho, hA.hN, hA.hw, hA.hv0, hA.hvg,
    fun k hk => ?_⟩
  have hvg := hA.hvg
  have key := hG.inner_heights hA hzo hz ho hk
  have hk1 : k < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat + v := by omega
  have e1 := mixFold_height_fromBits hGbd hk1
  have e2 := mixFold_height_fromBits hGbd
    (show Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat + k <
      Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat + v by omega)
  intro g G τ σ α β H0 L U
  have hL : L = heightWord (mixFoldGA (wordA F) g M v) (mixFoldGB (wordB F) g M v) k := e1
  have hU : U = heightWord (mixFoldGA (wordA F) g M v) (mixFoldGB (wordB F) g M v) (g + k) := e2
  rw [hL, hU]
  exact key

/-! ### Checked examples

The parent `F` of span `15` with the two case-(d) roots of periods `4` and `6` (`g = 2`,
remainder one) satisfies the hypotheses of the two theorems above. -/

example : Nat.gcd mixedRootFour.ω.period.toNat mixedRootSix.ω.period.toNat = 2 := by
  decide +kernel

/-- `eq:gluing-original-mixed-mark` applies to the roots of the parent of span `15`. -/
example := mixFold_original_mark_heights mixedRoots_twoRoots (by decide +kernel) rfl rfl

/-- `eq:gluing-mixed-heights` applies to the roots of the parent of span `15`. -/
example := mixFold_inner_heights mixedRoots_twoRoots (by decide +kernel) rfl rfl

end SkewGluing
