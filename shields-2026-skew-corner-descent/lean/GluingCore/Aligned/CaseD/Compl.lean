/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Compl.lean`. -/
import GluingCore.Aligned.CaseD.Mark1

/-!
# Aligned marks, case (d): the complements of the lower copy

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, condition III).

With `e_j = M_j - M_{j+a}` monotone in `{-1, 0, 1}` (`eq:gluing-walk-signs`), the diagonals
`j < b` with `e_j ≤ 0` carry no lower tail and the others `e_j = 1` carry one cell; there is a
split point `s'` of `[0, b)` (`alD_s`).  Dually the upper tails sit on the diagonals `a + j`,
`j < t'`, where `e_j = -1` (`alD_t`).  `V \ Z` and `V \ (Z + z)` are connected skew diagrams
(`alD_compl_lower`, `alD_compl_upper`): their diagonals are the tails followed by the whole
private and marked diagonals of `V`.

Sorry-free.
-/

namespace GluingCore

theorem alD_split (b : ℤ) (hb : 0 ≤ b) (f : ℤ → ℤ)
    (hmono : ∀ j, 0 ≤ j → j + 1 < b → f j ≤ f (j + 1)) (c : ℤ) :
    ∃ s, 0 ≤ s ∧ s ≤ b ∧ (∀ j, 0 ≤ j → j < s → f j < c) ∧ (∀ j, s ≤ j → j < b → c ≤ f j) := by
  by_cases hex : ∃ n : ℕ, (n : ℤ) < b ∧ c ≤ f n
  · classical
    have hspec := Nat.find_spec hex
    have hn2 : c ≤ f (Nat.find hex : ℕ) := hspec.2
    have hmin : ∀ k : ℕ, k < Nat.find hex → ¬ ((k : ℤ) < b ∧ c ≤ f k) :=
      fun k hk => Nat.find_min hex hk
    refine ⟨(Nat.find hex : ℤ), by omega, by omega, ?_, ?_⟩
    · intro j h0 h1
      have := hmin j.toNat (by omega)
      have e : ((j.toNat : ℕ) : ℤ) = j := by omega
      rw [e] at this
      omega
    · intro j h0 h1
      induction j, h0 using Int.leInduction with
      | base => exact hn2
      | succ k hk ih =>
        have := hmono k (by omega) h1
        have := ih (by omega)
        omega
  · refine ⟨b, hb, le_rfl, ?_, fun j h0 h1 => by omega⟩
    intro j h0 h1
    by_contra hcon
    have e : ((j.toNat : ℕ) : ℤ) = j := by omega
    exact hex ⟨j.toNat, by omega, by rw [e]; omega⟩

section Phases

variable {V : Diagram} {a θ : ℤ}

theorem alD_e_first (hV : IsConnectedSkew V) (hD : alD_Data V a θ) : alD_e V a 0 ≤ 0 := by
  have h0 := alD_end0 hV
  have ha := hD.ha
  have hb := hD.hb
  have l := alD_L_le_H hV (j := a) (by omega) (by omega)
  unfold alD_e
  simp only [zero_add]
  omega

theorem alD_e_last (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    0 ≤ alD_e V a ((span V : ℤ) - a - 1) := by
  have h0 := alD_endN hV
  have hb := hD.hb
  have ha := hD.ha
  have l := alD_L_le_H hV (j := (span V : ℤ) - a - 1) (by omega) (by omega)
  unfold alD_e
  have e : (span V : ℤ) - a - 1 + a = (span V : ℤ) - 1 := by ring
  rw [e]
  omega

/-- The split point of the lower tails: `e_j ≤ 0` on `[0, s')` and `e_j = 1` on `[s', b)`. -/
theorem alD_s (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    ∃ s, 1 ≤ s ∧ s ≤ (span V : ℤ) - a ∧ (∀ j, 0 ≤ j → j < s → alD_e V a j ≤ 0) ∧
      (∀ j, s ≤ j → j < (span V : ℤ) - a → alD_e V a j = 1) := by
  have hb := hD.hb
  obtain ⟨s, h0, h1, h2, h3⟩ := alD_split ((span V : ℤ) - a) hb.le (alD_e V a)
    hD.e_mono 1
  have e0 := alD_e_first hV hD
  refine ⟨s, ?_, h1, fun j hj hj' => by have := h2 j hj hj'; omega, fun j hj hj' => ?_⟩
  · by_contra hcon
    have : s = 0 := by omega
    have := h3 0 (by omega) hb
    omega
  · have := h3 j hj hj'
    have := hD.e_bd j (by omega) hj'
    omega

/-- The split point of the upper tails: `e_j = -1` on `[0, t')`, `0 ≤ e_j` on `[t', b)`. -/
theorem alD_t (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    ∃ t, 0 ≤ t ∧ t < (span V : ℤ) - a ∧ (∀ j, 0 ≤ j → j < t → alD_e V a j = -1) ∧
      (∀ j, t ≤ j → j < (span V : ℤ) - a → 0 ≤ alD_e V a j) := by
  have hb := hD.hb
  obtain ⟨t, h0, h1, h2, h3⟩ := alD_split ((span V : ℤ) - a) hb.le (alD_e V a)
    hD.e_mono 0
  have e0 := alD_e_last hV hD
  refine ⟨t, h0, ?_, fun j hj hj' => ?_, h3⟩
  · by_contra hcon
    have : t = (span V : ℤ) - a := by omega
    have := h2 ((span V : ℤ) - a - 1) (by omega) (by omega)
    omega
  · have := h2 j hj hj'
    have := hD.e_bd j hj (by omega)
    omega

end Phases

/-- The row of the lower tail on the diagonal `j` (the single cell of `V_j \ Z_j` when
`e_j = 1`). -/
def alD_tail (V : Diagram) (a θ j : ℤ) : ℤ :=
  if alD_L V j < alD_zl V a θ j then alD_L V j else alD_H V j

/-- First rows of `V \ Z`: the tail below `b`, the whole diagonal from `b` on. -/
def alD_c1Lo (V : Diagram) (a θ j : ℤ) : ℤ :=
  if j < (span V : ℤ) - a then alD_tail V a θ j else alD_L V j

/-- Last rows of `V \ Z`. -/
def alD_c1Hi (V : Diagram) (a θ j : ℤ) : ℤ :=
  if j < (span V : ℤ) - a then alD_tail V a θ j else alD_H V j

section Lower

variable {V : Diagram} {a θ : ℤ}

theorem alD_mem_compl1 (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {s : ℤ}
    (hs0 : 0 ≤ s) (hs3 : s ≤ (span V : ℤ) - a) (hs1 : ∀ j, 0 ≤ j → j < s → alD_e V a j ≤ 0)
    (hs2 : ∀ j, s ≤ j → j < (span V : ℤ) - a → alD_e V a j = 1) (r j : ℤ) :
    (r, r + (minContent V + j)) ∈ V \ alD_Z V a θ ↔
      s ≤ j ∧ j < (span V : ℤ) ∧ alD_c1Lo V a θ j ≤ r ∧ r ≤ alD_c1Hi V a θ j := by
  have hb := hD.hb
  have ha := hD.ha
  rw [Finset.mem_sdiff, alD_mem_V hV, alD_mem_Z hV ha.le]
  unfold alD_c1Lo alD_c1Hi
  by_cases hjb : j < (span V : ℤ) - a
  · simp only [hjb, ↓reduceIte]
    by_cases hj0 : 0 ≤ j
    · have z := alD_zrows hV hD hj0 hjb
      by_cases hjs : j < s
      · have := hs1 j hj0 hjs
        have e1 := hD.e_bd j hj0 hjb
        unfold alD_tail
        omega
      · have := hs2 j (by omega) hjb
        unfold alD_tail alD_e at *
        omega
    · omega
  · simp only [hjb, ↓reduceIte]
    omega

theorem alD_c1_ne (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {s : ℤ}
    (_hs2 : ∀ j, s ≤ j → j < (span V : ℤ) - a → alD_e V a j = 1) {j : ℤ} (hj : s ≤ j)
    (hs0 : 0 ≤ s) (hj2 : j < (span V : ℤ)) : alD_c1Lo V a θ j ≤ alD_c1Hi V a θ j := by
  have hb := hD.hb
  have ha := hD.ha
  unfold alD_c1Lo alD_c1Hi
  by_cases hjb : j < (span V : ℤ) - a
  · simp only [hjb, ↓reduceIte]; exact le_rfl
  · simp only [hjb, ↓reduceIte]
    exact alD_L_le_H hV (by omega) hj2

theorem alD_c1_step (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {s : ℤ}
    (hs0 : 1 ≤ s) (_hs3 : s ≤ (span V : ℤ) - a)
    (hs2 : ∀ j, s ≤ j → j < (span V : ℤ) - a → alD_e V a j = 1) {j : ℤ} (hj : s + 1 ≤ j)
    (hj2 : j < (span V : ℤ)) :
    (alD_c1Lo V a θ (j - 1) - alD_c1Lo V a θ j = 0 ∨
      alD_c1Lo V a θ (j - 1) - alD_c1Lo V a θ j = 1) ∧
    (alD_c1Hi V a θ (j - 1) - alD_c1Hi V a θ j = 0 ∨
      alD_c1Hi V a θ (j - 1) - alD_c1Hi V a θ j = 1) := by
  have hb := hD.hb
  have ha := hD.ha
  have hst := alD_step hV (j := j) (by omega) hj2
  have hbb := hD.singleton_b
  unfold alD_c1Lo alD_c1Hi
  by_cases hj1 : j - 1 < (span V : ℤ) - a
  · simp only [hj1, ↓reduceIte]
    by_cases hjb : j < (span V : ℤ) - a
    · simp only [hjb, ↓reduceIte]
      have z1 := alD_zrows hV hD (j := j - 1) (by omega) hj1
      have z2 := alD_zrows hV hD (j := j) (by omega) hjb
      have t1 := hD.th1 (j - 1) (by omega) hj1
      have t2 := hD.th1 j (by omega) hjb
      have t3 := hD.th2 j (by omega) hjb
      have d := hD.d_bd j (by omega) hjb
      have e1 := hs2 (j - 1) (by omega) hj1
      have e2 := hs2 j (by omega) hjb
      have l1 := alD_L_le_H hV (j := j - 1) (by omega) (by omega)
      have l2 := alD_L_le_H hV (j := j) (by omega) (by omega)
      have l3 := alD_L_le_H hV (j := j + a) (by omega) (by omega)
      have l4 := alD_L_le_H hV (j := j - 1 + a) (by omega) (by omega)
      have e : j + a - 1 = j - 1 + a := by ring
      unfold alD_d at d
      rw [e] at d
      unfold alD_e at e1 e2
      unfold alD_tail
      unfold alD_zl alD_zh at *
      omega
    · simp only [hjb, ↓reduceIte]
      have hjb' : j = (span V : ℤ) - a := by omega
      rw [← hjb'] at hbb
      have l1 := alD_L_le_H hV (j := j - 1) (by omega) (by omega)
      unfold alD_tail
      split_ifs <;> omega
  · have hjb : ¬ j < (span V : ℤ) - a := by omega
    simp only [hj1, hjb, ↓reduceIte]
    exact hst

theorem alD_compl_lower (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {s : ℤ}
    (hs0 : 1 ≤ s) (hs3 : s ≤ (span V : ℤ) - a)
    (hs1 : ∀ j, 0 ≤ j → j < s → alD_e V a j ≤ 0)
    (hs2 : ∀ j, s ≤ j → j < (span V : ℤ) - a → alD_e V a j = 1) :
    IsConnectedSkew (V \ alD_Z V a θ) := by
  have hb := hD.hb
  have ha := hD.ha
  refine alD_connected_of_rows (V \ alD_Z V a θ) (minContent V + s) ((span V : ℤ) - s)
    (fun j => alD_c1Lo V a θ (s + j)) (fun j => alD_c1Hi V a θ (s + j)) (by omega) ?_ ?_ ?_ ?_
    ?_ ?_
  · intro j r
    have := alD_mem_compl1 hV hD (by omega) hs3 hs1 hs2 r (s + j)
    have e : minContent V + (s + j) = minContent V + s + j := by ring
    rw [e] at this
    rw [this]
    omega
  · intro j h0 h1
    exact alD_c1_ne hV hD hs2 (by omega) (by omega) (by omega)
  · intro j h0 h1
    have := alD_c1_step hV hD hs0 hs3 hs2 (j := s + j) (by omega) (by omega)
    have e : s + j - 1 = s + (j - 1) := by ring
    rw [e] at this
    exact this.1
  · intro j h0 h1
    have := alD_c1_step hV hD hs0 hs3 hs2 (j := s + j) (by omega) (by omega)
    have e : s + j - 1 = s + (j - 1) := by ring
    rw [e] at this
    exact this.2
  · simp only [add_zero]
    unfold alD_c1Lo alD_c1Hi
    by_cases hjb : s < (span V : ℤ) - a
    · simp only [hjb, ↓reduceIte]
    · have : s = (span V : ℤ) - a := by omega
      simp only [hjb, ↓reduceIte]
      rw [this]; exact hD.singleton_b
  · have e : s + ((span V : ℤ) - s - 1) = (span V : ℤ) - 1 := by ring
    rw [e]
    unfold alD_c1Lo alD_c1Hi
    have : ¬ (span V : ℤ) - 1 < (span V : ℤ) - a := by omega
    simp only [this, ↓reduceIte]
    exact alD_endN hV

end Lower

/-- The row of the upper tail on the diagonal `a + j` (the cell of `V_{a+j} \ (Z_j + z)` when
`e_j = -1`). -/
def alD_utail (V : Diagram) (a θ j : ℤ) : ℤ :=
  if alD_L V (j + a) < alD_zl V a θ j + θ then alD_L V (j + a) else alD_H V (j + a)

/-- First rows of `V \ (Z + z)`: whole diagonals below `a`, then the tails. -/
def alD_c2Lo (V : Diagram) (a θ j : ℤ) : ℤ :=
  if j < a then alD_L V j else alD_utail V a θ (j - a)

/-- Last rows of `V \ (Z + z)`. -/
def alD_c2Hi (V : Diagram) (a θ j : ℤ) : ℤ :=
  if j < a then alD_H V j else alD_utail V a θ (j - a)

section Upper

variable {V : Diagram} {a θ : ℤ} {cs : AttachCase}

theorem alD_mem_compl2 (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {t : ℤ} (ht0 : 0 ≤ t)
    (ht1 : t < (span V : ℤ) - a)
    (ht2 : ∀ j, 0 ≤ j → j < t → alD_e V a j = -1)
    (ht3 : ∀ j, t ≤ j → j < (span V : ℤ) - a → 0 ≤ alD_e V a j) (r j : ℤ) :
    (r, r + (minContent V + j)) ∈ V \ (alD_mark V a θ cs).upper ↔
      0 ≤ j ∧ j < a + t ∧ alD_c2Lo V a θ j ≤ r ∧ r ≤ alD_c2Hi V a θ j := by
  have hb := hD.hb
  have ha := hD.ha
  rw [Finset.mem_sdiff, alD_mem_V hV, alD_mem_upper hV ha.le]
  unfold alD_c2Lo alD_c2Hi
  by_cases hja : j < a
  · simp only [hja, ↓reduceIte]
    omega
  · simp only [hja, ↓reduceIte]
    by_cases hjs : j < (span V : ℤ)
    · have z := alD_zrows hV hD (j := j - a) (by omega) (by omega)
      have t1 := hD.th1 (j - a) (by omega) (by omega)
      have e : j - a + a = j := by ring
      rw [e] at z t1
      have l1 := alD_L_le_H hV (j := j) (by omega) hjs
      by_cases hjt : j < a + t
      · have := ht2 (j - a) (by omega) (by omega)
        unfold alD_e at this
        rw [e] at this
        unfold alD_utail
        rw [e]
        unfold alD_zl alD_zh at *
        omega
      · have := ht3 (j - a) (by omega) (by omega)
        unfold alD_e at this
        rw [e] at this
        unfold alD_zl alD_zh at *
        omega
    · omega

theorem alD_c2_step (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {t : ℤ} (_ht0 : 0 ≤ t)
    (ht1 : t < (span V : ℤ) - a)
    (ht2 : ∀ j, 0 ≤ j → j < t → alD_e V a j = -1) {j : ℤ} (hj : 1 ≤ j) (hj2 : j < a + t) :
    (alD_c2Lo V a θ (j - 1) - alD_c2Lo V a θ j = 0 ∨
      alD_c2Lo V a θ (j - 1) - alD_c2Lo V a θ j = 1) ∧
    (alD_c2Hi V a θ (j - 1) - alD_c2Hi V a θ j = 0 ∨
      alD_c2Hi V a θ (j - 1) - alD_c2Hi V a θ j = 1) := by
  have hb := hD.hb
  have ha := hD.ha
  have hbb := hD.singleton_a
  unfold alD_c2Lo alD_c2Hi
  by_cases hja : j < a
  · have hst := alD_step hV (j := j) hj (by omega)
    have hj1 : j - 1 < a := by omega
    simp only [hja, hj1, ↓reduceIte]
    exact hst
  · obtain ⟨i, rfl⟩ : ∃ i, j = a + i := ⟨j - a, by ring⟩
    have hi0 : 0 ≤ i := by omega
    have hjj : a + i - a = i := by ring
    have hja' : ¬ a + i < a := by omega
    by_cases hi : i = 0
    · subst hi
      have hj1 : a + 0 - 1 < a := by omega
      simp only [hja', hj1, ↓reduceIte, hjj]
      have hst := alD_step hV (j := a + 0) (by omega) (by omega)
      have l1 := alD_L_le_H hV (j := a + 0) (by omega) (by omega)
      have z := alD_zrows hV hD (j := 0) (by omega) (by omega)
      have e : a + 0 - 1 = a - 1 := by ring
      rw [e] at hst ⊢
      rw [e] at hj1
      simp only [add_zero, zero_add] at *
      unfold alD_utail
      simp only [zero_add]
      split_ifs <;> omega
    · have hj1 : ¬ a + i - 1 < a := by omega
      simp only [hja', hj1, ↓reduceIte, hjj]
      have hjj2 : a + i - 1 - a = i - 1 := by ring
      rw [hjj2]
      have z1 := alD_zrows hV hD (j := i - 1) (by omega) (by omega)
      have z2 := alD_zrows hV hD (j := i) (by omega) (by omega)
      have t1 := hD.th1 (i - 1) (by omega) (by omega)
      have t2 := hD.th1 i (by omega) (by omega)
      have t3 := hD.th2 i (by omega) (by omega)
      have d := hD.d_bd i (by omega) (by omega)
      have e1 := ht2 (i - 1) (by omega) (by omega)
      have e2 := ht2 i (by omega) (by omega)
      have l1 := alD_L_le_H hV (j := i - 1) (by omega) (by omega)
      have l2 := alD_L_le_H hV (j := i) (by omega) (by omega)
      have l3 := alD_L_le_H hV (j := i + a) (by omega) (by omega)
      have l4 := alD_L_le_H hV (j := i - 1 + a) (by omega) (by omega)
      have e5 : i + a - 1 = i - 1 + a := by ring
      have hst := alD_step hV (j := i + a) (by omega) (by omega)
      rw [e5] at hst
      unfold alD_d at d
      rw [e5] at d
      have e1' := e1
      have e2' := e2
      unfold alD_e at e1' e2'
      unfold alD_utail
      unfold alD_zl alD_zh at *
      split_ifs <;> omega

theorem alD_compl_upper (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {t : ℤ} (ht0 : 0 ≤ t)
    (ht1 : t < (span V : ℤ) - a)
    (ht2 : ∀ j, 0 ≤ j → j < t → alD_e V a j = -1)
    (ht3 : ∀ j, t ≤ j → j < (span V : ℤ) - a → 0 ≤ alD_e V a j) :
    IsConnectedSkew (V \ (alD_mark V a θ cs).upper) := by
  have hb := hD.hb
  have ha := hD.ha
  refine alD_connected_of_rows (V \ (alD_mark V a θ cs).upper) (minContent V) (a + t)
    (alD_c2Lo V a θ) (alD_c2Hi V a θ) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j r
    exact alD_mem_compl2 hV hD ht0 ht1 ht2 ht3 r j
  · intro j h0 h1
    unfold alD_c2Lo alD_c2Hi
    by_cases hja : j < a
    · simp only [hja, ↓reduceIte]
      exact alD_L_le_H hV h0 (by omega)
    · simp only [hja, ↓reduceIte]; exact le_rfl
  · intro j h0 h1
    exact (alD_c2_step hV hD ht0 ht1 ht2 h0 h1).1
  · intro j h0 h1
    exact (alD_c2_step hV hD ht0 ht1 ht2 h0 h1).2
  · unfold alD_c2Lo alD_c2Hi
    simp only [show (0 : ℤ) < a from ha, ↓reduceIte]
    exact alD_end0 hV
  · unfold alD_c2Lo alD_c2Hi
    by_cases hja : a + t - 1 < a
    · simp only [hja, ↓reduceIte]
      have : t = 0 := by omega
      have e : a + t - 1 = a - 1 := by omega
      rw [e]; exact hD.singleton_a
    · simp only [hja, ↓reduceIte]

end Upper

end GluingCore
