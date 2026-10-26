import SkewGluing.Aligned.CaseD.Asm3

/-!
# Aligned marks, case (d): the nested count, parity by parity

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-nested-count`).

`alD_NC V a θ C` states the nested count for the composite `X = C ∘_μ V` in the four forms in which
it is proved for each attachment case of `μ`: the heights `M^X` on the marked diagonals `i < b`
and on the private diagonals `i ≥ b`, and the consecutive spans `S^X` for `i ≤ b` and `i > b`.
`alD_NCI_of_NC` assembles them into `alD_NCI`, the interleaved form used by
`alD_identity_of_NCI`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

/-- The nested count for `X = C ∘_μ V` (`eq:gluing-nested-count`), by parity. -/
def alD_NC (V : Diagram) (a θ : ℤ) (C : Diagram) : Prop :=
  (∀ J i : ℤ, 0 ≤ i → i < (span V : ℤ) - a →
    ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i →
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      alD_Om V a θ i + alD_CT C (walkDelta V a (2 * (minContent V + i) + 1)) J) ∧
  (∀ J i : ℤ, (span V : ℤ) - a ≤ i → i < a → minContent C ≤ J → J ≤ maxContent C →
    profM ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profM V (minContent V + i) + profM C J - 1) ∧
  (∀ J i : ℤ, 0 ≤ i → i ≤ (span V : ℤ) - a →
    ((minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1) →
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) - (if walkDelta V a (2 * (minContent V + i)) = 1 then 1 else 0) +
        alD_CT C (walkDelta V a (2 * (minContent V + i))) J) ∧
  (∀ J i : ℤ, (span V : ℤ) - a < i → i < a → minContent C ≤ J → J ≤ maxContent C →
    profS ((alD_lowerMark V a θ).compose C) (minContent V + (J * a + i)) =
      profS V (minContent V + i) + profM C J - 1)

variable {V C : Diagram} {a θ : ℤ}

theorem alD_Om_eq (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {i : ℤ} (h0 : 0 ≤ i)
    (h1 : i < (span V : ℤ) - a) :
    alD_Om V a θ i = (alD_H V i - alD_L V i + 1) - (if alD_e V a i = 1 then 1 else 0) := by
  have z := alD_zrows hV hD h0 h1
  have e1 := hD.e_bd i h0 h1
  have hE : alD_e V a i = (alD_H V i - alD_L V i) - (alD_H V (i + a) - alD_L V (i + a)) := rfl
  unfold alD_Om
  by_cases h : alD_e V a i = 1
  · have := z.2.2.2.2.2.2 (by omega)
    simp only [h, ite_true]
    omega
  · have := z.2.2.2.2.2.1 (by omega)
    simp only [h, ite_false]
    omega

theorem alD_walk_odd_eq (hV : IsConnectedSkew V) {j : ℤ} (h0 : 0 ≤ j) {a : ℤ} (ha : 0 ≤ a)
    (h1 : j + a ≤ (span V : ℤ) - 1) :
    walkDelta V a (2 * (minContent V + j) + 1) = alD_e V a j := by
  have := walkDelta_odd hV (a := a) (j := j) h0 h1 ha
  rw [this]
  unfold gStep kStep alD_e alD_L alD_H
  have e1 : minContent V + j + a = minContent V + (j + a) := by ring
  rw [e1]; ring

theorem alD_walk_even_eq {j : ℤ} :
    walkDelta V a (2 * (minContent V + j)) = profS V (minContent V + j) -
      profS V (minContent V + j + a) := by
  unfold walkDelta
  have e : 2 * (minContent V + j) + 2 * a = 2 * (minContent V + j + a) := by ring
  rw [e, profIL_even, profIL_even]
  ring

theorem alD_profM_V (hV : IsConnectedSkew V) {i : ℤ} (h0 : 0 ≤ i) (h1 : i < (span V : ℤ)) :
    profM V (minContent V + i) = alD_H V i - alD_L V i + 1 := by
  have hsp := aligned_span_eq hV
  rw [aligned_profM_eq (by omega)]
  rfl

theorem alD_profM_before_min (D : Diagram) (J : ℤ) (h : J < minContent D) : profM D J = 0 := by
  unfold profM
  have : ¬ (minContent D ≤ J ∧ J ≤ maxContent D) := by omega
  simp only [this, ite_false]

theorem alD_NCI_of_NC (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hNC : alD_NC V a θ C) : alD_NCI V a θ C := by
  obtain ⟨hM, hP, hS, hSP⟩ := hNC
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hMa : profM V (minContent V + (a - 1)) = 1 := by
    rw [alD_profM_V hV (by omega) (by omega)]
    have := hD.singleton_a
    omega
  intro J i κ hi0 hi1 hκ0 hκ1 hdom
  obtain rfl | rfl | rfl : κ = -1 ∨ κ = 0 ∨ κ = 1 := by omega
  · -- κ = -1
    have e1 : 2 * (minContent V + (J * a + i)) + -1 = 2 * (minContent V + (J * a + i) - 1) + 1 := by
      ring
    rw [e1, profIL_odd]
    have e2 : 2 * (minContent V + i) + -1 = 2 * (minContent V + i - 1) + 1 := by ring
    rw [e2, profIL_odd]
    by_cases hi : 1 ≤ i
    · have e3 : minContent V + (J * a + i) - 1 = minContent V + (J * a + (i - 1)) := by ring
      have e4 : minContent V + i - 1 = minContent V + (i - 1) := by ring
      rw [e3, e4]
      by_cases hm : 2 * i + -1 ≤ 2 * ((span V : ℤ) - a)
      · simp only [hm, ite_true]
        have hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J (i - 1) := by
          unfold ValidClass
          rcases hdom with h | ⟨h, -⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, by omega⟩
        rw [hM J (i - 1) (by omega) (by omega) hv, alD_Om_eq hV hD (by omega) (by omega),
          alD_profM_V hV (by omega) (by omega)]
        have := alD_walk_odd_eq hV (j := i - 1) (by omega) hap.le (by omega)
        rw [this]
      · simp only [hm, ite_false]
        have hJ : minContent C ≤ J ∧ J ≤ maxContent C := by
          rcases hdom with h | ⟨h, h2⟩
          · exact h
          · omega
        rw [hP J (i - 1) (by omega) (by omega) hJ.1 hJ.2, alD_profM_V hV (by omega) (by omega)]
    · have hi' : i = 0 := by omega
      subst hi'
      have e3 : minContent V + (J * a + 0) - 1 = minContent V + ((J - 1) * a + (a - 1)) := by ring
      rw [e3]
      have hm : 2 * 0 + -1 ≤ 2 * ((span V : ℤ) - a) := by omega
      simp only [hm, ite_true]
      have e5 : minContent V + 0 - 1 = minContent V - 1 := by ring
      rw [e5]
      have hp0 : profM V (minContent V - 1) = 0 := aligned_profM_eq_zero (by omega)
      have hwd : walkDelta V a (2 * (minContent V - 1) + 1) = -1 := by
        unfold walkDelta
        have e6 : 2 * (minContent V - 1) + 1 + 2 * a = 2 * (minContent V + (a - 1)) + 1 := by ring
        rw [e6, profIL_odd, profIL_odd, hp0, hMa]
        ring
      rw [hwd, hp0]
      have hCT : alD_CT C (-1) J = profM C (J - 1) := by unfold alD_CT; simp
      rw [hCT]
      by_cases hJ1 : minContent C ≤ J - 1
      · have hJ2 : J - 1 ≤ maxContent C := by
          rcases hdom with h | ⟨h, -⟩ <;> omega
        rw [hP (J - 1) (a - 1) (by omega) (by omega) hJ1 hJ2, hMa]
        have e0 : (if (-1 : ℤ) = 1 then (1 : ℤ) else 0) = 0 := by norm_num
        rw [e0]; ring
      · have hX0 : profM ((alD_lowerMark V a θ).compose C) (minContent V + ((J - 1) * a + (a - 1)))
            = 0 := by
          apply alD_profM_before_min
          rw [alD_minContent_X hV hD hC]
          have h5 : (J - 1) * a ≤ (minContent C - 1) * a :=
            mul_le_mul_of_nonneg_right (by omega) hap.le
          have e : (minContent C - 1) * a = minContent C * a - a := by ring
          omega
        have hC0 : profM C (J - 1) = 0 := alD_profM_before_min C _ (by omega)
        have e0 : (if (-1 : ℤ) = 1 then (1 : ℤ) else 0) = 0 := by norm_num
        rw [hX0, hC0, e0]; ring
  · -- κ = 0
    have e1 : 2 * (minContent V + (J * a + i)) + 0 = 2 * (minContent V + (J * a + i)) := by ring
    have e2 : 2 * (minContent V + i) + 0 = 2 * (minContent V + i) := by ring
    rw [e1, profIL_even]
    simp only [e2]
    rw [profIL_even]
    by_cases hm : 2 * i + 0 ≤ 2 * ((span V : ℤ) - a)
    · simp only [hm, ite_true]
      have hv : (minContent C ≤ J ∧ J ≤ maxContent C) ∨ J = maxContent C + 1 := by
        rcases hdom with h | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr h
      rw [hS J i hi0 (by omega) hv]
      ring
    · simp only [hm, ite_false]
      have hJ : minContent C ≤ J ∧ J ≤ maxContent C := by
        rcases hdom with h | ⟨h, h2⟩
        · exact h
        · omega
      rw [hSP J i (by omega) hi1 hJ.1 hJ.2]
      ring
  · -- κ = 1
    rw [profIL_odd, profIL_odd]
    by_cases hm : 2 * i + 1 ≤ 2 * ((span V : ℤ) - a)
    · simp only [hm, ite_true]
      have hv : ValidClass (minContent C) (maxContent C) ((span V : ℤ) - a) J i := by
        unfold ValidClass
        rcases hdom with h | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, by omega⟩
      rw [hM J i hi0 (by omega) hv, alD_Om_eq hV hD hi0 (by omega),
        alD_profM_V hV hi0 (by omega)]
      have := alD_walk_odd_eq hV (j := i) hi0 hap.le (by omega)
      rw [this]
    · simp only [hm, ite_false]
      have hJ : minContent C ≤ J ∧ J ≤ maxContent C := by
        rcases hdom with h | ⟨h, h2⟩
        · exact h
        · omega
      rw [hP J i (by omega) hi1 hJ.1 hJ.2, alD_profM_V hV hi0 (by omega)]

end MarkedInner

end SkewGluing
