import SkewGluing.FoldSupplied.MixedFacts

/-!
# The contacts and the end heights of a case-(d) inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:mixed-fold`): with `v = d g + a`, `0 < a < g`, both projected contacts lie in
`[0, a]`, the height at the folded private diagonal `a` is one, the exceptional bits of block `d`
are read off the phases, and the height after the upper copy, `Sg (M g)`, is one for
`M = r / g + d` (`MixCtx.end_facts`).

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

variable {A B : ℤ → ℤ} {r v s t g : ℕ}

namespace MixCtx

theorem m_ge_two (h : MixCtx A B r v s t g) : 2 ≤ r / g := by
  obtain ⟨c, hc⟩ := h.gr
  have hg := h.g_pos
  have hglt := h.glt
  have : r / g = c := by rw [hc]; exact Nat.mul_div_cancel_left c hg
  rw [this]
  by_contra hcon
  have : c ≤ 1 := by omega
  have : g * c ≤ g * 1 := Nat.mul_le_mul_left g this
  omega

theorem a_pos (h : MixCtx A B r v s t g) : 0 < v % g := by
  by_contra hcon
  have h0 : v % g = 0 := by omega
  have hv := h.w.v_pos
  have hvr := h.w.v_lt
  have e := h.mnB_mod (i := v) (by omega)
  rw [h0] at e
  have e2 : mnB B v = 1 := by
    have : v ≠ 0 := by omega
    simp only [mnB, this, if_false]; exact h.w.B_v
  have e3 : mnB B 0 = 0 := by simp [mnB]
  omega

/-- The case `d = 0`: the contacts are the phases themselves. -/
theorem facts_zero (h : MixCtx A B r v s t g) (hd : v / g = 0) :
    t % g ≤ v % g ∧ s % g ≤ v % g ∧ Sg A B (v % g + 1) = 1 ∧
    mnA A (v / g * g + t % g) = 1 ∧ mnA A (v / g * g + s % g) = 1 ∧ s / g = 0 ∧ t / g = 0 := by
  have hvg : v < g := by
    rcases Nat.div_eq_zero_iff.mp hd with h1 | h1
    · have := h.g_pos; omega
    · exact h1
  have hts := h.w.t_lt
  have hsv := h.w.s_le
  have hmv : v % g = v := Nat.mod_eq_of_lt hvg
  have hs : s % g = s := Nat.mod_eq_of_lt (by omega)
  have ht : t % g = t := Nat.mod_eq_of_lt (by omega)
  have hs0 : s / g = 0 := Nat.div_eq_of_lt (by omega)
  have ht0 : t / g = 0 := Nat.div_eq_of_lt (by omega)
  have s1 := h.w.sing_v
  rw [mixFold_ht_eq_Sg] at s1
  refine ⟨by omega, by omega, by rw [hmv]; exact s1, ?_, ?_, hs0, ht0⟩
  · rw [hd, zero_mul, zero_add, ht]; exact h.mnA_t
  · rw [hd, zero_mul, zero_add, hs]; exact h.mnA_s

theorem facts_pos (h : MixCtx A B r v s t g) (hd : 1 ≤ v / g) :
    t % g ≤ v % g ∧ s % g ≤ v % g ∧ Sg A B (v % g + 1) = 1 ∧
    Sg A B (v / g * g) = 1 + (if s / g < v / g then 1 else 0) ∧
    mnA A (v / g * g + t % g) = 0 ∧
    mnA A (v / g * g + s % g) = (if s / g = v / g then 1 else 0) ∧ t / g < v / g := by
  have hg := h.g_pos
  have hgr := h.glt
  have hts := h.w.t_lt
  have hsv := h.w.s_le
  have hvr := h.w.v_lt
  have hvpos := h.w.v_pos
  have hvdm := Nat.div_add_mod' v g
  have hsdm := Nat.div_add_mod' s g
  have htdm := Nat.div_add_mod' t g
  have ha := Nat.mod_lt v hg
  have hσ := Nat.mod_lt s hg
  have hτ := Nat.mod_lt t hg
  have hdg : g ≤ v / g * g := Nat.le_mul_of_pos_left g (by omega)
  -- the end of the mark
  have F1 := h.w.sing_v
  rw [mixFold_ht_eq_Sg] at F1
  have F2 := h.sg_block (j := v / g) (z := v % g) ha (by omega)
  rw [show v / g * g + v % g = v by omega] at F2
  -- the positivity of the mark
  have F3 := h.w.mpos (v / g * g - 1) (by omega)
  rw [mixFold_ht_eq_Sg, show v / g * g - 1 + 1 = v / g * g by omega] at F3
  have F4 := h.w.mpos (v % g) (by omega)
  rw [mixFold_ht_eq_Sg] at F4
  -- the bits
  have bP := h.mnA_bit (k := v / g * g + t % g) (by omega)
  have bQ := h.mnA_bit (k := v / g * g + s % g) (by omega)
  have hsd : s / g ≤ v / g := Nat.div_le_div_right hsv
  have htd : t / g ≤ s / g := Nat.div_le_div_right (by omega)
  have hQ : s / g = v / g → mnA A (v / g * g + s % g) = 1 := by
    intro e
    have := h.exc_term_s
    rwa [e] at this
  have hP : t / g = v / g → mnA A (v / g * g + t % g) = 1 := by
    intro e
    have := h.exc_term_t
    rwa [e] at this
  have hσa : s / g = v / g → s % g ≤ v % g := by
    intro e
    have : s / g * g = v / g * g := by rw [e]
    omega
  have hslt : s / g < v / g ↔ s < v / g * g := by
    rw [Nat.div_lt_iff_lt_mul hg]
  have hsle : (if s ≤ v / g * g - 1 then (1 : ℤ) else 0) = (if s / g < v / g then 1 else 0) := by
    have : s ≤ v / g * g - 1 ↔ s / g < v / g := by
      rw [hslt]; omega
    simp only [this]
  rw [hsle] at F3
  generalize mnA A (v / g * g + t % g) = P at *
  generalize mnA A (v / g * g + s % g) = Q at *
  generalize Sg A B (v / g * g) = X at *
  generalize Sg A B (v % g + 1) = Y at *
  split_ifs at F2 F3 F4 hQ hP hσa ⊢ <;> omega

theorem end_facts (h : MixCtx A B r v s t g) :
    t % g ≤ v % g ∧ s % g ≤ v % g ∧ Sg A B (v % g + 1) = 1 ∧
    mnA A (v / g * g + t % g) = (if t / g = v / g then 1 else 0) ∧
    mnA A (v / g * g + s % g) = (if s / g = v / g then 1 else 0) ∧
    Sg A B ((r / g + v / g) * g) = 1 := by
  have hg := h.g_pos
  have hr := h.r_eq
  have hsdm := Nat.div_add_mod' s g
  have htdm := Nat.div_add_mod' t g
  have hvdm := Nat.div_add_mod' v g
  have hts := h.w.t_lt
  have hsv := h.w.s_le
  have hvr := h.w.v_lt
  have hsd : s / g ≤ v / g := Nat.div_le_div_right hsv
  have htd : t / g ≤ s / g := Nat.div_le_div_right (by omega)
  by_cases hd : v / g = 0
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h.facts_zero hd
    refine ⟨a1, a2, a3, ?_, ?_, ?_⟩
    · rw [a4, a7, hd]; simp
    · rw [a5, a6, hd]; simp
    · rw [hd, add_zero, ← hr]; exact h.Sg_r
  · have hd1 : 1 ≤ v / g := Nat.one_le_iff_ne_zero.mpr hd
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h.facts_pos hd1
    refine ⟨a1, a2, a3, ?_, a6, ?_⟩
    · rw [a5]; have : ¬ t / g = v / g := by omega
      simp [this]
    · have hu := h.sg_upper (n := v / g * g) (by omega)
      have e : r + v / g * g = (r / g + v / g) * g := by
        rw [add_mul, ← hr]
      rw [e] at hu
      rw [hu, a4]
      have hl1 : (if s < v / g * g then (1 : ℤ) else 0) = (if s / g < v / g then 1 else 0) := by
        have : s < v / g * g ↔ s / g < v / g := by
          rw [Nat.div_lt_iff_lt_mul hg]
        simp only [this]
      have hl2 : (if t < v / g * g then (1 : ℤ) else 0) = 1 := by
        have : t < v / g * g := by
          have : t / g < v / g := a7
          exact (Nat.div_lt_iff_lt_mul hg).mp this
        simp [this]
      rw [hl1, hl2]
      split_ifs <;> omega

end MixCtx

end FoldSupplied
end SkewGluing
