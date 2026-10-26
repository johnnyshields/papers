import SkewGluing.SmallOverlap.Periodic

/-!
# An empty root and its partner

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the case of a root of width zero.

* `Chart.IsProperRoot.empty_mixed_false`: a diagram with an empty proper root of period `p` and a
  mixed proper root of period `Q`, neither period dividing the other, does not exist.
* `Chart.IsProperRoot.empty_ordinary_periodic`: with an ordinary partner (empty or not) both
  boundary words of the diagram have period `gcd p Q` except at the residue zero.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

/-- **`lem:gluing-small`, empty root: a mixed partner is impossible.**  The mixed root's fixed
boundary word becomes `g`-periodic, but its two private endpoint bits sit at the multiples `w` and
`q` of `g`. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.empty_mixed_false {χ₁ χ₂ : Chart} {F : Diagram}
    {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q) (hW₁ : χ₁.ω.W = ∅)
    (hW₂ : χ₂.ω.W.Nonempty) (hmix : χ₂.ω.case.IsMixed) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) :
    False := by
  obtain ⟨hr, hN1, -, hp2⟩ := h₁.arith
  obtain ⟨hm, hN2, hwQ, hQ2⟩ := h₂.arith
  have hw1 : χ₁.ω.width = 0 := width_eq_zero_of_eq_empty hW₁
  have hu1 : 0 < χ₂.ω.width := h₂.1.2.2.2.width_pos_of_nonempty hW₂
  have hlegal2 : χ₂.ω.IsLegalNonempty := ⟨h₂.1.2.2.2, hW₂⟩
  obtain ⟨s, t, hph⟩ := hlegal2.exists_phases
  have hNp : span F = span χ₁.D * p := by
    have : (span F : ℤ) = (span χ₁.D : ℤ) * p := by rw [hN1, hw1]; simp
    exact_mod_cast this
  have hNQ : span F = span χ₂.D * Q + χ₂.ω.width := by exact_mod_cast hN2
  have hwQ' : χ₂.ω.width < Q := by exact_mod_cast hwQ
  have e1 := h₁.periodic_empty hW₁
  have e2 := h₂.periodic_nonempty hW₂ hph
  have hQZ : χ₂.ω.period = Q := h₂.2.2
  have hwZ : χ₂.ω.widthZ = (χ₂.ω.width : ℤ) := rfl
  have hspP : span (χ₂.ω.compose χ₂.D) = span F := h₂.span_eq.symm
  have hp0 : 0 < p := by omega
  have hQ0 : 0 < Q := by omega
  have hmQ : 2 * Q ≤ span χ₂.D * Q := Nat.mul_le_mul_right Q hm
  have hdata := gcd_dvd_data hNp hNQ
  have hgpos : 0 < Nat.gcd Q p := Nat.gcd_pos_of_pos_left _ hQ0
  have hN1 : 1 ≤ span F := by omega
  have hNZ : ((span F - 1 : ℕ) : ℤ) = (span F : ℤ) - 1 := by push_cast [Nat.cast_sub hN1]; rfl
  have hlegal := hlegal2
  rcases hmix with hc | hd
  · -- case (c): the word `A` has the full period `Q`, with `A_{N-w} = 1` and `A_{N-Q} = 0`
    obtain ⟨-, -, -, -, c5, c6⟩ := hlegal.caps_c h₂.1.1 hc hph
    have hper := e2.1
    simp only [holesA, hc] at hper
    have hg := periodExcept_gcd_empty_full (f := wordA F) hp0 hQ0 hr hm hu1 hNp hNQ hpQ hQp
      e1.1 hper
    have hx := periodExcept_eq_of_dvd hg hgpos (x := (span F : ℤ) - Q)
      (y := (span F : ℤ) - χ₂.ω.width)
      (by omega) (by rw [hNZ]; omega) (by omega) (by
        have := dvd_sub hdata.2.1 hdata.2.2
        have e : ((span F : ℤ) - χ₂.ω.width) - ((span F : ℤ) - Q) = Q - χ₂.ω.width := by ring
        rw [e]; exact this) (by simp)
    have hxA : wordA F ((span F : ℤ) - Q) = 0 := by
      rw [h₂.wordA_eq (by omega) (by omega)]
      have := c6
      rw [hQZ, hspP] at this
      exact this
    have hyA : wordA F ((span F : ℤ) - χ₂.ω.width) = 1 := by
      rw [h₂.wordA_eq (by omega) (by omega)]
      have := c5
      rw [hwZ, hspP] at this
      exact this
    rw [hxA, hyA] at hx
    exact absurd hx (by norm_num)
  · -- case (d): the word `B` has the full period `Q`, with `B_w = 1` and `B_Q = 0`
    obtain ⟨-, -, -, -, c5, c6⟩ := hlegal.caps_d h₂.1.1 hd hph
    have hper := e2.2
    simp only [holesB, hd] at hper
    have hg := periodExcept_gcd_empty_full (f := wordB F) hp0 hQ0 hr hm hu1 hNp hNQ hpQ hQp
      e1.2 hper
    have hx := periodExcept_eq_of_dvd hg hgpos (x := (χ₂.ω.width : ℤ)) (y := (Q : ℤ))
      (by omega) (by rw [hNZ]; omega) (by omega) (by
        have := dvd_sub hdata.2.1 hdata.2.2
        exact (by
          have e : (Q : ℤ) - χ₂.ω.width = Q - χ₂.ω.width := rfl
          rw [e]; exact this)) (by simp)
    have hxB : wordB F (χ₂.ω.width : ℤ) = 1 := by
      rw [h₂.wordB_eq (by omega) (by omega)]
      have := c5
      rw [hwZ] at this
      exact this
    have hyB : wordB F (Q : ℤ) = 0 := by
      rw [h₂.wordB_eq (by omega) (by omega)]
      have := c6
      rw [hQZ] at this
      exact this
    rw [hxB, hyB] at hx
    exact absurd hx (by norm_num)

/-- **`lem:gluing-small`, empty root with an ordinary partner.**  Both boundary words of `F` have
period `g = gcd p Q` except at the residue zero, when `F` has an empty proper root of period `p`
and a proper root of period `Q` that is empty or ordinary, neither period dividing the other.
(`lem:gluing-periods` (ii), at width zero.) -/
theorem _root_.SkewGluing.Chart.IsProperRoot.empty_ordinary_periodic {χ₁ χ₂ : Chart}
    {F : Diagram} {p Q : ℕ} (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q)
    (hW₁ : χ₁.ω.W = ∅) (hord : χ₂.ω.W = ∅ ∨ ¬ χ₂.ω.case.IsMixed) (hpQ : ¬ p ∣ Q)
    (hQp : ¬ Q ∣ p) :
    PeriodWords.PeriodExcept (span F - 1) (Nat.gcd p Q) {0} (wordA F) ∧
    PeriodWords.PeriodExcept (span F - 1) (Nat.gcd p Q) {0} (wordB F) := by
  obtain ⟨hr, hN1, -, hp2⟩ := h₁.arith
  obtain ⟨hm, hN2, hwQ, hQ2⟩ := h₂.arith
  have hw1 : χ₁.ω.width = 0 := width_eq_zero_of_eq_empty hW₁
  have hNp : span F = span χ₁.D * p := by
    have : (span F : ℤ) = (span χ₁.D : ℤ) * p := by rw [hN1, hw1]; simp
    exact_mod_cast this
  have hNQ : span F = span χ₂.D * Q + χ₂.ω.width := by exact_mod_cast hN2
  have hwQ' : χ₂.ω.width < Q := by exact_mod_cast hwQ
  have e1 := h₁.periodic_empty hW₁
  have hp0 : 0 < p := by omega
  have hQ0 : 0 < Q := by omega
  by_cases hW₂ : χ₂.ω.W = ∅
  · have e2 := h₂.periodic_empty hW₂
    have hw2 : χ₂.ω.width = 0 := width_eq_zero_of_eq_empty hW₂
    exact ⟨periodExcept_gcd_zero_hole (h := 0) hp0 hQ0 hr hm hwQ' hNp hNQ hpQ hQp
        (by omega) e1.1 e2.1,
      periodExcept_gcd_zero_hole (h := 0) hp0 hQ0 hr hm hwQ' hNp hNQ hpQ hQp
        (by omega) e1.2 e2.2⟩
  · have hWne : χ₂.ω.W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW₂
    have hmix : ¬ χ₂.ω.case.IsMixed := hord.resolve_left hW₂
    have hlegal2 : χ₂.ω.IsLegalNonempty := ⟨h₂.1.2.2.2, hWne⟩
    obtain ⟨s, t, hph⟩ := hlegal2.exists_phases
    obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
    have e2 := h₂.periodic_nonempty hWne hph
    have hwZ : χ₂.ω.widthZ = (χ₂.ω.width : ℤ) := rfl
    have hcc : χ₂.ω.case = .a ∨ χ₂.ω.case = .b := by
      unfold AttachCase.IsMixed at hmix
      cases hh : χ₂.ω.case <;> simp_all
    rcases hcc with hc | hc
    · simp only [holesA, holesB, hc] at e2
      exact ⟨periodExcept_gcd_zero_hole (h := t) hp0 hQ0 hr hm hwQ' hNp hNQ hpQ hQp
          (by omega) e1.1 e2.1,
        periodExcept_gcd_zero_hole (h := s) hp0 hQ0 hr hm hwQ' hNp hNQ hpQ hQp
          (by omega) e1.2 e2.2⟩
    · simp only [holesA, holesB, hc] at e2
      exact ⟨periodExcept_gcd_zero_hole (h := s) hp0 hQ0 hr hm hwQ' hNp hNQ hpQ hQp
          (by omega) e1.1 e2.1,
        periodExcept_gcd_zero_hole (h := t) hp0 hQ0 hr hm hwQ' hNp hNQ hpQ hQp
          (by omega) e1.2 e2.2⟩

end SmallOverlap
end SkewGluing
