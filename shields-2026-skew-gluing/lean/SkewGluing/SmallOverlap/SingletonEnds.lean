import SkewGluing.SmallOverlap.SingletonInner

/-!
# The end bits of a width-one root

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the bits at the two ends of the boundary words of a diagram with a
proper root of width one.

With `λ = 0` for a horizontal and `1` for a vertical lower attachment and `υ = 0` for a horizontal
and `1` for a vertical upper attachment (`CaseBits`), the first bits are
`A_1 = B_1 = λ` and the last bits `A_{N-1} = B_{N-1} = υ`
(`Chart.IsProperRoot.singleton_ends`).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

/-- **End bits of a width-one root.** -/
theorem _root_.SkewGluing.Chart.IsProperRoot.singleton_ends {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) (hw : χ.ω.width = 1) :
    ∃ l u : ℤ, CaseBits χ.ω.case l u ∧ wordA F 1 = l ∧ wordB F 1 = l ∧
      wordA F ((span F : ℤ) - 1) = u ∧ wordB F ((span F : ℤ) - 1) = u := by
  have hW := h.W_nonempty_of_width_one hw
  have hlegal : χ.ω.IsLegalNonempty := ⟨h.1.2.2.2, hW⟩
  have hwZ : χ.ω.widthZ = 1 := by unfold MarkedInner.widthZ; omega
  obtain ⟨s, t, hph⟩ := hlegal.exists_phases
  obtain ⟨rfl, rfl⟩ := phases_one hph hwZ
  have htab := h.singleton_table hw
  have hD := h.1.1
  obtain ⟨hr, hN, hwq, hp2⟩ := h.arith
  have hperZ : χ.ω.period = (p : ℤ) := h.2.2
  have hNZ : (span F : ℤ) = (span χ.D : ℤ) * p + 1 := by rw [hN, hw]; push_cast; ring
  have hsd : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hr
  have hp2' : (2 : ℤ) ≤ p := by exact_mod_cast hp2
  have hpF : (p : ℤ) < span F := by nlinarith
  have hLZ : (((span F - 1 : ℕ)) : ℤ) = (span F : ℤ) - 1 := by
    have : 1 ≤ span F := by omega
    push_cast [Nat.cast_sub this]; rfl
  have hs : span (χ.ω.compose χ.D) = span F := h.span_eq.symm
  -- the word at `N - 1` equals the word at `p` on a class that is not exceptional
  have hlast : ∀ {S : Finset ℤ} {f : ℤ → ℤ}, PeriodWords.PeriodExcept (span F - 1) p S f →
      (0 : ℤ) ∉ S → f p = f ((span F : ℤ) - 1) := by
    intro S f hf h0
    refine periodExcept_eq_of_dvd hf (by omega : 0 < p) (x := p) (y := (span F : ℤ) - 1)
      (by omega) (by linarith [hLZ]) (by omega) ⟨(span χ.D - 1 : ℤ), by linarith [hNZ]⟩ ?_
    simpa using h0
  have hWA : ∀ k : ℤ, 1 ≤ k → k < (span F : ℤ) → wordA F k = wordA (χ.ω.compose χ.D) k :=
    fun k h1 h2 => h.wordA_eq h1 h2
  have hWB : ∀ k : ℤ, 1 ≤ k → k < (span F : ℤ) → wordB F k = wordB (χ.ω.compose χ.D) k :=
    fun k h1 h2 => h.wordB_eq h1 h2
  cases hc : χ.ω.case
  · rw [hc] at htab
    obtain ⟨hA, hB, a1, bp⟩ := htab
    obtain ⟨c1, c2, c3, c4⟩ := hlegal.caps_a hD hc hph
    have e2 : wordB F 1 = 0 := by
      rw [hWB 1 (by omega) (by omega)]; exact c2
    have e3 : wordA F ((span F : ℤ) - 1) = 0 := by
      rw [hWA _ (by omega) (by omega)]
      have := c3
      rw [hwZ, hs] at this
      simpa using this
    have e4 := hlast hB (by simp) 
    refine ⟨0, 0, ?_, a1, e2, e3, ?_⟩
    · simp [CaseBits]
    · rw [← e4]; exact bp
  · rw [hc] at htab
    obtain ⟨hA, hB, ap, b1⟩ := htab
    obtain ⟨c1, c2, c3, c4⟩ := hlegal.caps_b hD hc hph
    have e1 : wordA F 1 = 1 := by
      rw [hWA 1 (by omega) (by omega)]; exact c2
    have e3 : wordB F ((span F : ℤ) - 1) = 1 := by
      rw [hWB _ (by omega) (by omega)]
      have := c3
      rw [hwZ, hs] at this
      simpa using this
    have e4 := hlast hA (by simp)
    refine ⟨1, 1, ?_, e1, b1, ?_, e3⟩
    · simp [CaseBits]
    · rw [← e4]; exact ap
  · rw [hc] at htab
    obtain ⟨hA, hB, a1, ap⟩ := htab
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hlegal.caps_c hD hc hph
    have e2 : wordB F 1 = 0 := by
      rw [hWB 1 (by omega) (by omega)]; exact c2
    have e3 : wordB F ((span F : ℤ) - 1) = 1 := by
      rw [hWB _ (by omega) (by omega)]
      have := c3
      rw [hwZ, hs] at this
      simpa using this
    have e4 := hlast hA (by simp)
    refine ⟨0, 1, ?_, a1, e2, ?_, e3⟩
    · simp [CaseBits]
    · rw [← e4]; exact ap
  · rw [hc] at htab
    obtain ⟨hA, hB, b1, bp⟩ := htab
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hlegal.caps_d hD hc hph
    have e1 : wordA F 1 = 1 := by
      rw [hWA 1 (by omega) (by omega)]; exact c2
    have e3 : wordA F ((span F : ℤ) - 1) = 0 := by
      rw [hWA _ (by omega) (by omega)]
      have := c3
      rw [hwZ, hs] at this
      simpa using this
    have e4 := hlast hB (by simp)
    refine ⟨1, 0, ?_, e1, b1, e3, ?_⟩
    · simp [CaseBits]
    · rw [← e4]; exact bp

end SmallOverlap
end SkewGluing
