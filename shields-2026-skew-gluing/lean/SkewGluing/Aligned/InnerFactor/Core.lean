import SkewGluing.Aligned.InnerFactor.AgreeOrd
import SkewGluing.Aligned.InnerFactor.AgreeD
import SkewGluing.Aligned.InnerFactor.Period

/-!
# The inner factor of a divisible chart: the case of `ω` not of case (c)

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`).

Let `F = D ∘_ω E = C ∘_η B` with `ω`, `η` legal, `q` the period of `ω`, `Q = a q` that of `η`,
`a ≥ 2`.  The span laws give `N_D = a + b + Δ` with `Δ = (N_C - 1) a`, `0 ≤ b < a`, and the width
of `η` is `b q + w`.  The windows of `B` repeat the diagonals `[b, a - 1]` of `D` `Δ`
diagonals later (`PerData`, `FactorData`), the inner factor `V = innerFactor D a b Δ z₁` has the
first `a q` diagonals of `D ∘_ω E` and, from the diagonal `b q + w` on, a translate of its last
ones, so `B` and `V ∘_ω E` have the same two windows and are translates.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace MarkedInner

variable {ω η : MarkedInner} {D C : Diagram}

theorem IsLegal.diag_w_singleton (hη : η.IsLegal) :
    diagLo η.E (minContent η.E + η.widthZ) = diagHi η.E (minContent η.E + η.widthZ) := by
  by_cases hW : η.W = ∅
  · have he : η.IsLegalEmpty := ⟨hη, hW⟩
    rw [he.width_zero, add_zero]
    have hs := isConnectedSkew_iff_diagonal.mp hη.1.1
    exact hs.2.2.2.2 _ (minContent_mem hη.1.1.2.1) (Or.inl (fun hm => by
      have := minContent_le hm; omega))
  · have hl : η.IsLegalNonempty := ⟨hη, Finset.nonempty_iff_ne_empty.mpr hW⟩
    have := hl.lo_w_eq_hi_w
    exact this

/-- The numbers of `prop:gluing-divisible`: `r = N_D`, `r' = N_C`, `Q = a q` with `a ≥ 2`,
`w' = b q + w`, `0 ≤ b < a`, `r = (r' - 1) a + a + b`. -/
theorem exists_divisible_numbers (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D)
    (hC : IsConnectedSkew C) {u : ℤ × ℤ}
    (hFG : ω.compose D = translate u (η.compose C)) (hlt : ω.period < η.period)
    (hdiv : ω.period ∣ η.period) :
    ∃ a b Δ : ℤ, 2 ≤ a ∧ 0 ≤ b ∧ b < a ∧ 0 ≤ Δ ∧ η.period = a * ω.period ∧
      η.widthZ = b * ω.period + ω.widthZ ∧ (span D : ℤ) = a + b + Δ ∧
      Δ * ω.period = ((span C : ℤ) - 1) * η.period := by
  have hq := hω.period_pos
  have hQ := hη.period_pos
  have hwq : ω.widthZ < ω.period := hω.2.2.1.2
  have hwq' : η.widthZ < η.period := hη.2.2.1.2
  have hw0 : 0 ≤ ω.widthZ := by unfold widthZ; positivity
  have hw0' : 0 ≤ η.widthZ := by unfold widthZ; positivity
  obtain ⟨a, ha⟩ := hdiv
  have haQ : η.period = a * ω.period := by rw [ha]; ring
  have hsp1 := span_compose hD hω
  have hsp2 := span_compose hC hη
  have hsp3 : span (ω.compose D) = span (η.compose C) := by
    rw [hFG, span_translate]
  rw [hsp3] at hsp1
  have hr' : 1 ≤ (span C : ℤ) := by
    have := span_eq_of_isConnectedSkew hC
    have := minContent_le (maxContent_mem hC.2.1)
    omega
  have hmain : ((span D : ℤ) - (span C : ℤ) * a) * ω.period = η.widthZ - ω.widthZ := by
    unfold widthZ at *
    rw [haQ] at hsp2
    nlinarith
  set b := (span D : ℤ) - (span C : ℤ) * a with hbdef
  have ha2 : 2 ≤ a := by
    by_contra hn
    have : a ≤ 1 := by omega
    have := mul_le_mul_of_nonneg_right this hq.le
    omega
  have hb0 : 0 ≤ b := by
    by_contra hn
    have : b ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_right this hq.le
    omega
  have hba : b < a := by
    by_contra hn
    have : a ≤ b := by omega
    have := mul_le_mul_of_nonneg_right this hq.le
    omega
  refine ⟨a, b, ((span C : ℤ) - 1) * a, ha2, hb0, hba, ?_, haQ, ?_, ?_, ?_⟩
  · have : 0 ≤ a := by omega
    nlinarith
  · omega
  · rw [hbdef]; ring
  · rw [haQ]; ring

end MarkedInner

end SkewGluing
