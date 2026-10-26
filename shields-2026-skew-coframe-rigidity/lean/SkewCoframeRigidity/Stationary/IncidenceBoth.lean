/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.NeitherCase

/-!
# Both diagrams have a proper row at `M - 1`

Formalizes the «maximal-row incidence» step of `shields-2026-skew-coframe-rigidity.tex`,
`sc:positive-power`: for a distinct coequal pair satisfying the one-power equation, both proper row
sets contain `M - 1`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The two retained endpoint equations of the one-power equation, in the form used by
`top_matching`. -/
theorem endpoints_diagrams {D E : BetaDiagram (n + 1)} (hs : span D = span E) (hM : 3 ≤ span D)
    (hd : ∀ k ≤ span D, (defect D E).coeff k = 0) {p : ℕ} (P Q : ℚ[X])
    (heq : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) +
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) * potential P Q) = 0) :
    PowerSeries.coeff (span D - 1)
        (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0 ∧
      PowerSeries.coeff (span D) (letterSeries ^ p *
        ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) -
        (coframe E - coframe D).coeff 1 * PowerSeries.coeff (span D - 1)
          (letterSeries ^ p * (coframe D : PowerSeries CohField)) = 0 := by
  have := endpoints_of_powerEquation (span D) p (by omega) (coframe D) (coframe E) letterSeries
    (coframe_coeff_zero D) (coframe_coeff_zero E) (potential P Q) hd (heq _ (by omega))
    (heq _ (by omega))
  exact this

theorem incidence_both {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hn : 0 < n) (hs : span D = span E) (hM : 3 ≤ span D)
    (hcf : coframe D ≠ coframe E) (hDdeg : 0 < (coframe D).natDegree)
    (hcop : IsCoprime (coframe D) (coframe E))
    (hd : ∀ k ≤ span D, (defect D E).coeff k = 0) {p : ℕ} (hp : 2 ≤ p) (P Q : ℚ[X]) (hQ : Q ≠ 0)
    (heq : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) +
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) * potential P Q) = 0) :
    TopRow D hn ∧ TopRow E hn := by
  obtain ⟨h0, h1⟩ := endpoints_diagrams hs hM hd P Q heq
  by_cases htD : TopRow D hn <;> by_cases htE : TopRow E hn
  · exact ⟨htD, htE⟩
  · exfalso
    exact mixed_absurd' hD hn (dS_coframe_eq_zero hE hn htE) hs htD
      hp h0
  · exfalso
    exact mixed_absurd hE hn (dS_coframe_eq_zero hD hn htD) hs htE hp h0
  · exfalso
    have dG := dS_coframe_eq_zero hD hn htD
    have dC := dS_coframe_eq_zero hE hn htE
    rw [← hs] at dC
    refine neither_absurd_poly (span D) hM (coframe D) (coframe E) (coframe_coeff_zero D)
      (coframe_coeff_zero E) (natDegree_coframe_le D) (hs ▸ natDegree_coframe_le E) hDdeg hcop hcf
      dG dC hd (by omega) P Q hQ heq

end SkewCoframeRigidity.Coframe
