/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.TopMatching
import SkewCoframeRigidity.Stationary.MatchingWiring
import SkewCoframeRigidity.FixedCap.CapDescent

/-!
# `sc:top-matching`

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:top-matching`.  Two connected coequal
diagrams of the same span `M` whose first proper row sits at `M - 1`, and which satisfy the two
endpoint equations
`[H^p Δ]_{M-1} = 0` and `∂_{H_{M-1}}([H^p Δ]_M - Δ_1 [H^p G]_{M-1}) = 0` for an integer `p ≥ 2`,
have highest strict components with the same least column, span, coframe and top quotient; their
defect has `∂_{H_{M-1}} Δ = 0` and `Δ_1 = 0`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem dS_zero_of_matched_g {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE) (hg : sD.c.g = sE.c.g) :
    dS (span D - 1) ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) = 0 := by
  rw [dS_difference_matched hs hm, hg, sub_self]; simp

theorem delta_one_zero {D E : BetaDiagram (n + 1)} (hs : span D = span E) {p : ℕ}
    {sD : TopSide D p} {sE : TopSide E p} (hm : Matched sD sE)
    (htq : topQuotient D = topQuotient E) (hg : sD.c.g = sE.c.g) :
    (coframe E - coframe D).coeff 1 = 0 := by
  have h := V_relation hs hm htq
  rw [hg, sub_self] at h
  simp only [Polynomial.coe_zero, mul_zero, map_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · exact absurd h sD.c.hk

/-- `sc:top-matching`. -/
theorem top_matching {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hn : 0 < n) (hs : span D = span E) (htD : TopRow D hn) (htE : TopRow E hn)
    {p : ℕ} (hp : 2 ≤ p) (htq : topQuotient D = topQuotient E)
    (h0 : PowerSeries.coeff (span D - 1)
      (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0)
    (h1 : dRaw (span D - 1) (PowerSeries.coeff (span D)
        (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) -
      (coframe E - coframe D).coeff 1 * PowerSeries.coeff (span D - 1)
        (letterSeries ^ p * (coframe D : PowerSeries CohField))) = 0) :
    ∃ (sD : TopSide D p) (sE : TopSide E p), Matched sD sE ∧ sD.c.g = sE.c.g ∧
      dS (span D - 1) ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) = 0 ∧
      (coframe E - coframe D).coeff 1 = 0 := by
  obtain ⟨sD⟩ := topSide_exists hD hn htD p
  obtain ⟨sE⟩ := topSide_exists hE hn htE p
  have hratio := ratio_eq_of_endpoint hs (by omega) sD sE h0
  obtain ⟨hL, hk⟩ := ratio_compare sD.c sE.c hp hratio
  have ha : sD.a = sE.a := by
    have h1 := sD.hsum; have h2 := sE.hsum; omega
  have hm : Matched sD sE := ⟨ha, hk, hL⟩
  have hg : sD.c.g = sE.c.g := by
    rcases Nat.lt_or_ge sD.c.L 2 with hl | hl
    · have : sD.c.L = 0 ∨ sD.c.L = 1 := by omega
      rcases this with h | h
      · rw [(unit_gk sD.c h).1, (unit_gk sE.c (hL ▸ h)).1]
      · rw [(cell_gk sD.c h).1, (cell_gk sE.c (hL ▸ h)).1]
    · have hV := V_eq_delta_one_mul_k hs hp hm htq hl h1
      rcases sD.c.shape with ⟨h0', _⟩ | ⟨_, n1, E1, hE1, hs1, hg1, hk1⟩
      · omega
      rcases sE.c.shape with ⟨h0', _⟩ | ⟨_, n2, F1, hF1, hs2, hg2, hk2⟩
      · omega
      have := component_rigidity_of_cap (FixedCap.capVanishing cellCap cellCap_isNorm
        cellCap_connected) E1 F1 hE1 hF1 (hs1.trans (hL.trans hs2.symm)) (hs1 ▸ hl)
        (hk1.trans (hk.trans hk2.symm)) (by
          rw [hg1, hg2, hk1, hs1]; exact hV)
      rw [← hg1, ← hg2]; exact this
  exact ⟨sD, sE, hm, hg, dS_zero_of_matched_g hs hm hg, delta_one_zero hs hm htq hg⟩

end SkewCoframeRigidity.Coframe
