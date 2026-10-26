/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.RowTwo

/-!
# The branch `A < B` of the disconnected corner

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner, `A < B`).  With the two endpoint columns
`a = -z^A g / k_E` and `b = -z^B c / k_F`, the quadratic equation forces the coordinate `α_{F,p}`
to vanish; the only component for which it does is the two-cell row at `p = 2`, and then the span
three numerator `h₁² g₂ - 2 h₂²` of the other component must vanish.  Both are excluded by the
nonvanishing inputs.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries SkewCoframeRigidity SkewCoframeRigidity.Coframe
open Polynomial hiding coeff

variable {K : Type*} [Field K]

/-- The branch `A < B` of the quadratic equation is impossible: `α_{F,p} ≠ 0` unless `F` is the
two-cell row and `p = 2`, and the span three numerator of `E` is nonzero. -/
theorem lt_branch_false (h : ℕ → K) (M A B L R p : ℕ) (hp : 2 ≤ p) (hAB : A < B)
    (hAL : A + L + 1 = M) (hBR : B + R + 1 = M) (g c : K[X]) (kE kF : K)
    (hg0 : g.coeff 0 = 1) (hgdeg : 0 < L → ∀ j, L ≤ j → g.coeff j = 0)
    (hkE : kE = coeff L (seriesOf h * (g : K⟦X⟧))) (hkF : kF = coeff R (seriesOf h * (c : K⟦X⟧)))
    (hkE0 : kE ≠ 0) (hkF0 : kF ≠ 0)
    (heq : ∀ n < 2 * M, coeff n (defectExpr M p h
      (Polynomial.C (-1 / kE) * (Polynomial.X ^ A * g))
      (Polynomial.C (-1 / kF) * (Polynomial.X ^ B * c))) = 0)
    (hF : alphaOf h c p R ≠ 0 ∨ (p = 2 ∧ R = 2 ∧ c = 1))
    (hE : L = 3 → h 1 ^ 2 * g.coeff 2 ≠ 2 * h 2 ^ 2) : False := by
  have hlow : ∀ i < A, (Polynomial.C (-1 / kE) * (Polynomial.X ^ A * g)).coeff i = 0 := by
    intro i hi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
  have hAa : (Polynomial.C (-1 / kE) * (Polynomial.X ^ A * g)).coeff A ≠ 0 := by
    have := coeff_shift_poly (-1 / kE) A g 0
    rw [add_zero, hg0, mul_one] at this
    rw [this]; exact div_ne_zero (by norm_num) hkE0
  have hβ0 : (-1 / kF) ≠ 0 := div_ne_zero (by norm_num) hkF0
  have hk : (-1 / kF) * coeff R (seriesOf h * (c : K⟦X⟧)) = -1 := by
    rw [← hkF]; field_simp
  have hzero := alphaOf_eq_zero_of_low M A B R p hp (by omega) hAB (by omega) h _ c _ hlow hAa hβ0 hk
    (heq (M + A) (by omega))
  rcases hF with hF | ⟨rfl, rfl, rfl⟩
  · exact hF hzero
  · obtain ⟨s, rfl⟩ : ∃ s, M = s + 3 := ⟨M - 3, by omega⟩
    have hBs : B = s := by omega
    subst hBs
    have hk2 : kF = h 2 := by
      rw [hkF]; simp [coeff_seriesOf]
    have hβ : (-1 / kF) * h 2 = -1 := by rw [← hk2]; field_simp
    have hceq : (Polynomial.C (-1 / kF) * (Polynomial.X ^ B * (1 : K[X]))) =
        Polynomial.C (-1 / kF) * Polynomial.X ^ B := by rw [mul_one]
    rw [hceq] at heq
    have hkE' : (-1 / kE) * coeff (B + 2 - A) (seriesOf h * (g : K⟦X⟧)) = -1 := by
      have : B + 2 - A = L := by omega
      rw [this, ← hkE]; field_simp
    obtain ⟨hA1, hnum⟩ := rowTwo_exclusion B A (by omega) h g (-1 / kE) (-1 / kF) hg0
      (fun j hj => hgdeg (by omega) j (by omega)) hβ hkE' heq
    exact hE (by omega) hnum

theorem clippedOp_swap (M : ℕ) (a b : K[X]) (u : K⟦X⟧) :
    clippedOp M b a u = -clippedOp M a b u := by
  unfold clippedOp; ring

theorem defectExpr_swap (M p : ℕ) (h : ℕ → K) (a b : K[X]) :
    defectExpr M p h b a = -defectExpr M p h a b := by
  unfold defectExpr
  rw [clippedOp_swap M a b (seriesOf h ^ p), clippedOp_swap M a b (seriesOf h)]
  simp only [Polynomial.coe_neg]
  ring

/-- The branch `B < A` follows from the branch `A < B` by exchanging the two endpoints. -/
theorem gt_branch_false (h : ℕ → K) (M A B L R p : ℕ) (hp : 2 ≤ p) (hBA : B < A)
    (hAL : A + L + 1 = M) (hBR : B + R + 1 = M) (g c : K[X]) (kE kF : K)
    (hc0 : c.coeff 0 = 1) (hcdeg : 0 < R → ∀ j, R ≤ j → c.coeff j = 0)
    (hkE : kE = coeff L (seriesOf h * (g : K⟦X⟧))) (hkF : kF = coeff R (seriesOf h * (c : K⟦X⟧)))
    (hkE0 : kE ≠ 0) (hkF0 : kF ≠ 0)
    (heq : ∀ n < 2 * M, coeff n (defectExpr M p h
      (Polynomial.C (-1 / kE) * (Polynomial.X ^ A * g))
      (Polynomial.C (-1 / kF) * (Polynomial.X ^ B * c))) = 0)
    (hE : alphaOf h g p L ≠ 0 ∨ (p = 2 ∧ L = 2 ∧ g = 1))
    (hF : R = 3 → h 1 ^ 2 * c.coeff 2 ≠ 2 * h 2 ^ 2) : False := by
  refine lt_branch_false h M B A R L p hp hBA hBR hAL c g kF kE hc0 hcdeg hkF hkE hkF0 hkE0
    (fun n hn => ?_) hE hF
  rw [defectExpr_swap, map_neg, heq n hn, neg_zero]

end SkewCoframeRigidity.Unshifted
