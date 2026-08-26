/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.AttractorPole

/-!
# Shifting the weight by a monomial

Clause 3 asserts that the defect constants do not move when the numerator does, so a
certificate that the clause-3 route is not vacuous has to exercise a **family** of weights
with `deg B_N` genuinely varying — a single weight, or several of one degree, says nothing
about the uniformity.  The cheapest such family over a fixed denominator pencil is
`B = t^k`, and this module supplies the two facts that make it computable.

Multiplying the weight by `t^k` shifts the coefficient sequence by `k` and multiplies the
residue amplitude of `prop:isolated-dominant-cancellation` by `t^k`:

## Main statements

* `ftCoeffPoly_X_pow` — `F_M^{(t^k)} = F_{M-k}^{(1)}`, and `0` below the shift.  The
  convolution recurrence defining `F_M` sees the weight only through `B.coeff M`, so this is
  a strong induction with the sum reindexed across the shift.
* `ftAmp_X_pow` — `𝒲_{t^k}(z,t) = t^k𝒲_1(z,t)`, since the cofactor does not
  see the weight at all.

## Implementation notes

Both hold for any denominator, so neither is tied to the Favard pencil that consumes them.
On the principal branch `t_+ = τ e^{iθ}` the second reads
`|W_k| = τ^k|W_1|` and `arg W_k = kθ + arg W_1`, which is where the numerator's own
`κ` of `eq:phase-derivative-bound` comes from: it is `k`, and it grows with the weight,
while `eq:linear-phase-variation` still holds at constants that do not.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`,
`eq:canonical-Laurent-factorization` in the service of `thm:main` clause 3.

## Tags

monomial shift, weight polynomial, defect
-/

namespace ForgacsTran

open Polynomial

/-- **The residue amplitude under a monomial weight.**  `ftCofactor` is built from the
denominator alone, so multiplying the weight by `t^k` multiplies
`𝒲 = -B(t)/∂_tD(t)` by `t^k`. -/
theorem ftAmp_X_pow (Q : Polynomial ℂ) (r k : ℕ) (z t : ℂ) :
    ftAmp Q (X ^ k) r z t = t ^ k * ftAmp Q 1 r z t := by
  rw [ftAmp, ftAmp, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  ring

/-- **The coefficient sequence under a monomial weight.**  `B = t^k` shifts the sequence by
`k`: the convolution recurrence of `prop:isolated-dominant-cancellation` reads the weight only
through `B.coeff M`, and `(t^k).coeff M` is `(1).coeff (M-k)` once `k ≤ M`.  Below the shift
the sequence vanishes.

The proof is a strong induction on `M`; the sum over `range M` splits at `k`, its lower part
vanishes by the inductive hypothesis, and its upper part reindexes onto `range (M-k)`. -/
theorem ftCoeffPoly_X_pow (Q : Polynomial ℂ) (r k : ℕ) :
    ∀ M : ℕ, ftCoeffPoly Q (X ^ k) r M
      = if M < k then 0 else ftCoeffPoly Q 1 r (M - k) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rw [ftCoeffPoly_eq]
    by_cases hMk : M < k
    · rw [if_pos hMk]
      have hcoeff : (X ^ k : Polynomial ℂ).coeff M = 0 := by
        rw [Polynomial.coeff_X_pow, if_neg (by omega)]
      have hsum : ∑ i ∈ Finset.range M, ftDenCoeff Q r (M - i)
          * ftCoeffPoly Q (X ^ k) r i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hiM : i < M := Finset.mem_range.1 hi
        rw [ih i hiM, if_pos (by omega), mul_zero]
      rw [hcoeff, hsum, map_zero, sub_zero, mul_zero]
    · push Not at hMk
      rw [if_neg (by omega), ftCoeffPoly_eq Q 1 r (M - k)]
      have hcoeff : (X ^ k : Polynomial ℂ).coeff M = (1 : Polynomial ℂ).coeff (M - k) := by
        rw [Polynomial.coeff_X_pow, Polynomial.coeff_one]
        by_cases h : M = k
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      have hlow : ∑ i ∈ Finset.Ico 0 k, ftDenCoeff Q r (M - i)
          * ftCoeffPoly Q (X ^ k) r i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hik : i < k := (Finset.mem_Ico.1 hi).2
        rw [ih i (by omega), if_pos hik, mul_zero]
      have hcons := Finset.sum_Ico_consecutive
        (fun i => ftDenCoeff Q r (M - i) * ftCoeffPoly Q (X ^ k) r i)
        (Nat.zero_le k) hMk
      have hsum : ∑ i ∈ Finset.range M, ftDenCoeff Q r (M - i)
            * ftCoeffPoly Q (X ^ k) r i
          = ∑ j ∈ Finset.range (M - k), ftDenCoeff Q r (M - k - j)
            * ftCoeffPoly Q 1 r j := by
        rw [Finset.range_eq_Ico, ← hcons, hlow, zero_add, Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjM : j < M - k := Finset.mem_range.1 hj
        rw [ih (k + j) (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
          ← Nat.sub_sub]
      rw [hcoeff, hsum]

end ForgacsTran
