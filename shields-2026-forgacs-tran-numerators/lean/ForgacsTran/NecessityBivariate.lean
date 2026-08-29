/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.Necessity
import ForgacsTran.LaurentReduction

/-!
# The necessity statement in the paper's numerator vocabulary

`Necessity.not_exists_uniform_exceptional_bound` quantifies over numerators as
coefficient *sequences* — `prop:initial-data`'s reading, where properness is
`N_m = 0` for `m ≥ max{deg Q, r}`.  `thm:main` quantifies over the bivariate
polynomial `N ∈ ℝ[t,z]` itself, carried into the recurrence by `swapVars`, and
that is the form `Bridge.FTInputs.ofBivariateNumerator` and
`Main.main_bound_ofBivariateNumerator` consume.  This module states the negation
against that object, so it refutes the uniform-in-numerator reading of the
paper's own theorem with no translation step left to the reader.

## Main statements

* `swapVars_map_C` — the exchange of indeterminates on a numerator constant in
  `t`.  `N(t,z) = R(z)` is `R.map C` read in `ℝ[t][z]`, and its exchange is the
  `t`-constant `C R`, so the recurrence it drives has right-hand side
  `[m = 0]·R`.  This is `LaurentReduction.swapVars_C` in the other direction.
* `not_exists_uniform_exceptional_bound_bivariate` — for an admissible pencil
  `Q(t) + z t^r` there is no constant bounding the zeros of the coefficient
  polynomials off `posRay`, uniformly over nonzero proper bivariate numerators.

## Implementation notes

The numerator hypotheses are `thm:main`'s verbatim: `N ≠ 0` and
`deg_t N < max{deg Q, r}`, the latter as
`∀ β, (N.coeff β).degree < max Q.natDegree r`, with `N.coeff β ∈ ℝ[t]` the
coefficient of `z^β`.  The witness `N = R.map C` is constant in `t`, so every
`N.coeff β` is a constant and properness needs only `max{deg Q, r} ≥ 1`, which
`r ≥ 1` already gives.

`r ≥ 1` and `Q(0) ≠ 0` are all that is consumed; `eq:Q-hypotheses` and the
paper's `max{deg Q, r} > 1` are not needed for the negative half.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Introduction»
(`sec:introduction`, `eq:P-generating-intro`), in the numerator vocabulary of
«Main theorem» (`subsec:intro-main`, `thm:main`).

## Tags

necessity, numerator dependence, uniform bound, exchange of indeterminates
-/

open Polynomial

namespace ForgacsTran

variable {K : Type*} [Field K]

/-- Paper `sec:reduction` (supporting) — the exchange of indeterminates on a
numerator constant in `t`.  Read in `K[t][z]`, the numerator `N(t,z) = R(z)` is
`R.map C`; exchanging gives the `t`-constant `C R`, whose `t`-coefficients are
`R` at `m = 0` and `0` after.  The companion of `swapVars_C`, which runs the
other way. -/
theorem swapVars_map_C (R : Polynomial K) :
    swapVars (R.map (Polynomial.C : K →+* Polynomial K)) = Polynomial.C R := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial (a := Polynomial.C a),
        ← Polynomial.C_mul_X_pow_eq_monomial (a := a), map_mul, map_pow, swapVars_C, swapVars_X,
        Polynomial.map_C, map_mul, map_pow]

/-- Paper `sec:introduction` (supporting) — the `t`-coefficients of the exchanged
constant numerator: `R` at index `0`, and `0` after.  This is the right-hand side
`dvd_of_denomConv_const` consumes. -/
theorem coeff_swapVars_map_C (R : Polynomial K) (m : ℕ) :
    (swapVars (R.map (Polynomial.C : K →+* Polynomial K))).coeff m
      = if m = 0 then R else 0 := by
  rw [swapVars_map_C, Polynomial.coeff_C]

open scoped Classical in
/-- **`sec:introduction`, the necessity statement against `thm:main`'s own
numerator.**  For an admissible pencil `Q(t) + z t^r` — `r ≥ 1` and `Q(0) ≠ 0` —
no constant bounds the zeros of the coefficient polynomials off the positive
ray, uniformly over the nonzero proper bivariate numerators `thm:main` admits.

Given a candidate `C`, the witness is `N(t,z) = ∏_{j=1}^{C+1}(z+j)`: nonzero,
constant in `t` and hence proper for every admissible pencil, and its
coefficient sequence already carries `C+1` exceptional zeros at `m = 0`.  The
divisibility is `Reduction.dvd_of_denomConv_const`, the count is
`Necessity.le_card_exceptionalRoots_negRootPoly`, and the passage to the complex
count is `Necessity.card_exceptionalRoots_le_map`. -/
theorem not_exists_uniform_exceptional_bound_bivariate (Q : Polynomial ℝ) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) :
    ¬ ∃ C : ℕ, ∀ (N : (Polynomial ℝ)[X]) (P : ℕ → Polynomial ℝ),
        N ≠ 0 →
        (∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) →
        (∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m) →
        ∀ m, P m ≠ 0 →
          (exceptionalRoots ((P m).map (algebraMap ℝ ℂ)) posRay).card ≤ C := by
  rintro ⟨C, hC⟩
  have hd : IsUnit (ftDenom Q r 0) := isUnit_ftDenom_zero hr hQ0
  set R : Polynomial ℝ := negRootPoly (C + 1) with hR
  set N : (Polynomial ℝ)[X] := R.map (Polynomial.C : ℝ →+* Polynomial ℝ) with hN
  -- the witness is nonzero
  have hNne : N ≠ 0 := by
    rw [hN, Ne, Polynomial.map_eq_zero_iff (Polynomial.C : ℝ →+* Polynomial ℝ).injective]
    exact negRootPoly_ne_zero (C + 1)
  -- and proper: it is constant in `t`, and `max {deg Q, r} ≥ r ≥ 1`
  have hmaxpos : 0 < max Q.natDegree r := lt_of_lt_of_le hr (le_max_right _ _)
  have hmaxW : (0 : WithBot ℕ) < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    exact_mod_cast hmaxpos
  have hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ) := by
    intro β
    rw [hN, Polynomial.coeff_map]
    exact lt_of_le_of_lt Polynomial.degree_C_le hmaxW
  -- the coefficient sequence it drives
  obtain ⟨P, hP⟩ := exists_denomConv_eq hd (fun m => if m = 0 then R else 0)
  have hPswap : ∀ m, denomConv (ftDenom Q r) P m = (swapVars N).coeff m := by
    intro m; rw [hP m, hN, coeff_swapVars_map_C]
  have hP0 : P 0 ≠ 0 := ne_zero_of_denomConv_const (negRootPoly_ne_zero (C + 1)) hP
  have hle := hC N P hNne hproper hPswap 0 hP0
  have hge := le_card_exceptionalRoots_negRootPoly hd (C + 1) hP hP0
  have hbridge := card_exceptionalRoots_le_map (P 0)
  omega

end ForgacsTran
