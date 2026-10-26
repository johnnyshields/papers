/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Three-variable alternant ratio algebra

Coefficient separation for `lem:three-variable-endpoint` in
`shields-2026-skew-jacobi-negative.tex`.  The alternant is specialized
at its first variable equal to one, and regarded as a polynomial in the
third variable over the rational polynomial ring in the second.
-/

namespace SkewJacobiNegative.ThreeVariableRatio
open Polynomial

/-- The specialized three-row alternant, written with its three nonzero coefficients. -/
noncomputable def alternant (a b : ℕ) : Polynomial (Polynomial ℚ) :=
  monomial 0 (X ^ (b + 1) - X ^ (a + b + 2)) +
    monomial (b + 1) (X ^ (a + b + 2) - 1) +
    monomial (a + b + 2) (1 - X ^ (b + 1))

@[simp] theorem alternant_coeff_zero (a b : ℕ) :
    (alternant a b).coeff 0 = (X : Polynomial ℚ) ^ (b + 1) * (1 - X ^ (a + 1)) := by
  simp only [alternant, coeff_add, coeff_monomial, ite_true,
    ite_eq_right (show b + 1 ≠ 0 by omega),
    ite_eq_right (show a + b + 2 ≠ 0 by omega), add_zero]
  simp only [pow_add, pow_one]
  ring

private theorem roots_separate_lt (a c t : ℕ) (ht : 0 < t) (hac : a < c) :
    (1 - (X : Polynomial ℚ) ^ (a + t + 1)) * (1 - X ^ (c + 1)) ≠
      (1 - X ^ (a + 1)) * (1 - X ^ (c + t + 1)) := by
  intro h
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff (a + 1)) h
  have h1 : a + t + 1 ≠ a + 1 := by omega
  have h2 : c + 1 ≠ a + 1 := by omega
  have h3 : c + t + 1 ≠ a + 1 := by omega
  have h4 : (a + t + 1) + (c + 1) ≠ a + 1 := by omega
  have h5 : (a + 1) + (c + t + 1) ≠ a + 1 := by omega
  have h0 : a + 1 ≠ 0 := by omega
  simp only [sub_mul, mul_sub, one_mul, mul_one, ← pow_add] at hc
  simp only [coeff_sub, coeff_one, coeff_X_pow, ite_eq_right h0,
    ite_eq_right h1.symm, ite_eq_right h2.symm, ite_eq_right h3.symm,
    ite_eq_right h4.symm, ite_eq_right h5.symm, ite_true] at hc
  norm_num at hc

/-- The two-variable boundary already fixes the first partition difference. -/
theorem roots_ratio_injective (a c t : ℕ) (ht : 0 < t)
    (h : (1 - (X : Polynomial ℚ) ^ (a + t + 1)) * (1 - X ^ (c + 1)) =
      (1 - X ^ (a + 1)) * (1 - X ^ (c + t + 1))) : a = c := by
  rcases lt_trichotomy a c with ha | ha | ha
  · exact False.elim (roots_separate_lt a c t ht ha h)
  · exact ha
  · apply False.elim
    apply roots_separate_lt c a t ht ha
    simpa only [mul_comm] using h.symm

private theorem alternant_separate_lt (a b c t : ℕ) (ht : 0 < t) (hbc : b < c) :
    alternant (a + t) b * alternant a c ≠
      alternant a b * alternant (a + t) c := by
  intro h
  have hc := congrArg (fun p : Polynomial (Polynomial ℚ) => p.coeff (b + 1)) h
  have hca : c + 1 ≠ b + 1 := by omega
  have hba : a + b + 2 ≠ b + 1 := by omega
  have hbt : a + t + b + 2 ≠ b + 1 := by omega
  have hcb : a + c + 2 ≠ b + 1 := by omega
  have hct : a + t + c + 2 ≠ b + 1 := by omega
  simp only [alternant, add_mul, mul_add, monomial_mul_monomial,
    coeff_add, coeff_monomial, Nat.zero_add, Nat.add_zero] at hc
  split_ifs at hc <;> try omega
  have hx : (X : Polynomial ℚ) ^ (a + c + 2) *
      (1 - X ^ t) * (1 - X ^ (b + 1)) = 0 := by
    simp only [pow_add, pow_one] at hc ⊢
    linear_combination hc
  have hX : (X : Polynomial ℚ) ≠ 0 := X_ne_zero
  have ht' : (1 - (X : Polynomial ℚ) ^ t) ≠ 0 := by
    intro hh
    have hcoeff := congrArg (fun p : Polynomial ℚ => p.coeff 0) hh
    simp only [coeff_sub, coeff_one_zero, coeff_X_pow,
      ite_eq_right (Ne.symm (Nat.ne_of_gt ht)), coeff_zero] at hcoeff
    norm_num at hcoeff
  have hb' : (1 - (X : Polynomial ℚ) ^ (b + 1)) ≠ 0 := by
    intro hh
    have hcoeff := congrArg (fun p : Polynomial ℚ => p.coeff 0) hh
    simp only [coeff_sub, coeff_one_zero, coeff_X_pow,
      ite_eq_right (show 0 ≠ b + 1 by omega), coeff_zero] at hcoeff
    norm_num at hcoeff
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hX) ht') hb') hx

/-- Cross-multiplied extended alternant ratios determine both partition parameters. -/
theorem alternant_ratio_injective (a b c d t : ℕ) (ht : 0 < t)
    (h : alternant (a + t) b * alternant c d = alternant a b * alternant (c + t) d) :
    a = c ∧ b = d := by
  have hc := congrArg (fun p : Polynomial (Polynomial ℚ) => p.coeff 0) h
  simp only [mul_coeff_zero, alternant_coeff_zero] at hc
  have hz : (X : Polynomial ℚ) ^ (b + 1) * X ^ (d + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ X_ne_zero)
  have hroots : (1 - (X : Polynomial ℚ) ^ (a + t + 1)) * (1 - X ^ (c + 1)) =
      (1 - X ^ (a + 1)) * (1 - X ^ (c + t + 1)) := by
    apply mul_left_cancel₀ hz
    linear_combination hc
  have ha := roots_ratio_injective a c t ht hroots
  subst c
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy b d with hb | hb | hb
  · exact False.elim (alternant_separate_lt a b d t ht hb h)
  · exact hb
  · apply False.elim
    apply alternant_separate_lt a d b t ht hb
    simpa only [mul_comm] using h.symm

end SkewJacobiNegative.ThreeVariableRatio
