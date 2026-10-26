/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.ThreeVariableEndpoints
import SkewJacobiNegative.ThreeVariableRatio

/-!
# Faithful ratio separation for three-variable alternants

The coefficient argument in `lem:three-variable-endpoint` of
`shields-2026-skew-jacobi-negative.tex`, applied to the actual power determinant.
-/

namespace SkewJacobiNegative

/-- Specialize the first alphabet letter to one and retain the other two. -/
noncomputable def alternantTwoVariableMap : MvPolynomial (Fin 3) ℚ →+*
    Polynomial (Polynomial ℚ) :=
  MvPolynomial.eval₂Hom (algebraMap ℚ (Polynomial (Polynomial ℚ)))
    ![1, Polynomial.C Polynomial.X, Polynomial.X]

/-- The explicit three coefficients are the actual specialized alternant. -/
theorem threeAlternant_specialization (a b : ℕ) :
    alternantTwoVariableMap (threeAlternant a b) =
      ThreeVariableRatio.alternant a b := by
  simp only [threeAlternant, threePowerDet, Matrix.det_fin_three, Matrix.of_apply]
  simp only [map_sub, map_add, map_mul, map_pow, map_one,
    alternantTwoVariableMap, MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    ThreeVariableRatio.alternant, ← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.C_pow, map_sub, map_one, pow_zero, mul_one, one_mul]
  ring

/-- The cross-multiplied ratio determines the full two-parameter partition. -/
theorem threeAlternant_ratio_injective (a b c d t : ℕ) (ht : 0 < t)
    (h : threeAlternant (a + t) b * threeAlternant c d =
      threeAlternant a b * threeAlternant (c + t) d) : a = c ∧ b = d := by
  have hm := congrArg alternantTwoVariableMap h
  simp only [map_mul, threeAlternant_specialization] at hm
  exact ThreeVariableRatio.alternant_ratio_injective a b c d t ht hm

/-- The same ratio separation holds for the actual two-part Schur polynomials. -/
theorem threeSchur_ratio_injective (a b c d t : ℕ) (ht : 0 < t)
    (h : threeSchur (a + t) b * threeSchur c d =
      threeSchur a b * threeSchur (c + t) d) : a = c ∧ b = d := by
  apply threeAlternant_ratio_injective a b c d t ht
  rw [← threeSchur_mul_vandermonde, ← threeSchur_mul_vandermonde,
    ← threeSchur_mul_vandermonde, ← threeSchur_mul_vandermonde]
  calc
    _ = (threeSchur (a + t) b * threeSchur c d) * threeVandermonde ^ 2 := by ring
    _ = (threeSchur a b * threeSchur (c + t) d) * threeVandermonde ^ 2 := by rw [h]
    _ = _ := by ring

namespace BetaDiagram

set_option maxHeartbeats 800000 in
-- Finite-specialization homomorphisms expose nested coefficient-ring instances.
set_option backward.isDefEq.respectTransparency false in
/-- A nonsymmetric dense three-row endpoint difference survives three variables. -/
theorem threeVariable_endpointDifference_ne_zero (D : BetaDiagram 3)
    (hD : D.Dense) (hS : ¬ D.Symmetric) (t : ℤ) (ht : 0 < t) :
    threeVariableSpecialization (D.endpointDifference t ht) ≠ 0 := by
  intro hz
  have he : threeVariableSpecialization (D.extendTop t ht).schur =
      threeVariableSpecialization (D.extendBottom t ht).schur := by
    simpa only [endpointDifference, map_sub, sub_eq_zero] using hz
  have hf := (D.dense_three_top_factorization hD t ht).symm.trans
    ((congrArg (fun p : MvPolynomial (Fin 3) ℚ => p * threeVandermonde ^ 2) he).trans
      (D.dense_three_bottom_factorization hD t ht))
  have hx : (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 :
      MvPolynomial (Fin 3) ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1))
      (MvPolynomial.X_ne_zero 2)
  have hr :
      threeAlternant (D.threeUpperA + t.toNat) D.threeUpperB *
          threeAlternant D.threeLowerA D.threeLowerB =
        threeAlternant D.threeUpperA D.threeUpperB *
          threeAlternant (D.threeLowerA + t.toNat) D.threeLowerB := by
    apply mul_left_cancel₀ (pow_ne_zero D.threeCommonPower hx)
    simpa only [mul_assoc] using hf
  have hp := threeAlternant_ratio_injective D.threeUpperA D.threeUpperB
    D.threeLowerA D.threeLowerB t.toNat (by omega) hr
  exact hS (D.symmetric_of_three_parameters_eq hp.1 hp.2)

end BetaDiagram


end SkewJacobiNegative
