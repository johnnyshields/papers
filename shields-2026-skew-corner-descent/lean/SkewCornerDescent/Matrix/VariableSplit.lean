/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.SelectedCoordinate
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Splitting an actual selected generator

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`). The canonical polynomial ring is identified with polynomials in
one selected generator over the remaining original generators. Lower coefficients become
actual constants in this presentation. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Original polynomials in all generators other than the selected one. -/
abbrev OtherPolynomial (N : ℕ+) := MvPolynomial {j : ℕ+ // j ≠ N} ℚ

/-- The selected-generator splitting is an algebra equivalence, not a substitution
with a potentially nontrivial kernel. -/
noncomputable def splitGenerator (N : ℕ+) : Lambda ≃ₐ[ℚ] Polynomial (OtherPolynomial N) :=
  (MvPolynomial.renameEquiv ℚ (Equiv.optionSubtypeNe N).symm).trans
    (MvPolynomial.optionEquivLeft ℚ {j : ℕ+ // j ≠ N})

@[simp]
theorem splitGenerator_top (N : ℕ+) :
    splitGenerator N (MvPolynomial.X N) = Polynomial.X := by
  simp [splitGenerator]

@[simp]
theorem splitGenerator_other (N j : ℕ+) (hj : j ≠ N) :
    splitGenerator N (MvPolynomial.X j) = Polynomial.C (MvPolynomial.X ⟨j, hj⟩) := by
  simp [splitGenerator, Equiv.optionSubtypeNe_symm_of_ne hj]

/-- The univariate degree is exactly the degree in the selected original generator. -/
theorem splitGenerator_natDegree (N : ℕ+) (f : Lambda) :
    (splitGenerator N f).natDegree = f.degreeOf N :=
  (MvPolynomial.degreeOf_eq_natDegree N f).symm

/-- A polynomial omitting the selected generator is a genuine constant after splitting. -/
theorem splitGenerator_eq_constant (N : ℕ+) (f : Lambda) (h : N ∉ f.vars) :
    splitGenerator N f = Polynomial.C ((splitGenerator N f).coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  rw [splitGenerator_natDegree]
  apply Nat.eq_zero_of_le_zero
  rw [MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.mem_support_notMem_vars_zero hm h]

/-- Splitting the actual selected connected prime retains its full lower coefficient
and remainder, rather than imposing a new affine identity as an assumption. -/
theorem SelectedCoordinate.split_prime {D : Diagram} {hD : IsConnectedSkew D}
    (c : SelectedCoordinate D hD) :
    splitGenerator c.top (cellSchur D hD.1) =
      Polynomial.C ((splitGenerator c.top c.coefficient).coeff 0) * Polynomial.X +
      Polynomial.C ((splitGenerator c.top c.remainder).coeff 0) := by
  rw [c.prime_eq]
  simp only [affineCoordinate, map_add, map_mul, splitGenerator_top]
  conv_lhs =>
    rw [splitGenerator_eq_constant _ _ c.top_notMem_coefficient,
      splitGenerator_eq_constant _ _ c.top_notMem_remainder]

/-- The original nonzero selected top cofactor remains nonzero as a coefficient. -/
theorem SelectedCoordinate.split_coefficient_ne_zero {D : Diagram} {hD : IsConnectedSkew D}
    (c : SelectedCoordinate D hD) :
    (splitGenerator c.top c.coefficient).coeff 0 ≠ 0 := by
  intro h
  have he := splitGenerator_eq_constant c.top c.coefficient c.top_notMem_coefficient
  rw [h, Polynomial.C_0] at he
  exact c.coefficient_ne_zero ((splitGenerator c.top).injective (he.trans (map_zero _).symm))

end SkewCornerDescent.Matrix
