/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/PolynomialReadings.lean

import SkewJacobiNegative.BetaDiagrams
import SkewJacobiNegative.Base.MongeInitialCoefficients

/-!
# Actual determinant leading readings

Formalizes the minimum-square reading and nonvanishing in
`lem:polynomial-readings` of `shields-2026-skew-cofactor-independence.tex`.
Faithful coefficient extension preserves supports and initial components, so
these are readings of the actual rational determinant, not of a surrogate.
Sorry-free.
-/

namespace SkewJacobiNegative

open scoped BigOperators

/-- Coefficient extension is pointwise integer-to-rational casting. -/
theorem integerLift_coeff (p : Base.CompleteRing) (d : ℕ+ →₀ ℕ) :
    (integerLift p).coeff d = (p.coeff d : ℚ) :=
  MvPolynomial.coeff_map (Int.castRingHom ℚ) p d

/-- Faithful coefficient extension preserves every occupied monomial. -/
theorem integerLift_support (p : Base.CompleteRing) : (integerLift p).support = p.support := by
  apply MvPolynomial.support_map_of_injective
  intro a b h
  change (a : ℚ) = (b : ℚ) at h
  exact_mod_cast h

/-- The finite support minimum is unchanged by coefficient extension. -/
theorem integerLift_leastWeight (w : ℕ+ → ℝ) (p : Base.CompleteRing) :
    Base.leastWeight w (integerLift p) = Base.leastWeight w p := by
  unfold Base.leastWeight
  simp only [integerLift_support]

/-- Rational extension commutes with genuine weighted homogeneous components. -/
theorem integerLift_component (w : ℕ+ → ℝ) (a : ℝ) (p : Base.CompleteRing) :
    MvPolynomial.weightedHomogeneousComponent w a (integerLift p) =
      integerLift (MvPolynomial.weightedHomogeneousComponent w a p) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent, integerLift_coeff]
  split_ifs <;> simp

/-- Initial forms retain their full polynomial coefficients across the representation seam. -/
theorem integerLift_initialForm (w : ℕ+ → ℝ) (p : Base.CompleteRing) :
    Base.initialForm w (integerLift p) = integerLift (Base.initialForm w p) := by
  unfold Base.initialForm
  rw [integerLift_leastWeight, integerLift_component]

namespace BetaDiagram

variable {n : ℕ}

/-- The same Jacobi--Trudi matrix before rational coefficient extension. -/
noncomputable def integerMatrix (D : BetaDiagram n) :
    Matrix (Fin n) (Fin n) Base.CompleteRing :=
  Matrix.of fun i j => Base.complete (D.row i - D.col j)

/-- The integer determinant whose faithful rational image is the actual Schur polynomial. -/
noncomputable def integerSchur (D : BetaDiagram n) : Base.CompleteRing := D.integerMatrix.det

/-- Negating the decreasing beta coordinates gives the copied increasing staircase convention. -/
theorem integerMatrix_eq_staircase (D : BetaDiagram n) :
    D.integerMatrix = Base.staircaseMatrix (fun i => -D.row i) (fun i => -D.col i) := by
  apply Matrix.ext
  intro i j
  change Base.complete (D.row i - D.col j) = Base.complete (-D.col j - -D.row i)
  congr 1
  ring

/-- The integral and rational matrix entries are identified, not merely their signs. -/
theorem matrix_eq_integerLift (D : BetaDiagram n) :
    D.matrix = D.integerMatrix.map integerLift := rfl

/-- The rational determinant is the faithful image of the integral one. -/
theorem schur_eq_integerLift (D : BetaDiagram n) : D.schur = integerLift D.integerSchur := by
  rw [schur, matrix_eq_integerLift, ← integerLift_det]
  rfl

/-- The copied row ordering follows from the actual strict beta order. -/
theorem neg_row_strictMono (D : BetaDiagram n) : StrictMono (fun i => -D.row i) := by
  intro i j hij
  have h := D.row_strictAnti hij
  dsimp
  omega

/-- The copied column ordering follows from the actual strict beta order. -/
theorem neg_col_strictMono (D : BetaDiagram n) : StrictMono (fun i => -D.col i) := by
  intro i j hij
  have h := D.col_strictAnti hij
  dsimp
  omega

/-- Nonempty diagonal rows supply the increasing matching, without a density hypothesis. -/
theorem neg_diagonal_feasible (D : BetaDiagram n) : ∀ i, -D.row i ≤ -D.col i := by
  intro i
  have h := D.row_nonempty i
  omega

/-- The actual integral determinant is nonzero at every valid beta diagram. -/
theorem integerSchur_ne_zero (D : BetaDiagram n) : D.integerSchur ≠ 0 := by
  unfold integerSchur
  rw [integerMatrix_eq_staircase]
  exact Base.monge_minor_ne_zero Base.squareWeight D.neg_row_strictMono
    D.neg_col_strictMono D.neg_diagonal_feasible

/-- Every actual beta-diagram Schur determinant is nonzero, including the empty determinant. -/
theorem schur_ne_zero (D : BetaDiagram n) : D.schur ≠ 0 := by
  rw [schur_eq_integerLift]
  intro h
  apply D.integerSchur_ne_zero
  apply integerLift_injective
  simpa using h

/-- The unique minimum-square initial polynomial is the product of the actual row generators. -/
theorem square_initialForm (D : BetaDiagram n) :
    Base.initialForm Base.squareWeight.generatorWeight D.schur =
      ∏ i, complete (D.row i - D.col i) := by
  rw [schur_eq_integerLift, integerLift_initialForm]
  unfold integerSchur
  rw [integerMatrix_eq_staircase,
    Base.monge_minor_initialForm Base.squareWeight D.neg_row_strictMono
      D.neg_col_strictMono D.neg_diagonal_feasible, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  unfold complete
  congr 2
  ring

/-- Exponents of the actual ordered row lengths; repeated lengths are retained with multiplicity. -/
noncomputable def diagonalExponent (D : BetaDiagram n) : ℕ+ →₀ ℕ :=
  Base.exponentVector
    (Base.increasingIndexList (fun i => -D.row i) (fun i => -D.col i))

/-- The exponent data agree with the manuscript's row-length reading. -/
theorem diagonalExponent_eq_rowLengths (D : BetaDiagram n) :
    D.diagonalExponent = Base.exponentVector (List.ofFn fun i => (D.rowLength i).toNat) := by
  unfold diagonalExponent Base.increasingIndexList
  congr 2
  funext i
  dsimp [rowLength]
  congr 1
  ring

/-- The square-initial row monomial has coefficient exactly one over the rationals. -/
theorem square_initial_coefficient (D : BetaDiagram n) :
    (Base.initialForm Base.squareWeight.generatorWeight D.schur).coeff D.diagonalExponent = 1 := by
  rw [schur_eq_integerLift, integerLift_initialForm, integerLift_coeff]
  unfold integerSchur diagonalExponent
  rw [integerMatrix_eq_staircase,
    Base.monge_minor_initial_coefficient Base.squareWeight _ _ D.neg_row_strictMono
      D.neg_col_strictMono D.neg_diagonal_feasible]
  norm_num

end BetaDiagram
end SkewJacobiNegative
