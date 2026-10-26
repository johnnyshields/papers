/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordCoordinate
import SkewCornerDescent.Matrix.FiniteColumnReplacement

/-!
# Full original response word of the five-copy square source

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The original beta lists retain all six states and both unit vertices. Their
complete removed matrix has a nonzero off-diagonal coupling; its full inverse
produces the displayed response word. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial

/-- All original retained source rows, including both true ends. -/
def retainedRows : Fin 6 → Fin 8 := ![0,1,2,4,6,7]

/-- All original retained source columns, including both true ends. -/
def retainedCols : Fin 6 → Fin 8 := ![0,1,3,5,6,7]

/-- Both full original unit rows. -/
def removedRows : Fin 2 → Fin 8 := ![3,5]

/-- Both full original unit columns. -/
def removedCols : Fin 2 → Fin 8 := ![2,4]

/-- The retained and removed rows partition the complete original source. -/
noncomputable def rowFrame : (Fin 6 ⊕ Fin 2) ≃ Fin 8 :=
  Equiv.ofBijective (Sum.elim retainedRows removedRows) (by decide)

/-- The retained and removed columns partition the complete original source. -/
noncomputable def colFrame : (Fin 6 ⊕ Fin 2) ≃ Fin 8 :=
  Equiv.ofBijective (Sum.elim retainedCols removedCols) (by decide)

/-- The complete actual source Jacobi--Trudi matrix, under an arbitrary homomorphism. -/
noncomputable def sourceMatrix {R : Type*} [CommRing R] (f : Lambda →+* R) :
    Matrix (Fin 8) (Fin 8) R := (jtMatrix source.xi source.zeta).map f

/-- The literal full original matrix, before any normal or residue substitution. -/
theorem sourceMatrix_eq {R : Type*} [CommRing R] (f : Lambda →+* R) :
    sourceMatrix f = !![
      f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),f (X 15);
      f (X 1),f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 14);
      0,f (X 1),f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 11);
      0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9);
      0,0,0,f (X 1),f (X 2),f (X 4),f (X 7),f (X 8);
      0,0,0,0,1,f (X 2),f (X 5),f (X 6);
      0,0,0,0,0,f (X 1),f (X 4),f (X 5);
      0,0,0,0,0,0,f (X 1),f (X 2)] := by
  have hind : (Matrix.of fun i j : Fin 8 => source.xi i - source.zeta j) = !![
      2,5,6,8,9,11,14,15;
      1,4,5,7,8,10,13,14;
      -2,1,2,4,5,7,10,11;
      -4,-1,0,2,3,5,8,9;
      -5,-2,-1,1,2,4,7,8;
      -7,-4,-3,-1,0,2,5,6;
      -8,-5,-4,-2,-1,1,4,5;
      -11,-8,-7,-5,-4,-2,1,2] := by decide
  ext i j
  have hi := congrFun (congrFun hind i) j
  change source.xi i - source.zeta j = _ at hi
  change f (hh (source.xi i - source.zeta j)) = _
  rw [hi]
  fin_cases i <;> fin_cases j <;> norm_num [hh, hPos]

/-- The full retained beta block. -/
noncomputable def retainedMatrix {R : Type*} [CommRing R] (f : Lambda →+* R) :
    Matrix (Fin 6) (Fin 6) R := (sourceMatrix f).submatrix retainedRows retainedCols

/-- Every original incoming retained-to-unit coupling. -/
noncomputable def incomingMatrix {R : Type*} [CommRing R] (f : Lambda →+* R) :
    Matrix (Fin 6) (Fin 2) R := (sourceMatrix f).submatrix retainedRows removedCols

/-- Every original outgoing unit-to-retained coupling. -/
noncomputable def outgoingMatrix {R : Type*} [CommRing R] (f : Lambda →+* R) :
    Matrix (Fin 2) (Fin 6) R := (sourceMatrix f).submatrix removedRows retainedCols

/-- The whole removed source matrix, not its diagonal approximation. -/
noncomputable def removedMatrix {R : Type*} [CommRing R] (f : Lambda →+* R) :
    Matrix (Fin 2) (Fin 2) R := (sourceMatrix f).submatrix removedRows removedCols

/-- The removed unit vertices retain their full h-three interaction. -/
theorem removedMatrix_eq {R : Type*} [CommRing R] (f : Lambda →+* R) :
    removedMatrix f = !![1,f (X 3);0,1] := by
  rw [removedMatrix, sourceMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Both off-diagonal and diagonal entries of the true removed inverse. -/
theorem removedMatrix_inverse {R : Type*} [CommRing R] (f : Lambda →+* R) :
    (removedMatrix f)⁻¹ = !![1,-f (X 3);0,1] := by
  apply Matrix.inv_eq_left_inv
  rw [removedMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Genuine invertibility is produced from both complete explicit inverse identities. -/
@[instance_reducible]
noncomputable def removedMatrixInvertible {R : Type*} [CommRing R]
    (f : Lambda →+* R) : Invertible (removedMatrix f) where
  invOf := !![1,-f (X 3);0,1]
  invOf_mul_self := by
    rw [removedMatrix_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  mul_invOf_self := by
    rw [removedMatrix_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The true full original Schur complement on the retained source states. -/
noncomputable def sourceScalarMatrix {R : Type*} [CommRing R] (f : Lambda →+* R) :
    Matrix (Fin 6) (Fin 6) R :=
  retainedMatrix f - incomingMatrix f * (removedMatrix f)⁻¹ * outgoingMatrix f

/-- Every original row, column, and cross-unit coupling occurs in the exact frame. -/
theorem sourceMatrix_frame {R : Type*} [CommRing R] (f : Lambda →+* R) :
    (sourceMatrix f).submatrix rowFrame colFrame =
      Matrix.fromBlocks (retainedMatrix f) (incomingMatrix f)
        (outgoingMatrix f) (removedMatrix f) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The full reordered original determinant is exactly the true scalar determinant. -/
theorem sourceMatrix_frame_det {R : Type*} [CommRing R] (f : Lambda →+* R) :
    ((sourceMatrix f).submatrix rowFrame colFrame).det = (sourceScalarMatrix f).det := by
  let := removedMatrixInvertible f
  rw [sourceMatrix_frame, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  have hd : (removedMatrix f).det = 1 := by
    rw [removedMatrix_eq, Matrix.det_fin_two]
    simp
  rw [hd, one_mul]
  rfl

/-- Both actual caps and the exact original internal response word. -/
theorem sourceScalarMatrix_diagonal {R : Type*} [CommRing R] (f : Lambda →+* R) :
    (fun i : Fin 6 => sourceScalarMatrix f i i) =
      ![f (X 2),f (X 4),f (X 4)-f (X 2)^2,f (X 4)-f (X 2)^2,f (X 4),f (X 2)] := by
  funext i
  change (retainedMatrix f) i i -
    (∑ k : Fin 2, (∑ l : Fin 2, (incomingMatrix f) i l * (removedMatrix f)⁻¹ l k) *
      (outgoingMatrix f) k i) = _
  rw [removedMatrix_inverse]
  simp only [retainedMatrix, incomingMatrix, outgoingMatrix, sourceMatrix_eq]
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, Matrix.submatrix_apply, pow_two,
      retainedRows, retainedCols, removedRows, removedCols]

/-- All five selected original subdiagonals are the actual one-cell prime. -/
theorem sourceScalarMatrix_subdiagonal {R : Type*} [CommRing R] (f : Lambda →+* R) :
    ∀ i : Fin 5, sourceScalarMatrix f i.succ i.castSucc = f (X 1) := by
  intro i
  change (retainedMatrix f) i.succ i.castSucc -
    (∑ k : Fin 2, (∑ l : Fin 2, (incomingMatrix f) i.succ l * (removedMatrix f)⁻¹ l k) *
      (outgoingMatrix f) k i.castSucc) = _
  rw [removedMatrix_inverse]
  simp only [retainedMatrix, incomingMatrix, outgoingMatrix, sourceMatrix_eq]
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, Matrix.submatrix_apply,
      retainedRows, retainedCols, removedRows, removedCols]

/-- The actual internal states of the complete source scalar matrix. -/
noncomputable def sourceInternalResponse {R : Type*} [CommRing R] (f : Lambda →+* R)
    (i : Fin 4) : R := sourceScalarMatrix f i.castSucc.succ i.castSucc.succ

/-- The two original connector response functions, before residue specialization. -/
noncomputable def responseScalar {R : Type*} [CommRing R] (f : Lambda →+* R)
    (vertical : Bool) : R := if vertical then f (X 4) - f (X 2) ^ 2 else f (X 4)

/-- The actual join directions, in their original source order. -/
def sourceWordBits : Fin 4 → Bool := ![false,true,true,false]

/-- The whole two-copy window has the single horizontal connector. -/
def windowWordBits : Fin 1 → Bool := ![false]

/-- Full source elimination produces the exact four-position response word. -/
theorem sourceInternalResponse_actual_word {R : Type*} [CommRing R]
    (f : Lambda →+* R) (i : Fin 4) :
    sourceInternalResponse f i = responseScalar f (sourceWordBits i) := by
  have h := congrFun (sourceScalarMatrix_diagonal f) i.castSucc.succ
  fin_cases i <;> simpa [sourceInternalResponse, responseScalar, sourceWordBits] using h

/-- The complete original window Jacobi--Trudi matrix. -/
noncomputable def windowMatrix {R : Type*} [CommRing R] (f : Lambda →+* R) :
    Matrix (Fin 3) (Fin 3) R := (jtMatrix window.xi window.zeta).map f

/-- The full original window has the displayed actual horizontal response. -/
theorem windowInternalResponse_actual_word {R : Type*} [CommRing R]
    (f : Lambda →+* R) (i : Fin 1) :
    windowMatrix f 1 1 = responseScalar f (windowWordBits i) := by
  have hi : window.xi 1 - window.zeta 1 = 4 := by decide
  change f (hh (window.xi 1 - window.zeta 1)) = _
  rw [hi]
  fin_cases i
  norm_num [hh, hPos, responseScalar, windowWordBits]

/-- The actual source/window signed multiplicities, with every position counted. -/
def sourceClassExponent (vertical : Bool) : ℤ :=
  2 * ((Finset.univ.filter (fun i => sourceWordBits i = vertical)).card : ℤ) -
    5 * ((Finset.univ.filter (fun i => windowWordBits i = vertical)).card : ℤ)

/-- The exact two original exponents are minus one and four. -/
theorem sourceClassExponent_eq :
    sourceClassExponent false = -1 ∧ sourceClassExponent true = 4 := by decide

end SkewCornerDescent.SquareWordProfiles
