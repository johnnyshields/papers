/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SeamCoefficients
import SkewJacobiNegative.Gluing.RowTransport

/-!
# Retained units as an actual seam variable

Formalizes the unit-variable convention of `eq:unit-homogenization` in
`shields-2026-skew-class-inflation.tex`.  The faithful two-one affine lift
turns old units into the private generator indexed one; a proved inverse
substitution recovers the original complete-generator coefficients.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Gluing SkewJacobiNegative.Staircase
open SkewJacobiNegative.GeneralHessenberg

/-- Undo the positive odd-index generator embedding on its actual polynomial ring. -/
noncomputable def undoOdd : CompleteRing →+* CompleteRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j : ℕ+ => complete (((j.val : ℤ) - 1) / 2))

/-- The inverse substitution handles zero and negative original indices as well as positive ones. -/
theorem undoOdd_complete (k : ℤ) : undoOdd (complete (2 * k + 1)) = complete k := by
  by_cases hk : 0 ≤ k
  · have hp : 0 < 2 * k + 1 := by omega
    let j : ℕ+ := ⟨(2 * k + 1).toNat, by omega⟩
    have he : complete (2 * k + 1) = MvPolynomial.X j := complete_of_pos hp
    rw [he, undoOdd, MvPolynomial.eval₂Hom_X']
    congr 1
    dsimp [j]
    omega
  · rw [complete_of_neg (by omega), map_zero, complete_of_neg (by omega)]

/-- Preserve units as the univariate indeterminate in the full actual matrix. -/
noncomputable def unitEntry (k : ℤ) : Polynomial CompleteRing :=
  if k = 0 then Polynomial.X else Polynomial.C (complete k)

/-- The genuine full-board determinant with every unit retained independently. -/
noncomputable def unitSchur {n : ℕ} (P : Profile n) : Polynomial CompleteRing :=
  (Matrix.of fun i j => unitEntry (P.xi i - P.zeta j)).det

/-- The positive distinguished-seam variable of the lift is exactly the original unit variable. -/
theorem undoOdd_minimum_entry (k : ℤ) :
    Polynomial.map undoOdd (minimumPolynomial 1 (complete (2 * k + 1))) = unitEntry k := by
  rw [minimumPolynomial_complete]
  by_cases hk : k = 0
  · subst k
    simp [unitEntry]
  · have hne : 2 * k + 1 ≠ (1 : ℕ+).val := by norm_num; omega
    rw [ite_eq_right hne, Polynomial.map_C, undoOdd_complete, unitEntry, ite_eq_right hk]

/-- Exact polynomial identification of retained units with the lifted positive seam coordinate. -/
theorem unitSchur_eq_lifted_minimum {n : ℕ} (P : Profile n) :
    unitSchur P = Polynomial.map undoOdd
      (minimumPolynomial 1 (P.lift rowShiftTwoOne).toBetaDiagram.schur) := by
  change unitSchur P = (Polynomial.mapRingHom undoOdd)
    (minimumPolynomial 1 (P.lift rowShiftTwoOne).toBetaDiagram.schur)
  rw [BetaDiagram.schur, (minimumPolynomial 1).map_det,
    (Polynomial.mapRingHom undoOdd).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change unitEntry (P.xi i - P.zeta j) = Polynomial.map undoOdd
    (minimumPolynomial 1 (complete ((P.lift rowShiftTwoOne).xi i -
      (P.lift rowShiftTwoOne).zeta j)))
  have hi : (P.lift rowShiftTwoOne).xi i - (P.lift rowShiftTwoOne).zeta j =
      2 * (P.xi i - P.zeta j) + 1 := by
    rw [P.xi_lift, P.zeta_lift]
    norm_num [rowShiftTwoOne]
    ring
  rw [hi, undoOdd_minimum_entry]

/-- A seam contraction commutes with every legitimate affine profile lift. -/
theorem contract_lift {n : ℕ} (P : Profile (n + 1)) (s : RowShift) (c : Fin (n + 1)) :
    contract (P.lift s) c = (contract P c).lift s := by
  obtain ⟨hx, hz⟩ := contract_beta P c
  obtain ⟨hX, hZ⟩ := contract_beta (P.lift s) c
  apply Profile.eq_of_beta_eq
  · funext i
    rw [congrFun hX i, Profile.xi_lift, Profile.xi_lift, congrFun hx i]
  · funext i
    rw [congrFun hZ i, Profile.zeta_lift, Profile.zeta_lift, congrFun hz i]

/-- Mapping back the affine full determinant recovers exactly its original Schur polynomial. -/
theorem undoOdd_lifted_schur {n : ℕ} (P : Profile n) :
    undoOdd (P.lift rowShiftTwoOne).toBetaDiagram.schur = P.toBetaDiagram.schur := by
  rw [BetaDiagram.schur, undoOdd.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change undoOdd (complete ((P.lift rowShiftTwoOne).xi i -
      (P.lift rowShiftTwoOne).zeta j)) = complete (P.xi i - P.zeta j)
  have hi : (P.lift rowShiftTwoOne).xi i - (P.lift rowShiftTwoOne).zeta j =
      2 * (P.xi i - P.zeta j) + 1 := by
    rw [P.xi_lift, P.zeta_lift]
    norm_num [rowShiftTwoOne]
    ring
  rw [hi, undoOdd_complete]

/-- Constant-coefficient extraction is applied entrywise to the actual retained-unit determinant. -/
theorem unitSchur_constant_matrix {n : ℕ} (P : Profile n) :
    (unitSchur P).coeff 0 =
      (Matrix.of fun i j : Fin (n + 1) => (unitEntry (P.xi i - P.zeta j)).coeff 0).det := by
  let f : Polynomial CompleteRing →+* CompleteRing := Polynomial.constantCoeff
  change f (Matrix.of fun i j : Fin (n + 1) => unitEntry (P.xi i - P.zeta j)).det = _
  exact f.map_det _

/-- Evaluate the homogenized unit generator as the independent univariate coordinate. -/
noncomputable def unitEval : HomLambda →+* Polynomial CompleteRing :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun k : ℕ => unitEntry k)

/-- Homogenized complete entries retain exactly the original units. -/
theorem unitEval_hTilde (k : ℤ) : unitEval (hTilde k) = unitEntry k := by
  by_cases hk : k < 0
  · rw [hTilde, ite_eq_left hk, map_zero]
    simp [unitEntry, ne_of_lt hk, complete_of_neg hk]
  · rw [hTilde, ite_eq_right hk, unitEval, MvPolynomial.eval₂Hom_X']
    congr 1
    omega

/-- The retained-unit polynomial is the exact faithful homogenized-determinant specialization. -/
theorem unitEval_schurHom {n : ℕ} (P : Profile n) : unitEval P.schurHom = unitSchur P := by
  rw [Profile.schurHom, unitEval.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact unitEval_hTilde _

/-- Actual Schur equality supplies equality of the retained-unit polynomials. -/
theorem unitSchur_eq_of_schur_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) : unitSchur P = unitSchur Q := by
  have hn := Nat.succ.inj (P.toBetaDiagram.row_count_of_schur_eq Q.toBetaDiagram he)
  subst m
  have hh : P.schurHom = Q.schurHom := (Profile.schur_eq_iff_schurHom_eq P Q).mp
    (by simpa only [Profile.toBetaDiagram_schur] using he)
  rw [← unitEval_schurHom, ← unitEval_schurHom, hh]

end SkewClassInflation
