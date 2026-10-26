/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCoreNormalConstant
import SkewCornerDescent.Matrix.SelectedCoreSeries

/-!
# Complete normal inverses and endpoint profiles of proper selected cores

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The original proper minor's produced inverse retains every off-diagonal entry.
Its complete normal endpoint profiles equal the constant embeddings of the
actual residue profiles; all positive normal jets vanish. Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual complete proper-minor inverse, not a diagonal substitute, is constant
in the normal chart. Its regularity is supplied by the selected component. -/
theorem selected_core_normal_inverse_constant {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    ((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map
      c.normalPolynomialSeries)⁻¹ =
    (((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map
      c.residueMap)⁻¹).map PowerSeries.C := by
  let := c.selectedMinorResidueInverse P hP
  let B := (jtMatrix (fun i : Fin n => P.xi i.succ)
    (fun j => P.zeta j.castSucc)).map c.residueMap
  let inv := Invertible.map (PowerSeries.C (R := OtherField c.top)).mapMatrix B
  let : Invertible (B.map PowerSeries.C) := inv
  rw [c.selected_core_normal_matrix_constant P hP]
  have h := map_invOf (PowerSeries.C (R := OtherField c.top)).mapMatrix B
  change (⅟B).map PowerSeries.C = ⅟(B.map PowerSeries.C) at h
  simpa only [Matrix.invOf_eq_nonsing_inv, B] using h.symm

/-- The full proper-core incoming row in the genuine normal series chart. -/
def selectedCoreNormalIncoming {n : ℕ} (P : Profile n) :
    Matrix Unit (Fin n) (PowerSeries (OtherField c.top)) :=
  (Matrix.of fun _ j => c.normalPolynomialSeries (hh (P.xi 0 - P.zeta j.castSucc))) *
    ((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map
      c.normalPolynomialSeries)⁻¹

/-- The full proper-core outgoing column in the genuine normal series chart. -/
def selectedCoreNormalOutgoing {n : ℕ} (P : Profile n) :
    Matrix (Fin n) Unit (PowerSeries (OtherField c.top)) :=
  ((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map
    c.normalPolynomialSeries)⁻¹ *
    (Matrix.of fun i _ => c.normalPolynomialSeries (hh (P.xi i.succ - P.zeta (Fin.last n))))

/-- Complete incoming coefficients retain every full inverse entry and have no
positive normal jets. No vector constancy premise is assumed. -/
theorem selected_core_normal_incoming {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    c.selectedCoreNormalIncoming P = (c.selectedCoreIncoming P hP).map PowerSeries.C := by
  unfold selectedCoreNormalIncoming selectedCoreIncoming
  simp only [Matrix.invOf_eq_nonsing_inv]
  rw [c.selected_core_normal_inverse_constant P hP]
  ext u i : 1
  let B := (jtMatrix (fun i : Fin n => P.xi i.succ)
    (fun j => P.zeta j.castSucc)).map c.residueMap
  change (∑ j : Fin n, c.normalPolynomialSeries (hh (P.xi 0 - P.zeta j.castSucc)) *
    PowerSeries.C (B⁻¹ j i)) =
      PowerSeries.C (∑ j : Fin n, c.residueMap (hh (P.xi 0 - P.zeta j.castSucc)) * B⁻¹ j i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [c.selected_core_normal_incoming_constant P hP j, map_mul]

/-- Complete outgoing coefficients satisfy the same full normal-constancy identity. -/
theorem selected_core_normal_outgoing {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    c.selectedCoreNormalOutgoing P = (c.selectedCoreOutgoing P hP).map PowerSeries.C := by
  unfold selectedCoreNormalOutgoing selectedCoreOutgoing
  simp only [Matrix.invOf_eq_nonsing_inv]
  rw [c.selected_core_normal_inverse_constant P hP]
  ext i u : 1
  let B := (jtMatrix (fun i : Fin n => P.xi i.succ)
    (fun j => P.zeta j.castSucc)).map c.residueMap
  change (∑ j : Fin n, PowerSeries.C (B⁻¹ i j) *
    c.normalPolynomialSeries (hh (P.xi j.succ - P.zeta (Fin.last n)))) =
      PowerSeries.C (∑ j : Fin n, B⁻¹ i j * c.residueMap (hh (P.xi j.succ - P.zeta (Fin.last n))))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [c.selected_core_normal_outgoing_constant P hP j, map_mul]

/-- Proper incoming profile in the endpoint variable, with full normal-series coefficients. -/
def selectedCoreNormalLeftPolynomial {n : ℕ} (P : Profile n) :
    Polynomial (PowerSeries (OtherField c.top)) :=
  ordinaryEndpointProfile (fun i : Fin n => (P.xi 0 - P.xi i.succ).toNat)
    (fun i => c.selectedCoreNormalIncoming P () i)

/-- Proper outgoing profile in the endpoint variable, with full normal-series coefficients. -/
def selectedCoreNormalRightPolynomial {n : ℕ} (P : Profile n) :
    Polynomial (PowerSeries (OtherField c.top)) :=
  ordinaryEndpointProfile (fun i : Fin n => (P.zeta i.castSucc - P.zeta (Fin.last n)).toNat)
    (fun i => c.selectedCoreNormalOutgoing P i ())

/-- Every endpoint coefficient of the proper incoming profile is its complete constant
normal series. This proves all normal orders at once. -/
theorem selected_core_normal_left_polynomial {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    c.selectedCoreNormalLeftPolynomial P =
      (c.selectedCoreLeftPolynomial P hP).map PowerSeries.C := by
  rw [selectedCoreNormalLeftPolynomial, c.selected_core_normal_incoming P hP]
  simp only [selectedCoreLeftPolynomial, ordinaryEndpointProfile, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_sum, Polynomial.map_monomial, Matrix.map_apply]

/-- The symmetric full outgoing profile has the same all-normal-order bridge. -/
theorem selected_core_normal_right_polynomial {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    c.selectedCoreNormalRightPolynomial P =
      (c.selectedCoreRightPolynomial P hP).map PowerSeries.C := by
  rw [selectedCoreNormalRightPolynomial, c.selected_core_normal_outgoing P hP]
  simp only [selectedCoreRightPolynomial, ordinaryEndpointProfile, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_sum, Polynomial.map_monomial, Matrix.map_apply]

end SkewCornerDescent.Matrix.SelectedCoordinate
