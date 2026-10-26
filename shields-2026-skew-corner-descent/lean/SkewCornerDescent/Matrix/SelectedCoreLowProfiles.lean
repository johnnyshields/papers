/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCoreSeries
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Proper selected-core jets inside full upper-block endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Full
later incoming couplings do not alter the first core's incoming coefficients;
full earlier outgoing couplings do not alter the last core's outgoing ones.
All other positions strictly beyond the selected span disappear from precisely
that low coefficient window. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The first incoming block is unchanged by a complete upper-block suffix. -/
theorem upper_block_incoming_head {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (A : Matrix ν ν F) (U : Matrix ν μ F) (B : Matrix μ μ F)
    (r : Matrix Unit ν F) (s : Matrix Unit μ F)
    [Invertible A] [Invertible B] [Invertible (Matrix.fromBlocks A U 0 B)] (i : ν) :
    (Matrix.fromCols r s * ⅟(Matrix.fromBlocks A U 0 B)) () (.inl i) = (r * ⅟A) () i := by
  rw [Matrix.invOf_fromBlocks_zero₂₁_eq, Matrix.fromCols_mul_fromBlocks]
  simp [Matrix.fromCols]

/-- The last outgoing block is unchanged by a complete upper-block prefix. -/
theorem upper_block_outgoing_tail {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (A : Matrix ν ν F) (U : Matrix ν μ F) (B : Matrix μ μ F)
    (r : Matrix ν Unit F) (s : Matrix μ Unit F)
    [Invertible A] [Invertible B] [Invertible (Matrix.fromBlocks A U 0 B)] (i : μ) :
    (⅟(Matrix.fromBlocks A U 0 B) * Matrix.fromRows r s) (.inr i) () = (⅟B * s) i () := by
  rw [Matrix.invOf_fromBlocks_zero₂₁_eq, Matrix.fromBlocks_mul_fromRows]
  change ((0 : Matrix μ ν F) * r + ⅟B * s) i () = _
  simp

private theorem ordinary_profile_sum_coeff {ι ν F : Type*}
    [Fintype ι] [Fintype ν] [CommRing F]
    (d : ι → ℕ) (e : ν → ℕ) (a : ι → F) (v : ι ⊕ ν → F)
    (N k : ℕ) (hk : k ≤ N) (he : ∀ i, N < e i) (ha : ∀ i, v (.inl i) = a i) :
    (ordinaryEndpointProfile (Sum.elim d e) v).coeff k =
      (ordinaryEndpointProfile d a).coeff k := by
  classical
  have hz (i) : e i ≠ k := by have := he i; omega
  simp [ordinaryEndpointProfile, Fintype.sum_sum_type, Polynomial.coeff_monomial, ha, hz]

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete incoming profile agrees with its proper selected core through
selected-span degree, provided every other literal row starts strictly later.
The suffix and its complete off-diagonal coupling are arbitrary. -/
theorem selected_core_left_low_coeff {ν : Type*} [Fintype ν] [DecidableEq ν]
    {n : ℕ} (P : Profile n) (hP : cellSchur D hD.1 = P.schur)
    (B : Matrix ν ν (OtherField c.top)) [Invertible B]
    (U : Matrix (Fin n) ν (OtherField c.top)) (s : Matrix Unit ν (OtherField c.top))
    (distance : ν → ℕ) (hd : ∀ i, (c.top : ℕ) < distance i)
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    letI := c.selectedMinorResidueInverse P hP
    let A := (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map c.residueMap
    let r := Matrix.of fun (_ : Unit) (j : Fin n) =>
      c.residueMap (hh (P.xi 0 - P.zeta j.castSucc))
    letI := Matrix.fromBlocksZero₂₁Invertible A U B
    (ordinaryEndpointProfile
      (Sum.elim (fun i : Fin n => (P.xi 0 - P.xi i.succ).toNat) distance)
      (fun i => (Matrix.fromCols r s * ⅟(Matrix.fromBlocks A U 0 B)) () i)).coeff k =
        (c.selectedCoreLeftPolynomial P hP).coeff k := by
  let := c.selectedMinorResidueInverse P hP
  let A := (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map c.residueMap
  let r := Matrix.of fun (_ : Unit) (j : Fin n) => c.residueMap (hh (P.xi 0 - P.zeta j.castSucc))
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  apply ordinary_profile_sum_coeff _ distance _ _ (c.top : ℕ) k hk hd
  intro i
  exact upper_block_incoming_head A U B r s i

/-- The complete outgoing profile has the symmetric low selected-core jet;
all original earlier couplings remain in the upper-block matrix. -/
theorem selected_core_right_low_coeff {ν : Type*} [Fintype ν] [DecidableEq ν]
    {n : ℕ} (P : Profile n) (hP : cellSchur D hD.1 = P.schur)
    (A : Matrix ν ν (OtherField c.top)) [Invertible A]
    (U : Matrix ν (Fin n) (OtherField c.top)) (r : Matrix ν Unit (OtherField c.top))
    (distance : ν → ℕ) (hd : ∀ i, (c.top : ℕ) < distance i)
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    letI := c.selectedMinorResidueInverse P hP
    let B := (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map c.residueMap
    let s := Matrix.of fun (i : Fin n) (_ : Unit) =>
      c.residueMap (hh (P.xi i.succ - P.zeta (Fin.last n)))
    letI := Matrix.fromBlocksZero₂₁Invertible A U B
    (ordinaryEndpointProfile
      (Sum.elim distance (fun i : Fin n => (P.zeta i.castSucc - P.zeta (Fin.last n)).toNat))
      (fun i => (⅟(Matrix.fromBlocks A U 0 B) * Matrix.fromRows r s) i ())).coeff k =
        (c.selectedCoreRightPolynomial P hP).coeff k := by
  classical
  let := c.selectedMinorResidueInverse P hP
  let B := (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map c.residueMap
  let s := Matrix.of fun (i : Fin n) (_ : Unit) =>
    c.residueMap (hh (P.xi i.succ - P.zeta (Fin.last n)))
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  have hz (i) : distance i ≠ k := by have := hd i; omega
  have htail (i : Fin n) :
      (⅟(Matrix.fromBlocks A U 0 B) * Matrix.fromRows r s) (.inr i) () =
        c.selectedCoreOutgoing P hP i () := upper_block_outgoing_tail A U B r s i
  simp only [ordinaryEndpointProfile, Fintype.sum_sum_type]
  simp only [selectedCoreRightPolynomial, ordinaryEndpointProfile,
    Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Sum.elim_inl, Sum.elim_inr, hz, ite_false,
    Finset.sum_const_zero, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact htail i
  · rfl

end SelectedCoordinate
end SkewCornerDescent.Matrix
