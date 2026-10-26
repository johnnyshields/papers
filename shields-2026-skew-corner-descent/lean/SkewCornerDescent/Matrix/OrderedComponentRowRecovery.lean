/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EffectiveOutgoingCoordinates
import SkewCornerDescent.Matrix.OrderedComponentColumnRecovery

/-!
# Original component rows from complete ordered outgoing coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). The
known suffix's complete inverse supplies each effective outgoing coordinate.
The protected inverse row recovers every literal component row without deleting
or freezing a later-block coupling. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Complete outgoing coefficients expand in the full effective outgoing
column, retaining every current-block inverse entry. -/
theorem upper_block_effective_outgoing {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (A : Matrix ν ν F) (U : Matrix ν μ F) (B : Matrix μ μ F)
    (r : Matrix ν Unit F) (s : Matrix μ Unit F)
    [Invertible A] [Invertible B] [Invertible (Matrix.fromBlocks A U 0 B)] (i : ν) :
    (⅟(Matrix.fromBlocks A U 0 B) * Matrix.fromRows r s) (.inl i) () =
      ∑ k, ⅟A i k * (r - U * ⅟B * s) k () := by
  rw [upper_block_outgoing_head, ← Matrix.mul_apply, Matrix.mul_sub, Matrix.sub_apply]
  simp only [Matrix.mul_assoc]

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original outgoing coefficient is the full effective-coordinate
inventory, not an isolated component response. -/
theorem ordered_component_effective_outgoing {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (row col : ν → ℤ) (y τ : ℤ)
    (hsep : ∀ i k, row i < P.zeta k + τ)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hhigh : ∀ k, (c.top : ℤ) < P.xi k + τ - y) (i : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    letI := c.orderedComponentSuffixInverse P hne row col τ hsep
    let A := (jtMatrix P.xi P.zeta).map c.residueMap
    let rows := Sum.elim (fun i => P.xi i + τ) row
    let cols := Sum.elim (fun i => P.zeta i + τ) col
    (⅟(vertexBetaMatrix c.residueMap rows cols) * vertexIncoming c.residueMap rows y) (.inl i) () =
      ∑ k, ⅟A i k * c.effectiveOutgoingCoordinate row col y
        (higherIndexFromInteger c.top (P.xi k + τ - y) (hhigh k)) := by
  classical
  let := c.profileResidueInverse P hne
  let := c.orderedComponentSuffixInverse P hne row col τ hsep
  let A := (jtMatrix P.xi P.zeta).map c.residueMap
  let B := vertexBetaMatrix c.residueMap row col
  let U := Matrix.of fun k j => c.residueMap (hh (P.xi k + τ - col j))
  let r := Matrix.of fun k (_ : Unit) => c.residueMap (hh (P.xi k + τ - y))
  let s := vertexIncoming c.residueMap row y
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  have hinv :
      ⅟(vertexBetaMatrix c.residueMap (Sum.elim (fun i => P.xi i + τ) row)
        (Sum.elim (fun i => P.zeta i + τ) col)) = ⅟(Matrix.fromBlocks A U 0 B) := by
    rw [Matrix.invOf_eq_nonsing_inv, c.ordered_component_suffix_matrix P row col τ hsep,
      Matrix.invOf_eq_nonsing_inv]
  have hvec : vertexIncoming c.residueMap (Sum.elim (fun i => P.xi i + τ) row) y =
      Matrix.fromRows r s := by
    ext k j
    cases k <;> rfl
  dsimp only
  rw [hinv, hvec, upper_block_effective_outgoing]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change c.residueMap (hh (P.xi k + τ - y)) - (U * ⅟B * s) k () = _
  have hcorr : (U * ⅟B * s) k () =
      inverseContraction (fun j => c.residueMap (hh (P.xi k + τ - col j)))
        (fun j => c.residueMap (hh (row j - y))) B := by
    simp only [Matrix.mul_apply, Finset.sum_mul, U, s, vertexIncoming, Matrix.of_apply,
      Matrix.invOf_eq_nonsing_inv, inverseContraction]
    rw [Finset.sum_comm]
  rw [hcorr]
  exact c.effective_outgoing_original_coordinate row col y (P.xi k + τ)
    (higherIndexFromInteger c.top (P.xi k + τ - y) (hhigh k))
    (higherIndexFromInteger_coe _ _ _).symm

/-- Equal complete outgoing coefficients at two components' least columns
recover both complete literal row lists before the common original suffix. -/
theorem ordered_component_extreme_outgoing_rows_eq {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 ≠ P.schur) (hQ : cellSchur D hD.1 ≠ Q.schur)
    (hspanP : P.topVar ≤ c.top) (hspanQ : Q.topVar ≤ c.top)
    (row col : ν → ℤ) (y τ υ : ℤ)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hcol : ∀ i, y < col i)
    (hsepP : ∀ i k, row i < P.zeta k + τ) (hsepQ : ∀ i k, row i < Q.zeta k + υ)
    (hleft : ∀ i, (c.top : ℤ) < P.xi i + τ - y)
    (hright : ∀ j, (c.top : ℤ) < Q.xi j + υ - y)
    (hvalue :
      letI := c.orderedComponentSuffixInverse P hP row col τ hsepP
      letI := c.orderedComponentSuffixInverse Q hQ row col υ hsepQ
      (⅟(vertexBetaMatrix c.residueMap (Sum.elim (fun i => P.xi i + τ) row)
          (Sum.elim (fun i => P.zeta i + τ) col)) *
        vertexIncoming c.residueMap (Sum.elim (fun i => P.xi i + τ) row) y) (.inl (Fin.last n)) () =
      (⅟(vertexBetaMatrix c.residueMap (Sum.elim (fun i => Q.xi i + υ) row)
          (Sum.elim (fun i => Q.zeta i + υ) col)) *
        vertexIncoming c.residueMap (Sum.elim (fun i => Q.xi i + υ) row) y)
          (.inl (Fin.last m)) ()) :
    Finset.univ.image (fun i => P.xi i + τ) =
      Finset.univ.image (fun j => Q.xi j + υ) := by
  classical
  let := c.profileResidueInverse P hP
  let := c.profileResidueInverse Q hQ
  let IP := ⅟((jtMatrix P.xi P.zeta).map c.residueMap)
  let IQ := ⅟((jtMatrix Q.xi Q.zeta).map c.residueMap)
  let left := fun i => higherIndexFromInteger c.top (P.xi i + τ - y) (hleft i)
  let right := fun j => higherIndexFromInteger c.top (Q.xi j + υ - y) (hright j)
  let a : Fin (n + 1) → residueLowerField c.top c.top := fun i =>
    ⟨IP (Fin.last n) i,
      c.component_residue_inverse_mem_selected_lower P hP hspanP (Fin.last n) i⟩
  let b : Fin (m + 1) → residueLowerField c.top c.top := fun j =>
    ⟨IQ (Fin.last m) j,
      c.component_residue_inverse_mem_selected_lower Q hQ hspanQ (Fin.last m) j⟩
  have hl (i) : ((left i).val : ℤ) = P.xi i + τ - y := higherIndexFromInteger_coe _ _ _
  have hr (j) : ((right j).val : ℤ) = Q.xi j + υ - y := higherIndexFromInteger_coe _ _ _
  have hlinj : Function.Injective left := by
    intro i j heq
    have he := congrArg (fun z : ResidueHigherIndex c.top => (z.val : ℤ)) heq
    rw [hl i, hl j] at he
    apply P.xi_strictAnti.injective
    omega
  have hrinj : Function.Injective right := by
    intro i j heq
    have he := congrArg (fun z : ResidueHigherIndex c.top => (z.val : ℤ)) heq
    rw [hr i, hr j] at he
    apply Q.xi_strictAnti.injective
    omega
  have ha (i) : a i ≠ 0 := by
    intro he
    have hz := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) he
    exact c.residue_inverse_least_column_entry_ne_zero P hP hspanP i hz
  have hb (j) : b j ≠ 0 := by
    intro he
    have hz := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) he
    exact c.residue_inverse_least_column_entry_ne_zero Q hQ hspanQ j hz
  have hnextP (i k) : row k - y < ((left i).val : ℤ) := by
    rw [hl]
    have hs := hsepP k i
    have hp := P.r_pos i
    have he := P.xi_sub_zeta i
    omega
  have hnextQ (j k) : row k - y < ((right j).val : ℤ) := by
    rw [hr]
    have hs := hsepQ k j
    have hp := Q.r_pos j
    have he := Q.xi_sub_zeta j
    omega
  rw [c.ordered_component_effective_outgoing P hP row col y τ hsepP hleft (Fin.last n),
    c.ordered_component_effective_outgoing Q hQ row col y υ hsepQ hright (Fin.last m)] at hvalue
  have heval : (∑ i, (a i : OtherField c.top) * c.effectiveOutgoingCoordinate row col y (left i)) =
      ∑ j, (b j : OtherField c.top) * c.effectiveOutgoingCoordinate row col y (right j) := by
    simpa only [a, b, IP, IQ, left, right] using hvalue
  have hs := c.effective_outgoing_support_eq row col y hcol left right hlinj hrinj
    hnextP hnextQ a b ha hb heval
  have hrows := congrArg (Finset.image (fun j : ResidueHigherIndex c.top =>
    (j.val : ℤ) + y)) hs
  simpa only [Finset.image_image, Function.comp_def, hl, hr, sub_add_cancel] using hrows

end SelectedCoordinate
end SkewCornerDescent.Matrix
