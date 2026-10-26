/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EffectiveIncomingCoordinates
import SkewCornerDescent.Matrix.ComponentColumnRecovery

/-!
# Original component columns from complete ordered incoming coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). The
known prefix's full inverse supplies each effective incoming coordinate. The
component's protected extreme inverse column then recovers all its original
columns, without removing or freezing the earlier-block correction.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Complete upper-block incoming coefficients expand in the full effective
incoming row, with the whole current-block inverse still present. -/
theorem upper_block_effective_incoming {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (A : Matrix ν ν F) (U : Matrix ν μ F) (B : Matrix μ μ F)
    (r : Matrix Unit ν F) (s : Matrix Unit μ F)
    [Invertible A] [Invertible B] [Invertible (Matrix.fromBlocks A U 0 B)] (j : μ) :
    (Matrix.fromCols r s * ⅟(Matrix.fromBlocks A U 0 B)) () (.inr j) =
      ∑ k, (s - r * ⅟A * U) () k * ⅟B k j := by
  rw [upper_block_incoming_tail, ← Matrix.mul_apply, Matrix.sub_mul, Matrix.sub_apply]

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete literal incoming coefficient is the inventory in the produced
effective coordinates, not an isolated component response. -/
theorem ordered_component_effective_incoming {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (row col : ν → ℤ) (x τ : ℤ)
    (hsep : ∀ i k, P.xi i + τ < col k)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hhigh : ∀ k, (c.top : ℤ) < x - (P.zeta k + τ)) (j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    letI := c.orderedComponentPrefixInverse P hne row col τ hsep
    let B := (jtMatrix P.xi P.zeta).map c.residueMap
    let rows := Sum.elim row (fun i => P.xi i + τ)
    let cols := Sum.elim col (fun i => P.zeta i + τ)
    (vertexOutgoing c.residueMap cols x * ⅟(vertexBetaMatrix c.residueMap rows cols)) () (.inr j) =
      ∑ k, c.effectiveIncomingCoordinate row col x
        (higherIndexFromInteger c.top (x - (P.zeta k + τ)) (hhigh k)) * ⅟B k j := by
  classical
  let := c.profileResidueInverse P hne
  let := c.orderedComponentPrefixInverse P hne row col τ hsep
  let A := vertexBetaMatrix c.residueMap row col
  let B := (jtMatrix P.xi P.zeta).map c.residueMap
  let U := Matrix.of fun i k => c.residueMap (hh (row i - (P.zeta k + τ)))
  let r := vertexOutgoing c.residueMap col x
  let s := Matrix.of fun (_ : Unit) k => c.residueMap (hh (x - (P.zeta k + τ)))
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  have hinv :
      ⅟(vertexBetaMatrix c.residueMap (Sum.elim row (fun i => P.xi i + τ))
        (Sum.elim col (fun i => P.zeta i + τ))) = ⅟(Matrix.fromBlocks A U 0 B) := by
    rw [Matrix.invOf_eq_nonsing_inv, c.ordered_component_prefix_matrix P row col τ hsep,
      Matrix.invOf_eq_nonsing_inv]
  have hvec : vertexOutgoing c.residueMap (Sum.elim col (fun i => P.zeta i + τ)) x =
      Matrix.fromCols r s := by
    ext i k
    cases k <;> rfl
  dsimp only
  rw [hinv, hvec, upper_block_effective_incoming]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change c.residueMap (hh (x - (P.zeta k + τ))) - (r * ⅟A * U) () k = _
  have hcorr : (r * ⅟A * U) () k =
      inverseContraction (fun i => c.residueMap (hh (x - col i)))
        (fun i => c.residueMap (hh (row i - (P.zeta k + τ)))) A := by
    simp only [Matrix.mul_apply, Finset.sum_mul, r, vertexOutgoing, U, Matrix.of_apply,
      Matrix.invOf_eq_nonsing_inv, inverseContraction]
    rw [Finset.sum_comm]
  rw [hcorr]
  exact c.effective_incoming_original_coordinate row col x (P.zeta k + τ)
    (higherIndexFromInteger c.top (x - (P.zeta k + τ)) (hhigh k))
    (higherIndexFromInteger_coe _ _ _).symm

/-- Equal complete incoming coefficients at two components' greatest rows
recover both complete literal column lists after the common original prefix.
All lower-field coefficients and both full inverses are produced internally. -/
theorem ordered_component_extreme_incoming_columns_eq {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 ≠ P.schur) (hQ : cellSchur D hD.1 ≠ Q.schur)
    (hspanP : P.topVar ≤ c.top) (hspanQ : Q.topVar ≤ c.top)
    (row col : ν → ℤ) (x τ υ : ℤ)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hrow : ∀ i, row i < x)
    (hsepP : ∀ i k, P.xi i + τ < col k) (hsepQ : ∀ i k, Q.xi i + υ < col k)
    (hleft : ∀ i, (c.top : ℤ) < x - (P.zeta i + τ))
    (hright : ∀ j, (c.top : ℤ) < x - (Q.zeta j + υ))
    (hvalue :
      letI := c.orderedComponentPrefixInverse P hP row col τ hsepP
      letI := c.orderedComponentPrefixInverse Q hQ row col υ hsepQ
      (vertexOutgoing c.residueMap (Sum.elim col (fun i => P.zeta i + τ)) x *
        ⅟(vertexBetaMatrix c.residueMap (Sum.elim row (fun i => P.xi i + τ))
          (Sum.elim col (fun i => P.zeta i + τ)))) () (.inr 0) =
      (vertexOutgoing c.residueMap (Sum.elim col (fun i => Q.zeta i + υ)) x *
        ⅟(vertexBetaMatrix c.residueMap (Sum.elim row (fun i => Q.xi i + υ))
          (Sum.elim col (fun i => Q.zeta i + υ)))) () (.inr 0)) :
    Finset.univ.image (fun i => P.zeta i + τ) =
      Finset.univ.image (fun j => Q.zeta j + υ) := by
  classical
  let := c.profileResidueInverse P hP
  let := c.profileResidueInverse Q hQ
  let IP := ⅟((jtMatrix P.xi P.zeta).map c.residueMap)
  let IQ := ⅟((jtMatrix Q.xi Q.zeta).map c.residueMap)
  let left := fun i => higherIndexFromInteger c.top (x - (P.zeta i + τ)) (hleft i)
  let right := fun j => higherIndexFromInteger c.top (x - (Q.zeta j + υ)) (hright j)
  let a : Fin (n + 1) → residueLowerField c.top c.top := fun i =>
    ⟨IP i 0, c.component_residue_inverse_mem_selected_lower P hP hspanP i 0⟩
  let b : Fin (m + 1) → residueLowerField c.top c.top := fun j =>
    ⟨IQ j 0, c.component_residue_inverse_mem_selected_lower Q hQ hspanQ j 0⟩
  have hl (i) : ((left i).val : ℤ) = x - (P.zeta i + τ) := higherIndexFromInteger_coe _ _ _
  have hr (j) : ((right j).val : ℤ) = x - (Q.zeta j + υ) := higherIndexFromInteger_coe _ _ _
  have hlinj : Function.Injective left := by
    intro i j heq
    have he := congrArg (fun z : ResidueHigherIndex c.top => (z.val : ℤ)) heq
    rw [hl i, hl j] at he
    apply P.zeta_strictAnti.injective
    omega
  have hrinj : Function.Injective right := by
    intro i j heq
    have he := congrArg (fun z : ResidueHigherIndex c.top => (z.val : ℤ)) heq
    rw [hr i, hr j] at he
    apply Q.zeta_strictAnti.injective
    omega
  have ha (i) : a i ≠ 0 := by
    intro he
    have hz := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) he
    exact c.residue_inverse_greatest_row_entry_ne_zero P hP hspanP i hz
  have hb (j) : b j ≠ 0 := by
    intro he
    have hz := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) he
    exact c.residue_inverse_greatest_row_entry_ne_zero Q hQ hspanQ j hz
  have hprevP (i k) : x - col k < ((left i).val : ℤ) := by
    rw [hl]
    have hs := hsepP i k
    have hp := P.r_pos i
    have he := P.xi_sub_zeta i
    omega
  have hprevQ (j k) : x - col k < ((right j).val : ℤ) := by
    rw [hr]
    have hs := hsepQ j k
    have hp := Q.r_pos j
    have he := Q.xi_sub_zeta j
    omega
  rw [c.ordered_component_effective_incoming P hP row col x τ hsepP hleft 0,
    c.ordered_component_effective_incoming Q hQ row col x υ hsepQ hright 0] at hvalue
  have heval : (∑ i, (a i : OtherField c.top) * c.effectiveIncomingCoordinate row col x (left i)) =
      ∑ j, (b j : OtherField c.top) * c.effectiveIncomingCoordinate row col x (right j) := by
    simpa only [a, b, IP, IQ, left, right, mul_comm] using hvalue
  have hs := c.effective_incoming_support_eq row col x hrow left right hlinj hrinj
    hprevP hprevQ a b ha hb heval
  have hcolumns := congrArg (Finset.image (fun j : ResidueHigherIndex c.top =>
    x - (j.val : ℤ))) hs
  simpa only [Finset.image_image, Function.comp_def, hl, hr, sub_sub_cancel] using hcolumns

end SelectedCoordinate
end SkewCornerDescent.Matrix
