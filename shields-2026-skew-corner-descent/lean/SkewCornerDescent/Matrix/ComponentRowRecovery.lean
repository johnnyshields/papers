/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ComponentColumnRecovery

/-!
# Literal rows recovered from a complete component's extreme coefficient

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). The
outgoing coefficient at the least original column identifies every original row
of a complete unit block after its known outgoing row has been restored. Original
beta translations, complete inverses, and all nonzero protected weights remain.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete literal row lists of two unit blocks are recovered from equal
extreme outgoing coefficients. Coefficients belong to the actual selected lower
field; their nonvanishing is supplied by original extreme cofactors. -/
theorem component_extreme_outgoing_rows_eq {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 ≠ P.schur) (hQ : cellSchur D hD.1 ≠ Q.schur)
    (hspanP : P.topVar ≤ c.top) (hspanQ : Q.topVar ≤ c.top)
    (y τ υ : ℤ)
    (hleft : ∀ i, (c.top : ℤ) < P.xi i + τ - y)
    (hright : ∀ j, (c.top : ℤ) < Q.xi j + υ - y)
    (hvalue :
      letI := c.profileResidueInverse P hP
      letI := c.profileResidueInverse Q hQ
      (∑ i, ⅟((jtMatrix P.xi P.zeta).map c.residueMap) (Fin.last n) i *
        c.residueMap (hh (P.xi i + τ - y))) =
      ∑ j, ⅟((jtMatrix Q.xi Q.zeta).map c.residueMap) (Fin.last m) j *
        c.residueMap (hh (Q.xi j + υ - y))) :
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
    ⟨IP (Fin.last n) i, c.component_residue_inverse_mem_selected_lower P hP hspanP (Fin.last n) i⟩
  let b : Fin (m + 1) → residueLowerField c.top c.top := fun j =>
    ⟨IQ (Fin.last m) j, c.component_residue_inverse_mem_selected_lower Q hQ hspanQ (Fin.last m) j⟩
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
  have ha : ∀ i, a i ≠ 0 := by
    intro i heq
    have hzero := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) heq
    exact c.residue_inverse_least_column_entry_ne_zero P hP hspanP i hzero
  have hb : ∀ j, b j ≠ 0 := by
    intro j heq
    have hzero := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) heq
    exact c.residue_inverse_least_column_entry_ne_zero Q hQ hspanQ j hzero
  have hleftValue (i) : c.residueMap (hh (P.xi i + τ - y)) =
      residueGenerator c.top ⟨(left i).val, ne_of_gt (left i).prop⟩ := by
    rw [← hl i, hh_pnat, c.residueMap_other _ (ne_of_gt (left i).prop)]
    rfl
  have hrightValue (j) : c.residueMap (hh (Q.xi j + υ - y)) =
      residueGenerator c.top ⟨(right j).val, ne_of_gt (right j).prop⟩ := by
    rw [← hr j, hh_pnat, c.residueMap_other _ (ne_of_gt (right j).prop)]
    rfl
  have heval :
      (∑ i, (a i : OtherField c.top) * residueGenerator c.top ⟨(left i).val, ne_of_gt (left i).prop⟩) =
        ∑ j, (b j : OtherField c.top) * residueGenerator c.top ⟨(right j).val, ne_of_gt (right j).prop⟩ := by
    simp_rw [hleftValue, hrightValue] at hvalue
    simpa only [a, b, IP, IQ] using hvalue
  have hsupport := residue_higher_linear_support_eq c.top left right hlinj hrinj a b ha hb heval
  have hrows := congrArg (Finset.image (fun j : ResidueHigherIndex c.top => (j.val : ℤ) + y)) hsupport
  simpa only [Finset.image_image, Function.comp_def, hl, hr, sub_add_cancel] using hrows

end SkewCornerDescent.Matrix.SelectedCoordinate
