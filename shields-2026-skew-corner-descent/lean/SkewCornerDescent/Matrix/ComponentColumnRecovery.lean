/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProtectedComponentProfiles
import SkewCornerDescent.Matrix.HigherLinearRecovery

/-!
# Literal columns recovered from a complete component's extreme coefficient

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). The
incoming coefficient at the greatest original row identifies every original
column of a complete unit block once its earlier-block correction is removed.
Actual beta translations are retained. Protected inverse entries and the complete
selected lower coefficient field are produced, not assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial
open scoped BigOperators

/-- An actual integer endpoint distance strictly above the selected span gives
its corresponding surviving higher generator, with no truncated subtraction. -/
def higherIndexFromInteger (N : ℕ+) (z : ℤ) (hz : (N : ℤ) < z) : ResidueHigherIndex N :=
  ⟨⟨z.toNat, by have := N.pos; omega⟩, by
    change (N : ℕ) < z.toNat
    have := N.pos
    omega⟩

/-- The constructed index is exactly the original integer distance. -/
theorem higherIndexFromInteger_coe (N : ℕ+) (z : ℤ) (hz : (N : ℤ) < z) :
    ((higherIndexFromInteger N z hz).val : ℤ) = z := by
  change (z.toNat : ℤ) = z
  have := N.pos
  omega

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal extreme incoming coefficients of two complete nonselected blocks
recover their full literal column lists, including the original beta translations.
The common endpoint and its strict distance from every column are geometric data;
the coefficient equality is the endpoint-profile observation being decoded. -/
theorem component_extreme_incoming_columns_eq {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 ≠ P.schur) (hQ : cellSchur D hD.1 ≠ Q.schur)
    (hspanP : P.topVar ≤ c.top) (hspanQ : Q.topVar ≤ c.top)
    (x τ υ : ℤ)
    (hleft : ∀ i, (c.top : ℤ) < x - (P.zeta i + τ))
    (hright : ∀ j, (c.top : ℤ) < x - (Q.zeta j + υ))
    (hvalue :
      letI := c.profileResidueInverse P hP
      letI := c.profileResidueInverse Q hQ
      (∑ i, c.residueMap (hh (x - (P.zeta i + τ))) *
        ⅟((jtMatrix P.xi P.zeta).map c.residueMap) i 0) =
      ∑ j, c.residueMap (hh (x - (Q.zeta j + υ))) *
        ⅟((jtMatrix Q.xi Q.zeta).map c.residueMap) j 0) :
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
  have ha : ∀ i, a i ≠ 0 := by
    intro i heq
    have hzero := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) heq
    exact c.residue_inverse_greatest_row_entry_ne_zero P hP hspanP i hzero
  have hb : ∀ j, b j ≠ 0 := by
    intro j heq
    have hzero := congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) heq
    exact c.residue_inverse_greatest_row_entry_ne_zero Q hQ hspanQ j hzero
  have hleftValue (i) : c.residueMap (hh (x - (P.zeta i + τ))) =
      residueGenerator c.top ⟨(left i).val, ne_of_gt (left i).prop⟩ := by
    rw [← hl i, hh_pnat, c.residueMap_other _ (ne_of_gt (left i).prop)]
    rfl
  have hrightValue (j) : c.residueMap (hh (x - (Q.zeta j + υ))) =
      residueGenerator c.top ⟨(right j).val, ne_of_gt (right j).prop⟩ := by
    rw [← hr j, hh_pnat, c.residueMap_other _ (ne_of_gt (right j).prop)]
    rfl
  have heval :
      (∑ i, (a i : OtherField c.top) * residueGenerator c.top ⟨(left i).val, ne_of_gt (left i).prop⟩) =
        ∑ j, (b j : OtherField c.top) * residueGenerator c.top ⟨(right j).val, ne_of_gt (right j).prop⟩ := by
    simp_rw [hleftValue, hrightValue] at hvalue
    simpa only [a, b, IP, IQ, mul_comm] using hvalue
  have hsupport := residue_higher_linear_support_eq c.top left right hlinj hrinj a b ha hb heval
  have hcolumns := congrArg (Finset.image (fun j : ResidueHigherIndex c.top => x - (j.val : ℤ))) hsupport
  simpa only [Finset.image_image, Function.comp_def, hl, hr, sub_sub_cancel] using hcolumns

end SelectedCoordinate
end SkewCornerDescent.Matrix
