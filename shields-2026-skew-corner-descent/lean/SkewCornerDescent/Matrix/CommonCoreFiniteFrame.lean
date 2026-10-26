/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CommonCoreFrameOrientation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Natural finite frames for compatible Jacobi--Trudi borders

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). The row frame is in literal order. One common middle-column
rotation puts the right splice after the core, with the same determinant sign
for every border size. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The first core index is distinguished from its remaining indices. -/
def commonCoreFinEquiv (b : ℕ) : (Unit ⊕ Fin b) ≃ Fin (b + 1) where
  toFun | .inl _ => 0 | .inr i => i.succ
  invFun := Fin.cases (.inl ()) Sum.inr
  left_inv := by
    rintro (u | i)
    · cases u
      rfl
    · rfl
  right_inv := Fin.cases rfl (fun _ => rfl)

/-- The unmatched top row follows all left-border rows. -/
def commonCoreTopFinEquiv (a : ℕ) : (Fin a ⊕ Unit) ≃ Fin (a + 1) :=
  ((Equiv.sumComm (Fin a) Unit).trans (commonCoreFinEquiv a)).trans
    (finRotate (a + 1)).symm

@[simp]
theorem commonCoreTopFinEquiv_left (a : ℕ) (i : Fin a) :
    commonCoreTopFinEquiv a (.inl i) = i.castSucc := by
  change (finRotate (a + 1)).symm i.succ = i.castSucc
  apply (finRotate (a + 1)).symm_apply_eq.mpr
  exact (finRotate_of_lt i.isLt).symm

@[simp]
theorem commonCoreTopFinEquiv_unit (a : ℕ) :
    commonCoreTopFinEquiv a (.inr ()) = Fin.last a := by
  change (finRotate (a + 1)).symm 0 = Fin.last a
  apply (finRotate (a + 1)).symm_apply_eq.mpr
  exact finRotate_last.symm

/-- Natural row order of the whole compatible frame. -/
def commonCoreFiniteRows (a b c : ℕ) :
    ((Fin a ⊕ Unit) ⊕ ((Unit ⊕ Fin b) ⊕ Fin c)) ≃ Fin (a + 1 + (b + 1 + c)) :=
  (Equiv.sumCongr (commonCoreTopFinEquiv a)
    ((Equiv.sumCongr (commonCoreFinEquiv b) (Equiv.refl _)).trans finSumFinEquiv)).trans
      finSumFinEquiv

/-- The right-splice column follows every core column in natural matrix order. -/
def commonCoreFiniteCycle (b : ℕ) : Equiv.Perm (Unit ⊕ Fin b) :=
  ((commonCoreFinEquiv b).trans (finRotate (b + 1)).symm).trans
    (commonCoreFinEquiv b).symm

@[simp]
theorem commonCoreFiniteCycle_first (b : ℕ) :
    commonCoreFinEquiv b (commonCoreFiniteCycle b (.inl ())) = Fin.last b := by
  simp only [commonCoreFiniteCycle, Equiv.trans_apply, Equiv.apply_symm_apply]
  change (finRotate (b + 1)).symm 0 = Fin.last b
  apply (finRotate (b + 1)).symm_apply_eq.mpr
  exact finRotate_last.symm

@[simp]
theorem commonCoreFiniteCycle_tail (b : ℕ) (j : Fin b) :
    commonCoreFinEquiv b (commonCoreFiniteCycle b (.inr j)) = j.castSucc := by
  simp only [commonCoreFiniteCycle, Equiv.trans_apply, Equiv.apply_symm_apply]
  change (finRotate (b + 1)).symm j.succ = j.castSucc
  apply (finRotate (b + 1)).symm_apply_eq.mpr
  exact (finRotate_of_lt j.isLt).symm

/-- Natural column order in the same compatible frame. -/
def commonCoreFiniteCols (a b c : ℕ) :
    ((Fin a ⊕ Unit) ⊕ ((Unit ⊕ Fin b) ⊕ Fin c)) ≃ Fin (a + 1 + (b + 1 + c)) :=
  (commonCoreFramePerm (Fin a) (Fin c) (commonCoreFiniteCycle b)).trans
    (commonCoreFiniteRows a b c)

@[simp]
theorem commonCoreFiniteRows_left (a b c : ℕ) (i : Fin a) :
    (commonCoreFiniteRows a b c (.inl (.inl i))).val = i.val := by
  simp [commonCoreFiniteRows]

@[simp]
theorem commonCoreFiniteRows_top (a b c : ℕ) :
    (commonCoreFiniteRows a b c (.inl (.inr ()))).val = a := by
  simp [commonCoreFiniteRows]

@[simp]
theorem commonCoreFiniteRows_core (a b c : ℕ) (j : Unit ⊕ Fin b) :
    (commonCoreFiniteRows a b c (.inr (.inl j))).val =
      a + 1 + (commonCoreFinEquiv b j).val := by
  simp [commonCoreFiniteRows]

@[simp]
theorem commonCoreFiniteRows_right (a b c : ℕ) (i : Fin c) :
    (commonCoreFiniteRows a b c (.inr (.inr i))).val = a + 1 + (b + 1 + i.val) := by
  simp [commonCoreFiniteRows]

@[simp]
theorem commonCoreFiniteCols_left (a b c : ℕ) (i : Fin a) :
    (commonCoreFiniteCols a b c (.inl (.inl i))).val = i.val := by
  simp [commonCoreFiniteCols, commonCoreFramePerm]

@[simp]
theorem commonCoreFiniteCols_top (a b c : ℕ) :
    (commonCoreFiniteCols a b c (.inl (.inr ()))).val = a := by
  simp [commonCoreFiniteCols, commonCoreFramePerm]

@[simp]
theorem commonCoreFiniteCols_first (a b c : ℕ) :
    (commonCoreFiniteCols a b c (.inr (.inl (.inl ())))).val = a + 1 + b := by
  simp [commonCoreFiniteCols, commonCoreFramePerm]

@[simp]
theorem commonCoreFiniteCols_tail (a b c : ℕ) (j : Fin b) :
    (commonCoreFiniteCols a b c (.inr (.inl (.inr j)))).val = a + 1 + j.val := by
  simp [commonCoreFiniteCols, commonCoreFramePerm]

@[simp]
theorem commonCoreFiniteCols_right (a b c : ℕ) (i : Fin c) :
    (commonCoreFiniteCols a b c (.inr (.inr i))).val = a + 1 + (b + 1 + i.val) := by
  simp [commonCoreFiniteCols, commonCoreFramePerm]

/-- Natural indices of the entire retained core-column family. -/
@[simp]
theorem commonCoreFiniteCols_core (a b c : ℕ) (j : Unit ⊕ Fin b) :
    (commonCoreFiniteCols a b c
      (commonCoreColumnEquiv (Fin a) (Fin b) (Fin c) (.inr (.inl j)))).val =
      a + (commonCoreFinEquiv b j).val := by
  rcases j with u | j
  · cases u
    change (commonCoreFiniteCols a b c (.inl (.inr ()))).val = a + 0
    simpa only [Nat.add_zero] using commonCoreFiniteCols_top a b c
  · change (commonCoreFiniteCols a b c (.inr (.inl (.inr j)))).val = a + (j.val + 1)
    have he := commonCoreFiniteCols_tail a b c j
    omega

/-- Natural indices of the right splice and every remaining right-border column. -/
@[simp]
theorem commonCoreFiniteCols_border (a b c : ℕ) (j : Unit ⊕ Fin c) :
    (commonCoreFiniteCols a b c
      (commonCoreColumnEquiv (Fin a) (Fin b) (Fin c) (.inr (.inr j)))).val =
      a + (b + 1) + (commonCoreFinEquiv c j).val := by
  rcases j with u | j
  · cases u
    change (commonCoreFiniteCols a b c (.inr (.inl (.inl ())))).val = a + (b + 1) + 0
    have he := commonCoreFiniteCols_first a b c
    omega
  · change (commonCoreFiniteCols a b c (.inr (.inr j))).val = a + (b + 1) + (j.val + 1)
    have he := commonCoreFiniteCols_right a b c j
    omega

/-- Every naturally ordered finite Jacobi--Trudi matrix acquires the same middle
rotation sign when placed in the compatible block frame. -/
theorem det_commonCoreFiniteFrame {F : Type*} [CommRing F] (a b c : ℕ)
    (M : Matrix (Fin (a + 1 + (b + 1 + c))) (Fin (a + 1 + (b + 1 + c))) F) :
    (M.submatrix (commonCoreFiniteRows a b c) (commonCoreFiniteCols a b c)).det =
      Equiv.Perm.sign (commonCoreFiniteCycle b) * M.det := by
  have he : M.submatrix (commonCoreFiniteRows a b c) (commonCoreFiniteCols a b c) =
      (M.submatrix (commonCoreFiniteRows a b c) (commonCoreFiniteRows a b c)).submatrix
        id (commonCoreFramePerm (Fin a) (Fin c) (commonCoreFiniteCycle b)) := by
    ext i j
    rfl
  rw [he, det_commonCoreFramePerm, Matrix.det_submatrix_equiv_self]

end SkewCornerDescent.Matrix
