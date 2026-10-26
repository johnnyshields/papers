/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CommonCoreBorders

/-!
# Compatible common-core column orientation

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). A common permutation of the core/right-splice column frame
has the same determinant sign in all four border sizes. Its signs cancel in the
cross difference over every commutative ring. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {α β γ F : Type*}

/-- Extend a common middle-frame column permutation without changing either border. -/
def commonCoreFramePerm (α γ : Type*) (σ : Equiv.Perm (Unit ⊕ β)) :
    Equiv.Perm ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) :=
  Equiv.sumCongr (Equiv.refl (α ⊕ Unit)) (Equiv.sumCongr σ (Equiv.refl γ))

variable [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommRing F]

/-- The same middle permutation has one determinant sign regardless of the
left or right border size. -/
theorem det_commonCoreFramePerm (σ : Equiv.Perm (Unit ⊕ β))
    (M : Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F) :
    (M.submatrix id (commonCoreFramePerm α γ σ)).det = Equiv.Perm.sign σ * M.det := by
  rw [Matrix.det_permute']
  simp only [commonCoreFramePerm, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl,
    one_mul, mul_one]

/-- Natural column reordering retains the entire compatible cross difference,
including all four determinant orientations. No nonzero determinant is required. -/
theorem commonCore_cross_difference_column_orientation (σ : Equiv.Perm (Unit ⊕ β))
    (M00 : Matrix ((Empty ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ Empty))
      ((Empty ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ Empty)) F)
    (M10 : Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ Empty))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ Empty)) F)
    (M01 : Matrix ((Empty ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((Empty ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F)
    (M11 : Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) F) :
    (M11.submatrix id (commonCoreFramePerm α γ σ)).det *
        (M00.submatrix id (commonCoreFramePerm Empty Empty σ)).det -
      (M10.submatrix id (commonCoreFramePerm α Empty σ)).det *
        (M01.submatrix id (commonCoreFramePerm Empty γ σ)).det =
      M11.det * M00.det - M10.det * M01.det := by
  simp only [det_commonCoreFramePerm]
  have hs : (Equiv.Perm.sign σ : F) * (Equiv.Perm.sign σ : F) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  calc
    _ = ((Equiv.Perm.sign σ : F) * (Equiv.Perm.sign σ : F)) *
        (M11.det * M00.det - M10.det * M01.det) := by ring
    _ = _ := by rw [hs, one_mul]

end SkewCornerDescent.Matrix
