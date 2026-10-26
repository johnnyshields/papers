/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CommonCoreDifference

/-!
# Reindexing complete compatible left borders

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
Simultaneous row and column transport preserves each determinant and the full
cross difference. No border coupling is omitted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {α δ β γ F : Type*} [Fintype α] [Fintype δ] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq δ] [DecidableEq β] [DecidableEq γ] [CommRing F]

/-- The complete determinant is unchanged by an equivalence of left-border states. -/
theorem borderedCoreMatrix_left_equiv_det (e : δ ≃ α)
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F) :
    (borderedCoreMatrix (A.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) e)
      (R.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) id)
      (T.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) id) C S B).det =
      (borderedCoreMatrix A R T C S B).det := by
  let f := Equiv.sumCongr (Equiv.sumCongr e (Equiv.refl Unit))
    (Equiv.refl ((Unit ⊕ β) ⊕ γ))
  have hm : borderedCoreMatrix (A.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) e)
      (R.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) id)
      (T.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) id) C S B =
      (borderedCoreMatrix A R T C S B).submatrix f f := by
    ext i j
    rcases i with (a | u) | ((v | b) | g) <;>
      rcases j with (a | u) | ((v | b) | g) <;> rfl
  rw [hm, Matrix.det_submatrix_equiv_self]

/-- The same left-border equivalence transports both determinants that use it. -/
theorem commonCoreDifference_left_equiv (e : δ ≃ α)
    (A : Matrix (α ⊕ Unit) α F) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) F)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) F) (C : Matrix (Unit ⊕ β) (Unit ⊕ β) F)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) F) (B : Matrix γ (Unit ⊕ γ) F)
    (r s : (Unit ⊕ β) → F) (t : (α ⊕ Unit) → F) (q : (Unit ⊕ γ) → F) (z : F) :
    commonCoreDifference (A.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) e)
      (R.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) id)
      (T.submatrix (Equiv.sumCongr e (Equiv.refl Unit)) id) C S B r s
      (t ∘ Equiv.sumCongr e (Equiv.refl Unit)) q z =
      commonCoreDifference A R T C S B r s t q z := by
  unfold commonCoreDifference
  rw [borderedCoreMatrix_left_equiv_det]
  have ht : (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i).submatrix
      (Equiv.sumCongr e (Equiv.refl Unit)) id =
      Matrix.of fun i (_ : Unit ⊕ Fin 0) =>
        (t ∘ Equiv.sumCongr e (Equiv.refl Unit)) i := rfl
  rw [← ht, borderedCoreMatrix_left_equiv_det]

end SkewCornerDescent.Matrix
