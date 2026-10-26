/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CommonCoreFiniteFrame
import SkewGluing.Irreducibility

/-!
# Original Jacobi--Trudi matrices in compatible border frames

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). The complete original matrix is reindexed, not replaced by
border surrogates. Its determinant retains the produced common column sign.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The complete original profile matrix in the common-core row and column frame. -/
noncomputable def originalProfileFrame {n : ℕ} (P : Profile n) (a b c : ℕ)
    (hsize : n + 1 = a + 1 + (b + 1 + c)) :
    Matrix ((Fin a ⊕ Unit) ⊕ ((Unit ⊕ Fin b) ⊕ Fin c))
      ((Fin a ⊕ Unit) ⊕ ((Unit ⊕ Fin b) ⊕ Fin c)) Lambda :=
  (jtMatrix P.xi P.zeta).submatrix
    ((commonCoreFiniteRows a b c).trans (finCongr hsize.symm))
    ((commonCoreFiniteCols a b c).trans (finCongr hsize.symm))

/-- Literal natural row and column indices identify an entry of the entire
original frame. The supplied equalities are finite-index bookkeeping only. -/
theorem originalProfileFrame_entry_of_val {n : ℕ} (P : Profile n) (a b c : ℕ)
    (hsize : n + 1 = a + 1 + (b + 1 + c))
    (i j : (Fin a ⊕ Unit) ⊕ ((Unit ⊕ Fin b) ⊕ Fin c))
    (r s : Fin (n + 1))
    (hr : (commonCoreFiniteRows a b c i).val = r.val)
    (hs : (commonCoreFiniteCols a b c j).val = s.val) :
    originalProfileFrame P a b c hsize i j = hh (P.xi r - P.zeta s) := by
  have er : ((commonCoreFiniteRows a b c).trans (finCongr hsize.symm)) i = r := Fin.ext hr
  have es : ((commonCoreFiniteCols a b c).trans (finCongr hsize.symm)) j = s := Fin.ext hs
  change hh (P.xi _ - P.zeta _) = _
  rw [er, es]

/-- The whole original Schur determinant changes by exactly the common middle
column sign. Every row and column, including the boundary pivots, is retained. -/
theorem det_originalProfileFrame {n : ℕ} (P : Profile n) (a b c : ℕ)
    (hsize : n + 1 = a + 1 + (b + 1 + c)) :
    (originalProfileFrame P a b c hsize).det =
      Equiv.Perm.sign (commonCoreFiniteCycle b) * P.schur := by
  let e := finCongr hsize.symm
  let M := (jtMatrix P.xi P.zeta).submatrix e e
  have he : originalProfileFrame P a b c hsize =
      M.submatrix (commonCoreFiniteRows a b c) (commonCoreFiniteCols a b c) := by
    ext i j
    rfl
  rw [he, det_commonCoreFiniteFrame a b c]
  dsimp only [M]
  rw [Matrix.det_submatrix_equiv_self]
  rfl

end SkewCornerDescent.Matrix
