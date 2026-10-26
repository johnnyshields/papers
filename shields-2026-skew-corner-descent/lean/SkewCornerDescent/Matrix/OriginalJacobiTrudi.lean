/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.BlockResponse
import SkewCornerDescent.Matrix.GeneratorDerivation

/-!
# Complete elimination of an original profile matrix

Supports local algebraic steps in `shields-2026-skew-corner-descent.tex`, «Equal windows and
the determinant defect» (`sec:normal-chart`) and «From response functions to literal copies»
(`sec:one-active`).

`lem:actual-elimination` uses a row split and a column split of the original JT matrix.
Here the determinant factorization is proved for any such complete split, retaining its
permutation sign and the entire removed determinant. The entries and determinant are bridged
to `SkewGluing.Profile.schur` over the canonical rational field.

Selecting the actual component occurrences and proving invertibility of their complementary
blocks are separate geometric obligations. The profile-level top-generator derivative used in
`lem:cofactor` is exported below, but identifying its minor with the geometric interior still
requires that construction. No upper-Hessenberg or literal-root conclusion is asserted here.
Sorry-free.
-/

open scoped Matrix

namespace SkewCornerDescent.Matrix

open SkewGluing

variable {n : ℕ} {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

/-- The original profile JT matrix in the canonical rational field. -/
noncomputable def originalMatrix (P : Profile n) : Matrix (Fin (n + 1)) (Fin (n + 1))
    actualField :=
  fun i j => originalMap (hh (P.xi i - P.zeta j))

/-- The determinant is the embedded canonical profile Schur function. -/
theorem det_originalMatrix (P : Profile n) :
    (originalMatrix P).det = originalMap P.schur := by
  exact (RingHom.map_det originalMap _).symm

/-- Independently split the original rows and columns into retained and removed lists. -/
noncomputable def splitOriginalMatrix (P : Profile n)
    (rows cols : m ⊕ k ≃ Fin (n + 1)) : Matrix (m ⊕ k) (m ⊕ k) actualField :=
  (originalMatrix P).submatrix rows cols

/-- The sign of the actual row/column rearrangement is not normalized away. -/
theorem det_splitOriginalMatrix (P : Profile n) (rows cols : m ⊕ k ≃ Fin (n + 1)) :
    (splitOriginalMatrix P rows cols).det =
      (Equiv.Perm.sign (cols.symm.trans rows) : actualField) * originalMap P.schur := by
  change (Matrix.reindex rows.symm cols.symm (originalMatrix P)).det = _
  rw [Matrix.det_reindex, det_originalMatrix, Equiv.symm_symm]

/-- Exact determinant elimination of a complete original JT block. -/
theorem original_det_eq_removed_mul_response (P : Profile n)
    (rows cols : m ⊕ k ≃ Fin (n + 1))
    [Invertible (splitOriginalMatrix P rows cols).toBlocks₂₂] :
    (Equiv.Perm.sign (cols.symm.trans rows) : actualField) * originalMap P.schur =
      (splitOriginalMatrix P rows cols).toBlocks₂₂.det *
        (retainedResponse (splitOriginalMatrix P rows cols).toBlocks₁₁
          (splitOriginalMatrix P rows cols).toBlocks₁₂
          (splitOriginalMatrix P rows cols).toBlocks₂₁
          (splitOriginalMatrix P rows cols).toBlocks₂₂).det := by
  rw [← det_splitOriginalMatrix]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (splitOriginalMatrix P rows cols)]
  exact det_eq_removed_mul_response _ _ _ _

/-- Each original JT entry has the actual generator derivative, including `h_0`. -/
theorem entryDeriv_originalMatrix (P : Profile n) (j : ℕ+) :
    entryDeriv (generatorDeriv j) (originalMatrix P) =
      fun i k => if P.xi i - P.zeta k = (j : ℤ) then 1 else 0 := by
  ext i k
  exact generatorDeriv_hh j _

/-- The top original generator occurs in exactly the northeast Jacobi--Trudi entry.
This is the entry-level cofactor step in `lem:cofactor`. -/
theorem entryDeriv_originalMatrix_top (P : Profile n) :
    entryDeriv (generatorDeriv P.topVar) (originalMatrix P) =
      fun i j => if i = 0 ∧ j = Fin.last n then 1 else 0 := by
  ext i j
  rw [entryDeriv_originalMatrix]
  have htop : (((P.topVar : ℕ+) : ℕ) : ℤ) = P.xi 0 := P.topVar_coe
  by_cases hij : i = 0 ∧ j = Fin.last n
  · rcases hij with ⟨rfl, rfl⟩
    simp [htop, P.zeta_last]
  · have hne :
        P.xi i - P.zeta j ≠ (((P.topVar : ℕ+) : ℕ) : ℤ) := by
      intro heq
      apply hij
      exact P.xi_sub_zeta_eq_top (by rw [htop] at heq; exact heq)
    simp [hne, hij]

/-- The original-field derivative of the profile Schur function at its top generator is the
signed complementary Jacobi--Trudi minor from `lem:cofactor`. This is the matrix minor itself;
identifying it with the connected-component product of the geometric interior is separate. -/
theorem generatorDeriv_originalSchur_top (P : Profile n) :
    generatorDeriv P.topVar (originalMap P.schur) =
      originalMap ((-1 : Lambda) ^ n *
        SkewGluing.betaDet (fun i : Fin n => P.xi i.succ)
          (fun i : Fin n => P.zeta i.castSucc)) := by
  rw [generatorDeriv_originalMap, Profile.pderiv_schur_top]

/-- Original generators strictly above the profile span do not occur in its Schur function. -/
theorem generatorDeriv_originalSchur_of_gt (P : Profile n) (j : ℕ+)
    (hj : P.xi 0 < ((j : ℕ) : ℤ)) :
    generatorDeriv j (originalMap P.schur) = 0 := by
  rw [generatorDeriv_originalMap, Profile.pderiv_schur_of_gt P hj]
  simp


end SkewCornerDescent.Matrix
