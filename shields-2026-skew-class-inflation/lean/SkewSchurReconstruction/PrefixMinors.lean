/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/PrefixMinors.lean

import SkewSchurReconstruction.MaximalCofactors
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Prefix-minor elimination

Formalizes the determinant-linear relation in «Reconstruction from the first-row deletion»
(`subsec:child-separation`, `lem:two-cofactor-reconstruction`) of
`shields-2026-skew-boundary-reconstruction.tex`.  Every prefix functional annihilates
an actual maximal-cofactor vector; the relation is derived from its row kernel.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

variable {R : Type*} [CommRing R] {n k : ℕ}

/-- The minor with prescribed rows and prefix columns, followed by column `j`. -/
noncomputable def columnPrefixMinor (M : Matrix (Fin n) (Fin (n + 1)) R)
    (r : Fin (k + 1) → Fin n) (s : Fin k → Fin (n + 1)) (j : Fin (n + 1)) : R :=
  (M.submatrix r (Fin.snoc s j)).det

/-- Expansion in the final column makes its dependence on that column explicit. -/
theorem columnPrefixMinor_expansion (M : Matrix (Fin n) (Fin (n + 1)) R)
    (r : Fin (k + 1) → Fin n) (s : Fin k → Fin (n + 1)) (j : Fin (n + 1)) :
    columnPrefixMinor M r s j =
      ∑ i : Fin (k + 1), (-1) ^ (i.val + k) * M (r i) j *
        (M.submatrix (r ∘ i.succAbove) s).det := by
  rw [columnPrefixMinor, Matrix.det_succ_column _ (Fin.last k)]
  apply Finset.sum_congr rfl
  intro i _
  have hminor : (M.submatrix r (Fin.snoc s j)).submatrix i.succAbove
      (Fin.last k).succAbove = M.submatrix (r ∘ i.succAbove) s := by
    apply Matrix.ext
    intro a b
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, Fin.snoc_castSucc,
      Function.comp_apply]
  rw [hminor]
  simp only [Matrix.submatrix_apply, Fin.snoc_last, Fin.val_last]

/-- All prefix functionals give exact cofactor annihilations, not additional assumptions. -/
theorem columnPrefixMinor_cofactor_relation (M : Matrix (Fin n) (Fin (n + 1)) R)
    (r : Fin (k + 1) → Fin n) (s : Fin k → Fin (n + 1)) :
    ∑ j, signedMaximalCofactor M j * columnPrefixMinor M r s j = 0 := by
  classical
  simp_rw [columnPrefixMinor_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  calc
    (∑ j, signedMaximalCofactor M j *
        ((-1) ^ (i.val + k) * M (r i) j * (M.submatrix (r ∘ i.succAbove) s).det)) =
        ((-1) ^ (i.val + k) * (M.submatrix (r ∘ i.succAbove) s).det) *
          ∑ j, M (r i) j * signedMaximalCofactor M j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [row_sum_signedMaximalCofactor_eq_zero, mul_zero]

/-- A column already in the prefix makes the determinant vanish identically. -/
theorem columnPrefixMinor_eq_zero_of_repeated (M : Matrix (Fin n) (Fin (n + 1)) R)
    (r : Fin (k + 1) → Fin n) (s : Fin k → Fin (n + 1)) (i : Fin k) :
    columnPrefixMinor M r s (s i) = 0 := by
  unfold columnPrefixMinor
  apply Matrix.det_zero_of_column_eq (i := i.castSucc) (j := Fin.last k)
  · exact (ne_of_lt i.castSucc_lt_last)
  · intro a
    simp only [Matrix.submatrix_apply, Fin.snoc_castSucc, Fin.snoc_last]

end SkewSchurReconstruction
