/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.DesnanotJacobi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring

/-!
# Moving a row to the end, and collapsing a basis-vector border column

Two reindexings of a minor, and the collapse they are used for.  Deleting an interior row of a
tuple and appending it at the end is composition with an explicit permutation, so the determinant
picks up the sign of that permutation; and a bordered minor whose last column is the standard
basis vector supported on its largest row collapses to the minor on the remaining rows and
columns.  Together they turn a Desnanot--Jacobi expansion at a border column into an identity
among minors of the original matrix.

## Main results

* `Shields.snoc_succAbove_eq_comp`: `Fin.snoc (f ∘ i.succAbove) (f i) = f ∘ e` for the explicit
  permutation `e` -- the rotation followed by the cycle bringing `i` to the front.
* `Shields.sign_finRotate_trans_cycleRange_symm`: the sign of that permutation is `(-1) ^ (i + n)`.
* `Shields.det_submatrix_snoc_succAbove`: the determinant of that minor is
  `(-1) ^ (i + n)` times the original.
* `Shields.det_submatrix_border`: with `A` lower triangular with unit diagonal, a minor whose last
  column is the one indexed by its largest row equals the minor on the remaining rows and columns.

## Implementation notes

The sign is computed from `Fin.sign_cycleRange` and `sign_finRotate` rather than by counting
transpositions, which is what keeps it independent of `n`'s parity.

The border collapse expands along the last column with `Shields.det_of_basis_column`, which is
where the import of the Desnanot--Jacobi file comes from; nothing else here needs it.

Matrices are indexed by `ℕ` with rows and columns selected by tuples `Fin k → ℕ`, so that a minor
of a semi-infinite matrix is a determinant of a `Fin k` matrix without a containing block being
named.

## Tags

determinant, minor, submatrix, reindex, snoc, succAbove, triangular matrix
-/

namespace Shields

open Matrix

variable {R : Type*} [CommRing R]

/-! ### Reindexing -/

/-- Moving one entry of a tuple to the end, leaving the others in order, is
composition with a permutation: the rotation followed by the cycle that brings
`i` to the front. -/
theorem snoc_succAbove_eq_comp {α : Type*} {n : ℕ} (f : Fin (n + 1) → α)
    (i : Fin (n + 1)) :
    (Fin.snoc (f ∘ i.succAbove) (f i) : Fin (n + 1) → α)
      = f ∘ ⇑((finRotate (n + 1)).trans i.cycleRange.symm) := by
  rw [Fin.snoc_eq_cons_rotate]
  have hc : (Fin.cons (f i) (f ∘ i.succAbove) : Fin (n + 1) → α) = f ∘ ⇑i.cycleRange.symm :=
    Fin.cons_removeNth_eq_comp_cycleRange_symm f i
  funext j
  have := congrFun hc (finRotate (n + 1) j)
  simpa using this

/-- **The sign of that permutation is `(-1)^(i + n)`**, computed from `Fin.sign_cycleRange` and
`sign_finRotate` rather than by counting transpositions -- which is what keeps it independent of
`n`'s parity. -/
theorem sign_finRotate_trans_cycleRange_symm {n : ℕ} (i : Fin (n + 1)) :
    Equiv.Perm.sign ((finRotate (n + 1)).trans i.cycleRange.symm) = (-1) ^ ((i : ℕ) + n) := by
  have h1 : (finRotate (n + 1)).trans i.cycleRange.symm
      = i.cycleRange.symm * finRotate (n + 1) := rfl
  rw [h1, map_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    sign_finRotate, Nat.add_sub_cancel, pow_add]

/-- The determinant of a minor whose rows are those of `f` with the entry at `i`
moved to the end. -/
theorem det_submatrix_snoc_succAbove {n : ℕ} (A : Matrix ℕ ℕ R)
    (f : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℕ) (i : Fin (n + 1)) :
    (A.submatrix (Fin.snoc (f ∘ i.succAbove) (f i)) σ).det
      = (-1) ^ ((i : ℕ) + n) * (A.submatrix f σ).det := by
  rw [snoc_succAbove_eq_comp]
  have h : A.submatrix (f ∘ ⇑((finRotate (n + 1)).trans i.cycleRange.symm)) σ
      = (A.submatrix f σ).submatrix ((finRotate (n + 1)).trans i.cycleRange.symm) id := rfl
  rw [h, Matrix.det_permute]
  congr 1
  rw [sign_finRotate_trans_cycleRange_symm]
  push_cast
  ring

/-! ### The border column -/

/-- If the last column of a minor is the column indexed by its largest row, the
minor collapses to the one on the remaining rows and columns. -/
theorem det_submatrix_border {n : ℕ} {A : Matrix ℕ ℕ R} {c : ℕ}
    (hlow : ∀ i j : ℕ, i < j → A i j = 0) (hdiag : ∀ i : ℕ, A i i = 1)
    (ν : Fin (n + 1) → ℕ) (hc : ν (Fin.last n) = c)
    (hν : ∀ j : Fin n, ν j.castSucc < c)
    (τ : Fin n → ℕ) :
    (A.submatrix ν (Fin.snoc τ c)).det
      = (A.submatrix (ν ∘ Fin.castSucc) τ).det := by
  have hcol : ∀ k : Fin (n + 1),
      (A.submatrix ν (Fin.snoc τ c)) k (Fin.last n)
        = if k = Fin.last n then 1 else 0 := by
    intro k
    simp only [Matrix.submatrix_apply, Fin.snoc_last]
    rcases eq_or_ne k (Fin.last n) with rfl | hk
    · simp [hc, hdiag]
    · rw [if_neg hk]
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      exact hlow _ _ (hν j)
  rw [det_of_basis_column _ (Fin.last n) (Fin.last n) hcol]
  have hs : ((-1 : R)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [hs, one_mul, Fin.succAbove_last]
  congr 1
  funext a b
  simp [Fin.snoc_castSucc]

end Shields
