/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Exact interval contraction of an upper-Hessenberg determinant

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original coefficients»
(`sec:dual`, `lem:original-transfer`). Expanding the first row factors each minor into
its actual selected subdiagonals and the remaining trailing determinant. The statement
holds over every commutative ring, without invertibility or a nonzero-normal assumption.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {R : Type*} [CommRing R]

/-- Only the first subdiagonal may be nonzero below the diagonal. -/
def IsUpperHessenberg {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (j : ℕ) + 1 < (i : ℕ) → A i j = 0

/-- Delete the first row and the last column of the first contracted interval. -/
def contractionMinor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (j : Fin (n + 1)) : Matrix (Fin n) (Fin n) R := A.submatrix Fin.succ j.succAbove

/-- The remaining trailing block after contracting the first `j+1` states. -/
def contractionTail {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (j : Fin (n + 1)) :=
  (contractionMinor A j).toSquareBlockProp (fun i : Fin n => ¬ (i : ℕ) < (j : ℕ))

/-- A first-row cofactor is exactly the subdiagonal product times its trailing block. -/
theorem contractionMinor_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : IsUpperHessenberg A) (j : Fin (n + 1)) :
    (contractionMinor A j).det =
      (∏ i : {i : Fin n // (i : ℕ) < (j : ℕ)}, A i.1.succ i.1.castSucc) *
        (contractionTail A j).det := by
  classical
  have hcol (i : Fin n) (hi : (i : ℕ) < (j : ℕ)) : j.succAbove i = i.castSucc := by
    exact Fin.succAbove_of_castSucc_lt j i hi
  have hz (i : Fin n) (hi : ¬ (i : ℕ) < (j : ℕ))
      (k : Fin n) (hk : (k : ℕ) < (j : ℕ)) : contractionMinor A j i k = 0 := by
    change A i.succ (j.succAbove k) = 0
    rw [hcol k hk]
    apply hA
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  rw [Matrix.twoBlockTriangular_det (contractionMinor A j)
    (fun i : Fin n => (i : ℕ) < (j : ℕ)) hz]
  change _ * (contractionTail A j).det = _
  congr 1
  have ht : ((contractionMinor A j).toSquareBlockProp
      (fun i : Fin n => (i : ℕ) < (j : ℕ))).IsUpperTriangular := by
    intro i k hik
    change A i.1.succ (j.succAbove k.1) = 0
    rw [hcol k.1 k.2]
    apply hA
    change (k.1 : ℕ) + 1 < (i.1 : ℕ) + 1
    exact Nat.succ_lt_succ (show (k.1 : ℕ) < (i.1 : ℕ) from hik)
  rw [Matrix.det_of_isUpperTriangular ht]
  apply Finset.prod_congr rfl
  intro i _
  change A i.1.succ (j.succAbove i.1) = _
  rw [hcol i.1 i.2]

/-- The exact first-interval recurrence, retaining every contraction and its sign. -/
theorem hessenberg_det_recurrence {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hA : IsUpperHessenberg A) :
    A.det = ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * A 0 j *
      ((∏ i : {i : Fin n // (i : ℕ) < (j : ℕ)}, A i.1.succ i.1.castSucc) *
        (contractionTail A j).det) := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [← contractionMinor_det A hA j]
  rfl

/-- An interval of `j+1` states uses exactly `j` selected subdiagonals, including
the one-state and whole-matrix boundary cases. -/
theorem selected_subdiagonal_product {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (t : R)
    (hsub : ∀ i : Fin n, A i.succ i.castSucc = t) (j : Fin (n + 1)) :
    (∏ i : {i : Fin n // (i : ℕ) < (j : ℕ)}, A i.1.succ i.1.castSucc) =
      t ^ (j : ℕ) := by
  classical
  let e : {i : Fin n // (i : ℕ) < (j : ℕ)} ≃ Fin (j : ℕ) :=
    { toFun := fun i => ⟨i.1, i.2⟩
      invFun := fun k => ⟨⟨k, by have := j.isLt; have := k.isLt; omega⟩, k.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Fintype.card {i : Fin n // (i : ℕ) < (j : ℕ)} = (j : ℕ) := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  simp only [hsub, Finset.prod_const, Finset.card_univ, hc]

/-- Constant selected subdiagonals give their exact normal cost in each interval. -/
theorem hessenberg_det_constant_subdiagonal {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hA : IsUpperHessenberg A)
    (t : R) (hsub : ∀ i : Fin n, A i.succ i.castSucc = t) :
    A.det = ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * A 0 j *
      (t ^ (j : ℕ) * (contractionTail A j).det) := by
  rw [hessenberg_det_recurrence A hA]
  simp_rw [selected_subdiagonal_product A t hsub]

/-- Killing the selected subdiagonals makes the complete response matrix triangular. -/
theorem mapped_hessenberg_upperTriangular {S : Type*} [CommRing S] {n : ℕ}
    (φ : R →+* S) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : IsUpperHessenberg A)
    (hsub : ∀ i : Fin n, φ (A i.succ i.castSucc) = 0) :
    (A.map φ).IsUpperTriangular := by
  intro i j hji
  change φ (A i j) = 0
  by_cases hfar : (j : ℕ) + 1 < (i : ℕ)
  · rw [hA i j hfar, map_zero]
  · have hi : i ≠ 0 := by intro he; subst i; exact (Fin.not_lt_zero j) hji
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    have hj : j = k.castSucc := by
      apply Fin.ext
      have hlt : (j : ℕ) < (k : ℕ) + 1 := hji
      simp only [Fin.val_succ] at hfar
      simp only [Fin.val_castSucc]
      omega
    rw [hj]
    exact hsub k

/-- The residue determinant is the complete product of diagonal responses. -/
theorem mapped_hessenberg_det {S : Type*} [CommRing S] {n : ℕ}
    (φ : R →+* S) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : IsUpperHessenberg A)
    (hsub : ∀ i : Fin n, φ (A i.succ i.castSucc) = 0) :
    φ A.det = ∏ i : Fin (n + 1), φ (A i i) := by
  rw [RingHom.map_det]
  change (A.map φ).det = ∏ i : Fin (n + 1), φ (A i i)
  rw [Matrix.det_of_isUpperTriangular (mapped_hessenberg_upperTriangular φ A hA hsub)]
  rfl

end SkewCornerDescent.Matrix
