/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A determinant with an eliminated last column

The linear-algebra step behind both the Schur-complement identity `s_A = κ_A [HG]_M` and the
splice identity of `shields-2026-skew-coframe-rigidity.tex` («Rigidity with the same literal
cap», `sc:splice-identity`).  If a combination of the earlier columns cancels the last column in
every row but the first, the determinant is the signed minor times the surviving first-row entry.
Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Eliminating the last column below the first row factors the determinant as the signed minor
(first row and last column deleted) times the surviving entry of the combined last column. -/
theorem det_eq_of_eliminated_column (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (t : Fin n → R)
    (ht : ∀ i : Fin n, ∑ j, M i.succ j.castSucc * t j + M i.succ (Fin.last n) = 0) :
    M.det = (-1) ^ n * (M.submatrix Fin.succ Fin.castSucc).det *
      (M 0 (Fin.last n) + ∑ j, M 0 j.castSucc * t j) := by
  classical
  let c : Fin (n + 1) → R := Fin.snoc (α := fun _ => R) t 1
  have hdet := Matrix.det_updateCol_sum M (Fin.last n) c
  have hc : c (Fin.last n) = 1 := by simp [c]
  rw [hc, one_smul] at hdet
  have hcol : ∀ k, (∑ i, c i • M k i) = M k (Fin.last n) + ∑ j : Fin n, t j * M k j.castSucc := by
    intro k
    rw [Fin.sum_univ_castSucc]
    simp only [c, Fin.snoc_castSucc, Fin.snoc_last, smul_eq_mul, one_mul]
    rw [add_comm]
  have hsc : M.det = (M.updateCol (Fin.last n) fun k => ∑ i, c i • M k i).det := hdet.symm
  rw [hsc, Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_succ]
  have hrest : ∀ i : Fin n, (M.updateCol (Fin.last n) fun k => ∑ i, c i • M k i) i.succ
      (Fin.last n) = 0 := by
    intro i
    simp only [Matrix.updateCol_apply, ite_true]
    rw [hcol]
    have e : ∑ j, t j * M i.succ j.castSucc = ∑ j, M i.succ j.castSucc * t j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e, add_comm]
    exact ht i
  simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have hsub : ((M.updateCol (Fin.last n) fun k => ∑ i, c i • M k i).submatrix
      (Fin.succAbove 0) (Fin.last n).succAbove) = M.submatrix Fin.succ Fin.castSucc := by
    ext i j
    simp [Fin.succAbove_last, (Fin.castSucc_lt_last j).ne]
  rw [hsub]
  simp only [Matrix.updateCol_apply, ite_true, hcol, Fin.val_zero, Fin.val_last, zero_add]
  have e : ∑ j, t j * M 0 j.castSucc = ∑ j, M 0 j.castSucc * t j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  ring

end SkewCoframeRigidity.FixedCap
