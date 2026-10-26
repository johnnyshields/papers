/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.Hessenberg
import Mathlib.Algebra.BigOperators.Fin

/-!
# Full triangular inverse trace against a Hessenberg first jet

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Triangular inverse support and the actual first jet's Hessenberg support leave
exactly the onsite terms and adjacent pairs. All retained matrix entries are
unchanged; distant entries disappear by support, not by a diagonal substitution.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Only onsite and adjacent pairs survive the full inverse-trace contraction. -/
theorem upper_hessenberg_trace {F : Type*} [CommRing F] {n : ℕ}
    (U B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hU : U.IsUpperTriangular) (hB : IsUpperHessenberg B) :
    Matrix.trace (U * B) = (∑ i, U i i * B i i) +
      ∑ i : Fin n, U i.castSucc i.succ * B i.succ i.castSucc := by
  classical
  have he (i j : Fin (n + 1)) : U i j * B j i =
      (if j = i then U i i * B i i else 0) +
        (if j.val = i.val + 1 then U i j * B j i else 0) := by
    by_cases heq : j = i
    · subst j
      simp
    · by_cases hadj : j.val = i.val + 1
      · simp [heq, hadj]
      · simp only [ite_eq_right heq, ite_eq_right hadj, zero_add]
        by_cases hlt : j < i
        · rw [hU hlt, zero_mul]
        · rw [hB j i (by have hn : j.val ≠ i.val := fun h => heq (Fin.ext h); omega),
            mul_zero]
  have htrace : Matrix.trace (U * B) = (∑ i, U i i * B i i) +
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        if j.val = i.val + 1 then U i j * B j i else 0 := by
    calc
      _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          ((if j = i then U i i * B i i else 0) +
            (if j.val = i.val + 1 then U i j * B j i else 0)) := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact he i j
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
  rw [htrace]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hlast : (∑ j : Fin (n + 1),
      if j.val = (Fin.last n).val + 1 then U (Fin.last n) j * B j (Fin.last n) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.val_last]; omega)]
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hne
    rw [ite_eq_right (by
      intro h
      apply hne
      apply Fin.ext
      exact h)]
  · simp

end SkewCornerDescent.Matrix
