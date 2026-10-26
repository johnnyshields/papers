/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.MergeBetaSets

/-!
# The actual distinguished-seam cut and merge recurrence

Formalizes `eq:cut-merge` at every admissible joining gap in
`shields-2026-skew-class-inflation.tex`.  The two principal pieces are
identified with the original full normalized profiles.  Sorry-free.
-/

namespace SkewClassInflation.Profile

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- The left principal function at the joining seam is the original left function. -/
theorem join_left_function {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (leftOfSeam (join P Q d hP hQ)
      (⟨n, by omega⟩ : Fin (n + m + 1))).toBetaDiagram.schur =
      P.toBetaDiagram.schur := by
  rw [leftOfSeam, slice_schur]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change complete ((join P Q d hP hQ).xi (sliceEmbedding 0 n (by omega) i) -
    (join P Q d hP hQ).zeta (sliceEmbedding 0 n (by omega) j)) = complete (P.xi i - P.zeta j)
  have hx := join_xi_left P Q d hP hQ i
  have hz := join_zeta_left P Q d hP hQ j
  have hi : sliceEmbedding 0 n (by omega) i =
      (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + m + 2)) := by
    apply Fin.ext
    exact Nat.zero_add _
  have hj : sliceEmbedding 0 n (by omega) j =
      (⟨j.val, by have := j.isLt; omega⟩ : Fin (n + m + 2)) := by
    apply Fin.ext
    exact Nat.zero_add _
  rw [hi, hj, hx, hz]
  congr 1
  ring

/-- The right principal function at the joining seam is the original right function. -/
theorem join_right_function {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    (rightOfSeam (join P Q d hP hQ)
      (⟨n, by omega⟩ : Fin (n + m + 1))).toBetaDiagram.schur =
      Q.toBetaDiagram.schur := by
  rw [rightOfSeam, slice_schur]
  let e : Fin (m + 1) ≃ Fin (n + m - n + 1) := finCongr (by omega)
  rw [← Matrix.det_submatrix_equiv_self e]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hi : sliceEmbedding (n + 1) (n + m - n) (by omega) (e i) =
      (⟨n + 1 + i.val, by have := i.isLt; omega⟩ : Fin (n + m + 2)) := by
    apply Fin.ext
    rfl
  have hj : sliceEmbedding (n + 1) (n + m - n) (by omega) (e j) =
      (⟨n + 1 + j.val, by have := j.isLt; omega⟩ : Fin (n + m + 2)) := by
    apply Fin.ext
    rfl
  change complete ((join P Q d hP hQ).xi (sliceEmbedding _ _ _ (e i)) -
    (join P Q d hP hQ).zeta (sliceEmbedding _ _ _ (e j))) = complete (Q.xi i - Q.zeta j)
  rw [hi, hj, join_xi_right, join_zeta_right]

/-- The genuine connected join has its product-minus-contraction determinant identity. -/
theorem join_schur {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0)
    (hJ : Staircase.Thick (join P Q d hP hQ)) :
    (join P Q d hP hQ).toBetaDiagram.schur =
      P.toBetaDiagram.schur * Q.toBetaDiagram.schur -
        complete d * (merge P Q d hP hQ).toBetaDiagram.schur := by
  have he := schur_join_formula (join P Q d hP hQ) hJ
    (⟨n, by omega⟩ : Fin (n + m + 1))
  have hg : (join P Q d hP hQ).g ⟨n, by omega⟩ = d := joinGaps_middle P Q d
  rw [join_left_function, join_right_function, hg] at he
  exact he

/-- A genuine zero join is the product of its original pieces minus its actual merger. -/
theorem zeroJoin_schur {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) :
    (zeroJoin P Q).toBetaDiagram.schur =
      P.toBetaDiagram.schur * Q.toBetaDiagram.schur -
        (merge P Q 0 (P.r_pos _) (Q.r_pos _)).toBetaDiagram.schur := by
  have he := join_schur P Q 0 (P.r_pos _) (Q.r_pos _) (zeroJoin_thick P Q hP hQ)
  simpa only [zeroJoin, Nat.cast_zero, complete_zero, one_mul] using he

end SkewClassInflation.Profile
