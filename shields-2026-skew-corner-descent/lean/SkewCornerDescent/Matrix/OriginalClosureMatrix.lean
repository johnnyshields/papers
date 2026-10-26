/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureBeta
import SkewCornerDescent.Matrix.InteriorBlocks

/-!
# Complete original complementary matrix of the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The two complete
source endpoint lists identify both diagonal copies and the entire off-diagonal
connector. No original row or column is discarded. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The two complete complementary index lists in their actual closure order. -/
def originalClosureComplementaryEquiv {n m : ℕ} (P : Profile n) (Q : Profile m)
    (v : ℤ × ℤ) (hQ : originalHorizontalClosure P = translate v Q.cells) :
    Fin n ⊕ Fin n ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (by
    have hm := (originalHorizontalClosure_profile_rows P Q v hQ).1
    omega))

/-- Upper-copy original rows are the source rows with their common affine shift. -/
theorem originalHorizontalClosure_complementary_xi_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    Q.xi ((originalClosureComplementaryEquiv P Q v hQ (.inl i)).succ) =
      P.xi i.succ + P.xi 0 := by
  have he : (originalClosureComplementaryEquiv P Q v hQ (.inl i)).succ =
      originalClosureUpperRow P Q v hQ i.succ := by apply Fin.ext; rfl
  rw [he]
  exact originalHorizontalClosure_xi_upper P Q v hQ i.succ

/-- Upper-copy original columns are the source columns with the same affine shift. -/
theorem originalHorizontalClosure_complementary_zeta_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    Q.zeta ((originalClosureComplementaryEquiv P Q v hQ (.inl i)).castSucc) =
      P.zeta i.castSucc + P.xi 0 := by
  have he : (originalClosureComplementaryEquiv P Q v hQ (.inl i)).castSucc =
      originalClosureUpperRow P Q v hQ i.castSucc := by apply Fin.ext; rfl
  rw [he]
  exact originalHorizontalClosure_zeta_upper P Q v hQ i

/-- Lower-copy original rows are the source rows without an affine shift. -/
theorem originalHorizontalClosure_complementary_xi_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    Q.xi ((originalClosureComplementaryEquiv P Q v hQ (.inr i)).succ) =
      P.xi i.succ := by
  have he : (originalClosureComplementaryEquiv P Q v hQ (.inr i)).succ =
      originalClosureLowerRow P Q v hQ i.succ := by
    apply Fin.ext
    change n + i.val + 1 = n + (i.val + 1)
    omega
  rw [he]
  exact originalHorizontalClosure_xi_lower P Q v hQ i

/-- Lower-copy original columns are the source columns without an affine shift. -/
theorem originalHorizontalClosure_complementary_zeta_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i : Fin n) :
    Q.zeta ((originalClosureComplementaryEquiv P Q v hQ (.inr i)).castSucc) =
      P.zeta i.castSucc := by
  have he : (originalClosureComplementaryEquiv P Q v hQ (.inr i)).castSucc =
      originalClosureLowerRow P Q v hQ i.castSucc := by apply Fin.ext; rfl
  rw [he]
  exact originalHorizontalClosure_zeta_lower P Q v hQ i.castSucc

/-- The full original complementary matrix has two source copies and its literal connector.
The lower cross block vanishes by the original endpoint ordering, not by pruning. -/
theorem originalHorizontalClosure_complementary_matrix {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    (jtMatrix (fun i : Fin m => Q.xi i.succ) (fun j => Q.zeta j.castSucc)).submatrix
        (originalClosureComplementaryEquiv P Q v hQ)
        (originalClosureComplementaryEquiv P Q v hQ) =
      _root_.Matrix.fromBlocks
        (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc))
        (jtMatrix (fun i : Fin n => P.xi i.succ + P.xi 0)
          (fun j => P.zeta j.castSucc)) 0
        (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)) := by
  apply _root_.Matrix.ext
  intro a b
  rcases a with i | i <;> rcases b with j | j
  · change hh (_ - _) = hh (_ - _)
    dsimp only
    rw [originalHorizontalClosure_complementary_xi_upper P Q v hQ,
      originalHorizontalClosure_complementary_zeta_upper P Q v hQ]
    congr 1
    ring
  · change hh (_ - _) = hh (_ - _)
    dsimp only
    rw [originalHorizontalClosure_complementary_xi_upper P Q v hQ,
      originalHorizontalClosure_complementary_zeta_lower P Q v hQ]
  · change hh (_ - _) = 0
    dsimp only
    rw [originalHorizontalClosure_complementary_xi_lower P Q v hQ,
      originalHorizontalClosure_complementary_zeta_upper P Q v hQ]
    apply hh_of_neg
    have hr := P.xi_strictAnti (show (0 : Fin (n + 1)) < i.succ by
      change 0 < i.val + 1; omega)
    have hc := P.zeta_nonneg j.castSucc
    omega
  · change hh (_ - _) = hh (_ - _)
    dsimp only
    rw [originalHorizontalClosure_complementary_xi_lower P Q v hQ,
      originalHorizontalClosure_complementary_zeta_lower P Q v hQ]

end SkewCornerDescent.Matrix
