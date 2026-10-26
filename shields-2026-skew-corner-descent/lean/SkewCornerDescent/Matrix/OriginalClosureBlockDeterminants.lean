/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureBlockIntervals
import SkewCornerDescent.Matrix.OriginalRemovalLayout

/-!
# Actual copied block determinants in the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete original
block fibers are affinely reindexed, including unit pivots. Their determinant and exact
selection predicate are preserved without assuming a copied block inventory. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The complete original block fiber is reindexed, with no discarded source position. -/
noncomputable def originalClosureBlockFiberEquiv {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    {j : Fin n // interiorBlock P j = interiorBlock P i} ≃
      {q : Fin m // interiorBlock Q q =
        interiorBlock Q (originalClosureComplementaryCopy P Q v hQ upper i)} :=
  Equiv.ofBijective (fun j => ⟨originalClosureComplementaryCopy P Q v hQ upper j.val,
    (originalHorizontalClosure_block_fiber P Q v hQ upper i _).mpr ⟨j.val, rfl, j.property⟩⟩)
    ⟨by
      intro j k h
      apply Subtype.ext
      exact (originalHorizontalClosure_complementary_copy_strictMono P Q v hQ upper).injective
        (congrArg Subtype.val h), by
      intro q
      obtain ⟨j, hj, hp⟩ := (originalHorizontalClosure_block_fiber P Q v hQ upper i q.val).mp
        q.property
      exact ⟨⟨j, hp⟩, Subtype.ext hj.symm⟩⟩

/-- The whole copied original block matrix agrees entrywise with the source block matrix. -/
theorem originalHorizontalClosure_block_matrix {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    _root_.Matrix.submatrix
      ((jtMatrix (fun q : Fin m => Q.xi q.succ) (fun q => Q.zeta q.castSucc)).toSquareBlock
        (interiorBlock Q) (interiorBlock Q (originalClosureComplementaryCopy P Q v hQ upper i)))
      (originalClosureBlockFiberEquiv P Q v hQ upper i)
      (originalClosureBlockFiberEquiv P Q v hQ upper i) =
      (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
        (interiorBlock P) (interiorBlock P i) := by
  apply _root_.Matrix.ext
  intro j k
  change hh (Q.xi (originalClosureComplementaryCopy P Q v hQ upper j.val).succ -
    Q.zeta (originalClosureComplementaryCopy P Q v hQ upper k.val).castSucc) =
      hh (P.xi j.val.succ - P.zeta k.val.castSucc)
  cases upper with
  | true =>
    change hh (Q.xi (originalClosureComplementaryEquiv P Q v hQ (.inl j.val)).succ -
      Q.zeta (originalClosureComplementaryEquiv P Q v hQ (.inl k.val)).castSucc) = _
    rw [originalHorizontalClosure_complementary_xi_upper P Q v hQ,
      originalHorizontalClosure_complementary_zeta_upper P Q v hQ]
    congr 1
    ring
  | false =>
    change hh (Q.xi (originalClosureComplementaryEquiv P Q v hQ (.inr j.val)).succ -
      Q.zeta (originalClosureComplementaryEquiv P Q v hQ (.inr k.val)).castSucc) = _
    rw [originalHorizontalClosure_complementary_xi_lower P Q v hQ,
      originalHorizontalClosure_complementary_zeta_lower P Q v hQ]

/-- The actual complete block determinant is unchanged in either closure copy. -/
theorem originalHorizontalClosure_block_det {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) (i : Fin n) :
    ((jtMatrix (fun q : Fin m => Q.xi q.succ) (fun q => Q.zeta q.castSucc)).toSquareBlock
        (interiorBlock Q)
        (interiorBlock Q (originalClosureComplementaryCopy P Q v hQ upper i))).det =
      ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
        (interiorBlock P) (interiorBlock P i)).det := by
  classical
  rw [← _root_.Matrix.det_submatrix_equiv_self (originalClosureBlockFiberEquiv P Q v hQ upper i),
    originalHorizontalClosure_block_matrix]

/-- The actual canonical representative of any source block in either closure copy. -/
def originalClosureBlockCopy {n m : ℕ} (P : Profile n) (Q : Profile m)
    (v : ℤ × ℤ) (hQ : originalHorizontalClosure P = translate v Q.cells)
    (upper : Bool) (b : OriginalBlocks P) : OriginalBlocks Q :=
  ⟨originalClosureComplementaryCopy P Q v hQ upper b.val, by
    rw [originalHorizontalClosure_block_first, b.property]⟩

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Exact original determinant divisibility selects the same source block in each copy. -/
theorem originalHorizontalClosure_block_selected {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalBlocks P) :
    originalBlockSelected (hD := hD) Q (originalClosureBlockCopy P Q v hQ upper b) ↔
      originalBlockSelected (hD := hD) P b := by
  exact Iff.of_eq (congrArg (fun a : Lambda => cellSchur D hD.1 ∣ a)
    (originalHorizontalClosure_block_det P Q v hQ upper b.val))

end SelectedCoordinate

end SkewCornerDescent.Matrix
