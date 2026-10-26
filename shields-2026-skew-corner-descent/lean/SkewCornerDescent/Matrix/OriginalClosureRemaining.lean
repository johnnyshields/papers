/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureRemoval
import SkewCornerDescent.Matrix.OriginalUpperResponses

/-!
# Complete remaining source inventory of the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The two complete
remaining source lists biject with the actual remaining closure list. Exact selection
chooses every proper minor and retains every unselected block. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A literal source copy of one remaining original index, including its actual proper minor. -/
noncomputable def originalClosureRemainingCopy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (j : OriginalRemainingIndices (hD := hD) P) : OriginalRemainingIndices (hD := hD) Q :=
  ⟨originalClosureBlockCopy P Q v hQ upper j.1,
    Fin.cast (originalHorizontalClosure_removed_size P Q v hQ upper j.1).symm j.2⟩

/-- Both complete source remaining lists enumerate every actual closure remaining index once. -/
noncomputable def originalClosureRemainingEquiv {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    OriginalRemainingIndices (hD := hD) P ⊕ OriginalRemainingIndices (hD := hD) P ≃
      OriginalRemainingIndices (hD := hD) Q := by
  let e := originalClosureBlocksEquiv P Q v hQ
  let size := Sum.elim (originalRemovedSize (hD := hD) P) (originalRemovedSize (hD := hD) P)
  have hs : ∀ s, originalRemovedSize (hD := hD) Q (e s) = size s := by
    intro s
    rcases s with b | b
    · exact originalHorizontalClosure_removed_size P Q v hQ true b
    · exact originalHorizontalClosure_removed_size P Q v hQ false b
  exact ((Equiv.sumSigmaDistrib (fun s => Fin (size s))).symm.trans
    (Equiv.sigmaCongrRight (fun s => finCongr (hs s).symm))).trans
      (Equiv.sigmaCongrLeft (β := fun b => Fin (originalRemovedSize (hD := hD) Q b)) e)

/-- The first complete remaining summand is its actual upper-copy placement. -/
theorem originalClosureRemainingEquiv_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalClosureRemainingEquiv P Q v hQ (.inl j) =
      originalClosureRemainingCopy P Q v hQ true j := rfl

/-- The second complete remaining summand is its actual lower-copy placement. -/
theorem originalClosureRemainingEquiv_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalClosureRemainingEquiv P Q v hQ (.inr j) =
      originalClosureRemainingCopy P Q v hQ false j := rfl

/-- The complete actual remaining row and column endpoints have the same affine shift. -/
theorem originalHorizontalClosure_remaining_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (j : OriginalRemainingIndices (hD := hD) P) :
    let w := originalClosureBlockDisplacement P upper
    originalResponseRows Q (originalClosureRemainingCopy P Q v hQ upper j) =
      originalResponseRows P j + w.2 - w.1 ∧
    originalResponseCols Q (originalClosureRemainingCopy P Q v hQ upper j) =
      originalResponseCols P j + w.2 - w.1 := by
  dsimp only [originalResponseRows, originalResponseCols, originalClosureRemainingCopy]
  rw [originalHorizontalClosure_removed_row, originalHorizontalClosure_removed_col]
  exact ⟨(originalHorizontalClosure_copy_coordinates P Q v hQ upper
      (originalRemovedRow (hD := hD) P j.1 j.2)).2.1,
    (originalHorizontalClosure_copy_coordinates P Q v hQ upper
      (originalRemovedCol (hD := hD) P j.1 j.2)).2.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
