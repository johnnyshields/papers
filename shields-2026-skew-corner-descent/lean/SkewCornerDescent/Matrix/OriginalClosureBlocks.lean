/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureBlockCells

/-!
# Complete canonical block inventory of the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Both source block
lists biject with the entire actual closure block list, including unselected blocks and
unit pivots. The literal index order fixes the copy placements. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The two canonical complete block lists cover the actual closure block list exactly once. -/
noncomputable def originalClosureBlocksEquiv {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    OriginalBlocks P ⊕ OriginalBlocks P ≃ OriginalBlocks Q :=
  Equiv.ofBijective (Sum.elim (originalClosureBlockCopy P Q v hQ true)
    (originalClosureBlockCopy P Q v hQ false)) ⟨by
      intro a b h
      rcases a with a | a <;> rcases b with b | b
      · apply congrArg Sum.inl
        apply Subtype.ext
        exact (originalHorizontalClosure_complementary_copy_strictMono P Q v hQ true).injective
          (congrArg Subtype.val h)
      · have hv := congrArg (fun b : OriginalBlocks Q => b.val.val) h
        change a.val.val = n + b.val.val at hv
        have ha := a.val.isLt
        omega
      · have hv := congrArg (fun b : OriginalBlocks Q => b.val.val) h
        change n + a.val.val = b.val.val at hv
        have hb := b.val.isLt
        omega
      · apply congrArg Sum.inr
        apply Subtype.ext
        exact (originalHorizontalClosure_complementary_copy_strictMono P Q v hQ false).injective
          (congrArg Subtype.val h), by
      intro b
      obtain ⟨s, hs⟩ := (originalClosureComplementaryEquiv P Q v hQ).surjective b.val
      rcases s with j | j
      · have hj : interiorBlockFirst P j = j := by
          apply (originalHorizontalClosure_complementary_copy_strictMono P Q v hQ true).injective
          have hb := b.property
          rw [← hs] at hb
          change interiorBlockFirst Q (originalClosureComplementaryCopy P Q v hQ true j) =
            originalClosureComplementaryCopy P Q v hQ true j at hb
          rw [originalHorizontalClosure_block_first] at hb
          exact hb
        exact ⟨.inl ⟨j, hj⟩, Subtype.ext hs⟩
      · have hj : interiorBlockFirst P j = j := by
          apply (originalHorizontalClosure_complementary_copy_strictMono P Q v hQ false).injective
          have hb := b.property
          rw [← hs] at hb
          change interiorBlockFirst Q (originalClosureComplementaryCopy P Q v hQ false j) =
            originalClosureComplementaryCopy P Q v hQ false j at hb
          rw [originalHorizontalClosure_block_first] at hb
          exact hb
        exact ⟨.inr ⟨j, hj⟩, Subtype.ext hs⟩⟩

/-- The first summand enumerates precisely the translated complete source-copy blocks. -/
theorem originalClosureBlocksEquiv_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (b : OriginalBlocks P) :
    originalClosureBlocksEquiv P Q v hQ (.inl b) = originalClosureBlockCopy P Q v hQ true b := rfl

/-- The second summand enumerates precisely the unshifted complete source-copy blocks. -/
theorem originalClosureBlocksEquiv_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (b : OriginalBlocks P) :
    originalClosureBlocksEquiv P Q v hQ (.inr b) = originalClosureBlockCopy P Q v hQ false b := rfl

end SkewCornerDescent.Matrix
