/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureCapIntervals
import SkewCornerDescent.Matrix.OriginalClosureResponses

/-!
# Whole original exterior-cap responses of the literal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The genuine upper
left cap and lower right cap equal their complete source responses in the regular ring,
with every normal-dependent inverse entry retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Both actual retained cap endpoints have the complete source interval's affine shift. -/
theorem originalHorizontalClosure_cap_retained_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
    let w := originalClosureBlockDisplacement P upper
    Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (originalClosureCapLeft upper q))) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (originalClosureCapLeft upper b))) +
        w.2 - w.1 ∧
    Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (originalClosureCapRight upper q))) =
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (originalClosureCapRight upper b))) +
        w.2 - w.1 := by
  cases upper
  · change Q.xi (originalRowSplitEquiv (hD := hD) Q
        (.inl (some (originalHorizontalClosureSelectedCopy P Q v hQ false b)))) =
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) + n - n ∧
      Q.zeta (Fin.last m) = P.zeta (Fin.last n) + n - n
    refine ⟨(originalHorizontalClosure_retained_endpoints P Q v hQ false b).1, ?_⟩
    rw [Q.zeta_last, P.zeta_last]
    omega
  · change Q.xi 0 = P.xi 0 + P.xi 0 - 0 ∧
      Q.zeta (originalColSplitEquiv (hD := hD) Q
        (.inl (some (originalHorizontalClosureSelectedCopy P Q v hQ true b)))) =
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) + P.xi 0 - 0
    refine ⟨?_, (originalHorizontalClosure_retained_endpoints P Q v hQ true b).2⟩
    have hz : originalClosureUpperRow P Q v hQ 0 = (0 : Fin (m + 1)) := by
      apply Fin.ext
      simp only [originalClosureUpperRow, Fin.val_zero]
    simpa only [hz, sub_zero] using originalHorizontalClosure_xi_upper P Q v hQ 0

/-- The actual entire exterior-cap response equals its entire source response. -/
theorem originalHorizontalClosure_cap_response {n m : ℕ}
    (c : SelectedCoordinate D hD) (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
    c.originalLocalResponse Q (originalClosureCapLeft upper q) (originalClosureCapRight upper q) =
      c.originalLocalResponse P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) := by
  classical
  let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
  let e := originalClosureCapIntervalEquiv P Q v hQ upper b
  let w := originalClosureBlockDisplacement P upper
  let := c.originalResponseIntervalInverse P
    (originalClosureCapLeft upper b) (originalClosureCapRight upper b)
  let := c.originalResponseIntervalInverse Q
    (originalClosureCapLeft upper q) (originalClosureCapRight upper q)
  apply c.regularEmbedding_injective
  rw [c.originalLocalResponse_embedding_pruned, c.originalLocalResponse_embedding_pruned]
  apply intervalResponse_affine_reindex e _ _ _ _ (w.2 - w.1)
  · simpa only [add_sub_assoc] using
      (originalHorizontalClosure_cap_retained_endpoints P Q v hQ upper b).1
  · simpa only [add_sub_assoc] using
      (originalHorizontalClosure_cap_retained_endpoints P Q v hQ upper b).2
  · intro i
    simpa only [add_sub_assoc] using
      (originalHorizontalClosure_cap_interval_endpoints P Q v hQ upper b i).1
  · intro i
    simpa only [add_sub_assoc] using
      (originalHorizontalClosure_cap_interval_endpoints P Q v hQ upper b i).2

end SkewCornerDescent.Matrix.SelectedCoordinate
