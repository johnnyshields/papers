/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.PrivateSidePartition
import SkewCornerDescent.Matrix.OriginalPrivateCapSides

/-!
# Complete beta lists of both private interval sides

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
After excluding the private unit, every remaining original index belongs to
one of the two complete clipped caps. Both endpoint lists are preserved, so
cross-side matrix entries can be transported as well. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The complete nonunit interval is exactly its two strict cap parts.
No inverse entries or cross-component couplings are dropped by the equivalence. -/
theorem originalPrivateInterval_cap_vectors {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (k : ℤ)
    (hk : diagLo P.cells k = diagHi P.cells k)
    (hp : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (hb : k < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))
    (hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) < k) :
    ∃ e : {i : OriginalResponseInterval (hD := hD) P (some b) (some d) //
        ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} ≃
      ({i : OriginalWholeWindowRemaining (hD := hD) P 0 k //
          originalCapBlockSide true d i.1.val} ⊕
        {i : OriginalWholeWindowRemaining (hD := hD) P k (P.xi 0) //
          originalCapBlockSide false b i.1.val}),
      ∀ j,
        originalResponseRows P (e.symm j).val.1.1 =
          Sum.elim (fun i => originalResponseRows P ⟨i.val.1.val, i.val.2⟩)
            (fun i => originalResponseRows P ⟨i.val.1.val, i.val.2⟩) j ∧
        originalResponseCols P (e.symm j).val.1.1 =
          Sum.elim (fun i => originalResponseCols P ⟨i.val.1.val, i.val.2⟩)
            (fun i => originalResponseCols P ⟨i.val.1.val, i.val.2⟩) j := by
  let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseCols P i.1.1
  obtain ⟨s, hs⟩ := private_nonunit_sides_equiv row col k
    (originalInterval_private_cut_trichotomy P (some b) (some d) k hk hp)
  let lower := originalLowerPrivateCapEquiv (hD := hD) P b d k hk hp hb
  let upper := originalUpperPrivateCapEquiv (hD := hD) P b d k hk hp hd
  refine ⟨s.trans (Equiv.sumCongr lower upper), ?_⟩
  intro j
  rcases j with j | j
  · exact hs (.inl (lower.symm j))
  · exact hs (.inr (upper.symm j))

end SkewCornerDescent.Matrix.SelectedCoordinate
