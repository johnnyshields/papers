/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalHorizontalSourceCapVectors
import SkewCornerDescent.Matrix.OriginalClosureJoinProjection

/-!
# Complete source-cap lists on the actual horizontal join sides

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Both complete source caps match the actual strict join-side index lists.
Literal geometry supplies all interval endpoints and private flags. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The upper-copy lower cap is the complete above-cut part of the actual
horizontal join, with every beta coordinate shifted by the source span. -/
theorem originalHorizontalClosure_above_cap_vectors {n m : ℕ}
    (P : Profile n) (H : Profile m) (v : ℤ × ℤ)
    (hH : originalHorizontalClosure P = translate v H.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    let bH := originalHorizontalClosureSelectedCopy P H v hH true b
    let dH := originalHorizontalClosureSelectedCopy P H v hH false d
    ∃ e : OriginalResponseInterval (hD := hD) P (some b) none ≃
      {i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) //
        P.xi 0 < originalResponseCols H i.1.1},
      ∀ i, originalResponseRows H (e i).val.1.1 = originalResponseRows P i.1.1 + P.xi 0 ∧
        originalResponseCols H (e i).val.1.1 = originalResponseCols P i.1.1 + P.xi 0 := by
  intro bH dH
  have hpriv := originalHorizontalClosure_profile_join_private P H v hH
  have hy : H.zeta (originalColSplitEquiv (hD := hD) H (.inl (some dH))) < P.xi 0 := by
    have he := (originalHorizontalClosure_retained_endpoints P H v hH false d).2
    simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte,
      add_sub_cancel_right, originalColSplitEquiv_selected] at he
    have hle := P.zeta_strictAnti.antitone (Fin.zero_le (interiorBlockLast P d.val.val).castSucc)
    have hspan := P.xi_sub_zeta (0 : Fin (n + 1))
    have hpos := P.r_pos (0 : Fin (n + 1))
    rw [originalColSplitEquiv_selected]
    dsimp only [dH]
    omega
  obtain ⟨s, hs⟩ := originalHorizontalClosure_source_cap_vectors P H v hH true false b
  let t := originalUpperPrivateCapEquiv (hD := hD) H bH dH (P.xi 0) hpriv.1 hpriv.2 hy
  refine ⟨s.trans t.symm, ?_⟩
  intro i
  exact hs i

/-- The lower-copy upper cap is the complete below-cut part of the actual
horizontal join, without any lost unit-component or proper-strip index. -/
theorem originalHorizontalClosure_below_cap_vectors {n m : ℕ}
    (P : Profile n) (H : Profile m) (v : ℤ × ℤ)
    (hH : originalHorizontalClosure P = translate v H.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    let bH := originalHorizontalClosureSelectedCopy P H v hH true b
    let dH := originalHorizontalClosureSelectedCopy P H v hH false d
    ∃ e : OriginalResponseInterval (hD := hD) P none (some d) ≃
      {i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) //
        originalResponseRows H i.1.1 < P.xi 0},
      ∀ i, originalResponseRows H (e i).val.1.1 = originalResponseRows P i.1.1 ∧
        originalResponseCols H (e i).val.1.1 = originalResponseCols P i.1.1 := by
  intro bH dH
  have hpriv := originalHorizontalClosure_profile_join_private P H v hH
  have hx : P.xi 0 < H.xi (originalRowSplitEquiv (hD := hD) H (.inl (some bH))) := by
    have he := (originalHorizontalClosure_retained_endpoints P H v hH true b).1
    simp only [originalClosureBlockDisplacement, ↓reduceIte, sub_zero,
      originalRowSplitEquiv_selected] at he
    have hpos := P.xi_pos b.val.val.succ
    rw [originalRowSplitEquiv_selected]
    dsimp only [bH]
    omega
  obtain ⟨s, hs⟩ := originalHorizontalClosure_source_cap_vectors P H v hH false true d
  let t := originalLowerPrivateCapEquiv (hD := hD) H bH dH (P.xi 0) hpriv.1 hpriv.2 hx
  refine ⟨s.trans t.symm, ?_⟩
  intro i
  have he := hs i
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at he
  exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
