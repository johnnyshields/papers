/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowConvexity
import SkewCornerDescent.Matrix.OriginalWindowRemainingMatrices
import SkewCornerDescent.Matrix.OriginalEndpointProfiles

/-!
# Actual retained endpoint intervals inside complete windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The complete
original retained interval is exactly the closed interval of whole window blocks.
Selected boundary proper minors and empty unit pivots remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Canonical source representatives strictly order their produced block labels. -/
theorem originalBlocks_label_strictMono {n : ℕ} (P : Profile n) :
    StrictMono (fun b : OriginalBlocks P => interiorBlock P b.val) := by
  intro b d hbd
  apply lt_of_le_of_ne (interiorBlock_mono P hbd.le)
  intro he
  exact (ne_of_lt hbd) (originalBlocks_label_injective P he)

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The integer response cuts include exactly the whole blocks between their selected endpoints. -/
theorem originalResponseInterval_block_bounds {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (a : OriginalBlocks P) :
    originalResponseLowerCut P (some b) < (interiorBlock P a.val : ℤ) ∧
        (interiorBlock P a.val : ℤ) < originalResponseUpperCut P (some d) ↔
      b.val ≤ a ∧ a ≤ d.val := by
  have hleft := (originalBlocks_label_strictMono P).le_iff_le
    (a := b.val) (b := a)
  have hright := (originalBlocks_label_strictMono P).le_iff_le
    (a := a) (b := d.val)
  change ((interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P a.val : ℤ) ∧
    (interiorBlock P a.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1) ↔ _
  rw [← hleft, ← hright]
  omega

/-- Complete whole-window positions between the two actual retained selected blocks. -/
abbrev OriginalWindowResponseInterval {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b d : OriginalSelectedBlocks (hD := hD) P) :=
  {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
    b.val ≤ i.1.val ∧ i.1.val ≤ d.val}

/-- Every actual retained source position belongs to the complete whole-window interval. -/
noncomputable def originalWindowResponseIntervalCopy {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hb : originalBlockInWindow P lo hi b.val) (hd : originalBlockInWindow P lo hi d.val)
    (i : OriginalResponseInterval (hD := hD) P (some b) (some d)) :
    OriginalWindowResponseInterval (hD := hD) P lo hi b d := by
  have hipos := (originalResponseInterval_block_bounds (hD := hD) P b d i.1.1.1).mp
    ⟨i.2, i.1.2⟩
  exact ⟨⟨⟨i.1.1.1, originalBlockInWindow_between P lo hi b.val i.1.1.1 d.val
    hb hd hipos.1 hipos.2⟩, i.1.1.2⟩, hipos⟩

/-- The full actual retained interval and the closed whole-window interval are identical. -/
noncomputable def originalWindowResponseIntervalEquiv {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hb : originalBlockInWindow P lo hi b.val) (hd : originalBlockInWindow P lo hi d.val) :
    OriginalResponseInterval (hD := hD) P (some b) (some d) ≃
      OriginalWindowResponseInterval (hD := hD) P lo hi b d where
  toFun := originalWindowResponseIntervalCopy P lo hi b d hb hd
  invFun i := by
    have hi := (originalResponseInterval_block_bounds (hD := hD) P b d i.val.1.val).mpr
      i.property
    exact ⟨⟨⟨i.val.1.val, i.val.2⟩, hi.2⟩, hi.1⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

end SelectedCoordinate
end SkewCornerDescent.Matrix
