/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueLowStrips

/-!
# Original selected boundary strips contain exactly their own block indices

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). Valid original interval cuts identify each boundary strip
with every remaining index of its selected block. Empty proper minors remain
empty finite types. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Integer source cuts identify the actual first boundary strip's block. -/
theorem originalLeftStrip_block_eq {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (i : OriginalLeftStripIndex (hD := hD) P b d) : i.1.1.1.1 = b.val := by
  apply originalBlocks_label_injective P
  change interiorBlock P i.1.1.1.1.val = interiorBlock P b.val.val
  have hlo := i.1.2
  have hhi := i.2
  change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P i.1.1.1.1.val : ℤ) at hlo
  change (interiorBlock P i.1.1.1.1.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1 at hhi
  omega

/-- Every original remaining selected-block index occurs in a valid first strip. -/
noncomputable def originalLeftStripSourceEquiv {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (hupper : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P d) :
    Fin (originalRemovedSize (hD := hD) P b.val) ≃ OriginalLeftStripIndex (hD := hD) P b d where
  toFun k := ⟨⟨⟨⟨b.val, k⟩, hupper⟩, by
    change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P b.val.val : ℤ)
    omega⟩, by
    change (interiorBlock P b.val.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1
    omega⟩
  invFun i := (originalLeftStrip_block_eq P b d i) ▸ i.1.1.1.2
  left_inv k := by rfl
  right_inv i := by
    have hb := originalLeftStrip_block_eq P b d i
    rcases i with ⟨⟨⟨⟨t, k⟩, hi⟩, hlo⟩, hhi⟩
    change t = b.val at hb
    subst t
    rfl

/-- The last strip's integer source cuts identify exactly its selected block. -/
theorem originalRightStrip_block_eq {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (i : OriginalRightStripIndex (hD := hD) P b d) : i.1.1.1.1 = d.val := by
  apply originalBlocks_label_injective P
  change interiorBlock P i.1.1.1.1.val = interiorBlock P d.val.val
  have hlo := i.2
  have hhi := i.1.1.2
  change (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P i.1.1.1.1.val : ℤ) at hlo
  change (interiorBlock P i.1.1.1.1.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1 at hhi
  omega

/-- All original remaining indices of a selected block occur in its valid last strip. -/
noncomputable def originalRightStripSourceEquiv {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (hlower : originalResponseLowerCut P b < (interiorBlock P d.val.val : ℤ)) :
    Fin (originalRemovedSize (hD := hD) P d.val) ≃ OriginalRightStripIndex (hD := hD) P b d where
  toFun k := ⟨⟨⟨⟨d.val, k⟩, by
    change (interiorBlock P d.val.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1
    omega⟩, hlower⟩, by
    change (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P d.val.val : ℤ)
    omega⟩
  invFun i := (originalRightStrip_block_eq P b d i) ▸ i.1.1.1.2
  left_inv k := by rfl
  right_inv i := by
    have hb := originalRightStrip_block_eq P b d i
    rcases i with ⟨⟨⟨⟨t, k⟩, hi⟩, hlo⟩, hhi⟩
    change t = d.val at hb
    subst t
    rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
