/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedComponentLookup
import SkewCornerDescent.Matrix.OriginalHessenbergInventory

/-!
# True cap tops as selected component content extrema

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The original ordered selected inventory supplies its first and last components.
Their actual least and greatest contents identify the full exterior cap tops.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The first actual selected occurrence precedes every selected block. -/
theorem selected_first_le {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩ ≤ b := by
  have hle : (⟨0, hB⟩ : Fin (originalSelectedCount (hD := hD) P)) ≤
      (originalSelectedEnumeration (hD := hD) P).symm b := by
    change 0 ≤ _
    exact Nat.zero_le _
  have h := (originalSelectedEnumeration (hD := hD) P).monotone hle
  rw [OrderIso.apply_symm_apply] at h
  change originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩ ≤ b at h
  exact h

/-- The last actual selected occurrence follows every selected block. -/
theorem selected_le_last {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    b ≤ originalSelectedEnumeration (hD := hD) P
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩ := by
  have hi := ((originalSelectedEnumeration (hD := hD) P).symm b).isLt
  have hle : (originalSelectedEnumeration (hD := hD) P).symm b ≤
      (⟨originalSelectedCount (hD := hD) P - 1, by omega⟩ :
        Fin (originalSelectedCount (hD := hD) P)) := by
    change ((originalSelectedEnumeration (hD := hD) P).symm b).val ≤
      originalSelectedCount (hD := hD) P - 1
    omega
  have h := (originalSelectedEnumeration (hD := hD) P).monotone hle
  rw [OrderIso.apply_symm_apply] at h
  change b ≤ originalSelectedEnumeration (hD := hD) P
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩ at h
  exact h

/-- The actual first cap top is the parent top minus the first selected
component's least content. -/
theorem originalFirstCapDistance_contents {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalFirstCapDistance P b = P.xi 0 - minContent (interiorBlockCells P b.val.val) := by
  rw [interiorBlockCells_minContent P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)]
  rfl

/-- The actual last cap top is one past the last selected component's greatest content. -/
theorem originalLastCapDistance_contents {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalLastCapDistance P b = maxContent (interiorBlockCells P b.val.val) + 1 := by
  obtain ⟨c⟩ := exists_selectedCoordinate hD
  have ht := c.originalSelected_endpoint_distance P b
  rw [originalSelected_maxContent P b, interiorBlockCells_minContent P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)]
  unfold originalLastCapDistance
  rw [P.zeta_last]
  have hs := c.span_eq
  have hsz : (c.top : ℤ) = (span D : ℤ) := by exact_mod_cast hs
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
