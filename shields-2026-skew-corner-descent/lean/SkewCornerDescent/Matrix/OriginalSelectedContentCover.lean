/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalSelectedMiddleCover

/-!
# Actual middle content bands are covered by complete parent-row strips

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The extreme original selected beta coordinates bound a genuine middle
content band. Monotonicity of both parent-row beta lists places every
cell of that band inside the complete selected-middle row cover.
No cell-coordinate or strip-membership premise is added. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The genuine last selected starting beta coordinate bounding the middle content band. -/
noncomputable def originalSelectedMiddleLowerBeta {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] : ℤ :=
  originalSelectedSourceBeta P ⟨originalSelectedCount (hD := hD) P-1, by
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega⟩

/-- The genuine first selected last-column beta coordinate bounding the middle content band. -/
noncomputable def originalSelectedMiddleUpperBeta {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] : ℤ :=
  P.zeta (interiorBlockLast P (originalSelectedEnumeration (hD := hD) P
    ⟨0, NeZero.pos _⟩).val.val).castSucc

/-- Complete actual parent-row strips cover every cell in the selected middle content band. -/
theorem originalInternalParentStrip_cover_content {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hb : 2 ≤ originalSelectedCount (hD := hD) P) (x : ℤ × ℤ) (hx : x ∈ P.cells)
    (hlo : originalSelectedMiddleLowerBeta (hD := hD) P ≤ content x)
    (hhi : content x < originalSelectedMiddleUpperBeta (hD := hD) P) :
    ∃ i : Fin (originalSelectedCount (hD := hD) P - 1), x ∈ originalInternalParentStrip P i := by
  let first := originalSelectedEnumeration (hD := hD) P ⟨0, by omega⟩
  let last := originalSelectedEnumeration (hD := hD) P
    ⟨originalSelectedCount (hD := hD) P-1, by omega⟩
  obtain ⟨r, hr, hcolumns⟩ := P.mem_cells.mp hx
  have hcontent : P.zeta r ≤ content x ∧ content x < P.xi r := by
    dsimp only [content]
    omega
  have hrowlo : originalSelectedSourceRow P ⟨0, by omega⟩ < x.1 := by
    by_contra hn
    have hfirst := interiorBlockFirst_le_last P first.val.val
    rw [first.val.property] at hfirst
    have hle : r ≤ (interiorBlockLast P first.val.val).castSucc := by
      change r.val ≤ (interiorBlockLast P first.val.val).val
      change ¬ ((first.val.val.val : ℤ) < x.1) at hn
      omega
    have hz := P.zeta_strictAnti.antitone hle
    change P.zeta (interiorBlockLast P first.val.val).castSucc ≤ P.zeta r at hz
    change content x < P.zeta (interiorBlockLast P first.val.val).castSucc at hhi
    omega
  have hrowhi : x.1 ≤ ((interiorBlockLast P last.val.val).val : ℤ) := by
    by_contra hn
    have hlast := interiorBlockFirst_le_last P last.val.val
    rw [last.val.property] at hlast
    have hle : last.val.val.succ ≤ r := by
      change last.val.val.val+1 ≤ r.val
      omega
    have hz := P.xi_strictAnti.antitone hle
    change P.xi r ≤ P.xi last.val.val.succ at hz
    change P.xi last.val.val.succ ≤ content x at hlo
    omega
  exact originalInternalParentStrip_cover_middle P hb x hx hrowlo hrowhi

end SkewCornerDescent.Matrix.SelectedCoordinate
