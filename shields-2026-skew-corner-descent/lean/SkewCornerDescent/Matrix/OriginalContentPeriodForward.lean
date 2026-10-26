/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalSelectedContentCover

/-!
# Actual forward period on the complete middle content band

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete literal parent-strip copies and the full selected endpoint period
translate every genuine middle-band cell forward. The actual last selected
endpoint excludes a fictitious wrapped interval at the bottom boundary.
All original parent cells and both row bounds remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Genuine literal strip periods transport every actual cell in the
complete eligible middle content band. -/
theorem originalMiddleBand_forward_period {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hb : 2 ≤ originalSelectedCount (hD := hD) P) (r : ℕ) [NeZero r]
    (hr : r < originalSelectedCount (hD := hD) P) (δ : ℤ) (hδ : 0 < δ)
    (v : ℤ × ℤ) (hv : content v = -δ)
    (hstrips : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1), j.val = i.val+r →
      translate v (originalInternalParentStrip P i) = originalInternalParentStrip P j)
    (hselected : ∀ a b : Fin (originalSelectedCount (hD := hD) P), b.val = a.val+r →
      originalSelectedSourceBeta P b - originalSelectedSourceBeta P a = content v)
    (x : ℤ × ℤ) (hx : x ∈ P.cells)
    (hlo : originalSelectedMiddleLowerBeta (hD := hD) P + δ ≤ content x)
    (hhi : content x < originalSelectedMiddleUpperBeta (hD := hD) P) : x+v ∈ P.cells := by
  have hmidlo : originalSelectedMiddleLowerBeta (hD := hD) P ≤ content x := by omega
  obtain ⟨i, hix⟩ := originalInternalParentStrip_cover_content P hb x hx hmidlo hhi
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P-1, by omega⟩
  let m : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P-1-r, by omega⟩
  have hmlast : last.val = m.val+r := by dsimp only [m,last]; omega
  have hbeta := hselected m last hmlast
  rw [hv] at hbeta
  have hlast : originalSelectedSourceBeta P m =
      originalSelectedMiddleLowerBeta (hD := hD) P + δ := by
    change originalSelectedSourceBeta P m = originalSelectedSourceBeta P last + δ
    omega
  have htop : content x < originalSelectedSourceBeta P a := by
    have hlow := (Finset.mem_filter.mp hix).2.1
    change (((originalSelectedEnumeration (hD := hD) P a).val.val.val : ℤ) + 1) ≤ x.1 at hlow
    obtain ⟨row, hrow, hcols⟩ := P.mem_cells.mp hx
    have hle : (originalSelectedEnumeration (hD := hD) P a).val.val.succ ≤ row := by
      change (originalSelectedEnumeration (hD := hD) P a).val.val.val+1 ≤ row.val
      omega
    have he := P.xi_strictAnti.antitone hle
    change P.xi row ≤ originalSelectedSourceBeta P a at he
    have hraw : content x < P.xi row := by dsimp only [content]; omega
    exact hraw.trans_le he
  have heligible : i.val+r < originalSelectedCount (hD := hD) P - 1 := by
    by_contra hn
    have hma : m ≤ a := by change m.val ≤ a.val; dsimp only [m,a]; omega
    have hanti := (originalSelectedSourceBeta_strictAnti P).antitone hma
    rw [hlast] at hanti
    omega
  let j : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨i.val+r, heligible⟩
  have htrans : x+v ∈ translate v (originalInternalParentStrip P i) :=
    mem_translate.mpr (by simpa only [add_sub_cancel_right] using hix)
  rw [hstrips i j rfl] at htrans
  exact (Finset.mem_filter.mp htrans).1

end SkewCornerDescent.Matrix.SelectedCoordinate
