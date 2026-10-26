/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalSelectedContentCover

/-!
# Actual inverse period on the complete middle content band

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete literal parent-strip copies and the full selected endpoint period
translate every genuine middle-band cell backward. The common actual
selected-core span excludes an unbuilt interval at the top boundary.
All original parent cells and both row bounds remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Genuine literal strip periods transport every actual cell in the
complete eligible middle content band. -/
theorem originalMiddleBand_backward_period {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hb : 2 ≤ originalSelectedCount (hD := hD) P) (r : ℕ) [NeZero r]
    (hr : r < originalSelectedCount (hD := hD) P) (δ : ℤ) (hδ : 0 < δ)
    (v : ℤ × ℤ) (hv : content v = -δ)
    (hstrips : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1), j.val = i.val+r →
      translate v (originalInternalParentStrip P i) = originalInternalParentStrip P j)
    (hselected : ∀ a b : Fin (originalSelectedCount (hD := hD) P), b.val = a.val+r →
      originalSelectedSourceBeta P b - originalSelectedSourceBeta P a = content v)
    (x : ℤ × ℤ) (hx : x ∈ P.cells)
    (hlo : originalSelectedMiddleLowerBeta (hD := hD) P ≤ content x)
    (hhi : content x < originalSelectedMiddleUpperBeta (hD := hD) P - δ) : x-v ∈ P.cells := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  have hmidhi : content x < originalSelectedMiddleUpperBeta (hD := hD) P := by omega
  obtain ⟨j, hjx⟩ := originalInternalParentStrip_cover_content P hb x hx hlo hmidhi
  have heligible : r ≤ j.val := by
    by_contra hn
    let l : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, by omega⟩
    let pr : Fin (originalSelectedCount (hD := hD) P) := ⟨r, hr⟩
    let E := originalSelectedEnumeration (hD := hD) P
    have hlr : l ≤ pr := by change l.val ≤ pr.val; dsimp only [l,pr]; omega
    have hanti := (originalSelectedSourceBeta_strictAnti P).antitone hlr
    have hbeta := hselected first pr (by dsimp only [first,pr]; omega)
    rw [hv] at hbeta
    have hf := coord.originalSelected_endpoint_distance P (E first)
    have hl := coord.originalSelected_endpoint_distance P (E l)
    change originalSelectedSourceBeta P first -
      P.zeta (interiorBlockLast P (E first).val.val).castSucc = (coord.top : ℤ) at hf
    change originalSelectedSourceBeta P l -
      P.zeta (interiorBlockLast P (E l).val.val).castSucc = (coord.top : ℤ) at hl
    have hupper : originalSelectedMiddleUpperBeta (hD := hD) P - δ ≤
        P.zeta (interiorBlockLast P (E l).val.val).castSucc := by
      change P.zeta (interiorBlockLast P (E first).val.val).castSucc - δ ≤ _
      omega
    have hbound := (Finset.mem_filter.mp hjx).2.2
    change x.1 ≤ ((interiorBlockLast P (E l).val.val).val : ℤ) at hbound
    obtain ⟨row, hrow, hcols⟩ := P.mem_cells.mp hx
    have hle : row ≤ (interiorBlockLast P (E l).val.val).castSucc := by
      change row.val ≤ (interiorBlockLast P (E l).val.val).val
      omega
    have hz := P.zeta_strictAnti.antitone hle
    have hraw : P.zeta row ≤ content x := by dsimp only [content]; omega
    have hh := hupper.trans (hz.trans hraw)
    omega
  let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨j.val-r, by have := j.isLt; omega⟩
  have hij : j.val = i.val+r := by dsimp only [i]; omega
  have htrans : x ∈ translate v (originalInternalParentStrip P i) := by
    rw [hstrips i j hij]
    exact hjx
  have hsource := mem_translate.mp htrans
  exact (Finset.mem_filter.mp hsource).1

end SkewCornerDescent.Matrix.SelectedCoordinate
