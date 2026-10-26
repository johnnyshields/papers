/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralParentStrips
import SkewCornerDescent.Matrix.OriginalSelectedCells

/-!
# Complete parent-cell coverage between the extreme selected components

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every genuine parent cell between the first retained selected row and the
last selected component belongs to an actual consecutive parent-row strip.
The canonical maximal preceding selected occurrence supplies the interval;
no cell, unit vertex, or endpoint strip is omitted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Actual consecutive parent-row strips cover every cell of the selected middle. -/
theorem originalInternalParentStrip_cover_middle {n : ℕ} (P : Profile n)
    (hb : 2 ≤ originalSelectedCount (hD := hD) P) (x : ℤ × ℤ) (hx : x ∈ P.cells)
    (hlo : originalSelectedSourceRow P ⟨0, by omega⟩ < x.1)
    (hhi : x.1 ≤ ((interiorBlockLast P (originalSelectedEnumeration (hD := hD) P
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩).val.val).val : ℤ)) :
    ∃ i : Fin (originalSelectedCount (hD := hD) P - 1), x ∈ originalInternalParentStrip P i := by
  classical
  let S := Finset.univ.filter fun k : Fin (originalSelectedCount (hD := hD) P) =>
    originalSelectedSourceRow P k < x.1
  have hS : S.Nonempty := ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo⟩⟩
  let k := S.max' hS
  have hkS : k ∈ S := Finset.max'_mem _ _
  have hbelow := (Finset.mem_filter.mp hkS).2
  by_cases hn : k.val+1 < originalSelectedCount (hD := hD) P
  · let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨k.val, by omega⟩
    let next : Fin (originalSelectedCount (hD := hD) P) := ⟨k.val+1, hn⟩
    have hnext : x.1 ≤ originalSelectedSourceRow P next := by
      by_contra hnot
      have hm : next ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hnot⟩
      have hle := Finset.le_max' S next hm
      change next.val ≤ k.val at hle
      dsimp only [next] at hle
      omega
    have he : originalSelectedSourceRow P next ≤ (originalInternalRowLast P i : ℤ) := by
      change (originalInternalRowEnd P i : ℤ) ≤ (originalInternalRowLast P i : ℤ)
      exact_mod_cast (originalInternal_row_frame_bounds P i).2.1
    refine ⟨i, Finset.mem_filter.mpr ⟨hx, ?_, hnext.trans he⟩⟩
    change (originalInternalRowStart P i : ℤ) < x.1 at hbelow
    omega
  · have hk : k.val = originalSelectedCount (hD := hD) P-1 := by have := k.isLt; omega
    let i : Fin (originalSelectedCount (hD := hD) P - 1) :=
      ⟨originalSelectedCount (hD := hD) P-2, by omega⟩
    let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
    have hak : a < k := by change i.val < k.val; dsimp only [i]; omega
    have hleft := (originalSelectedSourceRow_strictMono P hak).trans hbelow
    have he : (⟨i.val+1, by have := i.isLt; omega⟩ :
        Fin (originalSelectedCount (hD := hD) P)) =
        ⟨originalSelectedCount (hD := hD) P-1, by omega⟩ := Fin.ext (by dsimp only [i]; omega)
    have hlast : originalInternalRowLast P i =
        (interiorBlockLast P (originalSelectedEnumeration (hD := hD) P
          ⟨originalSelectedCount (hD := hD) P-1, by omega⟩).val.val).val := by
      unfold originalInternalRowLast
      rw [he]
    refine ⟨i, Finset.mem_filter.mpr ⟨hx, ?_, ?_⟩⟩
    · change (originalInternalRowStart P i : ℤ) < x.1 at hleft
      omega
    · rw [hlast]
      exact hhi

end SkewCornerDescent.Matrix.SelectedCoordinate
