/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCapContents

/-!
# Actual first and last cap tops under whole-diagram transpose

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Complete selected-component lookup in both directions exchanges the first and
last actual occurrences. Their intrinsic content extrema swap the true cap
tops, including the one-selected-component boundary. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The complete normalized transpose reverses both extrema of any matched
actual selected component. -/
theorem selected_transpose_content_extrema {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (e : OriginalSelectedBlocks (hD := isConnectedSkew_transpose hD) T)
    (he : transpose (interiorBlockCells P b.val.val) =
      translate a (interiorBlockCells T e.val.val)) :
    minContent (interiorBlockCells T e.val.val) =
        P.xi 0 - 1 - maxContent (interiorBlockCells P b.val.val) ∧
      maxContent (interiorBlockCells T e.val.val) =
        P.xi 0 - 1 - minContent (interiorBlockCells P b.val.val) := by
  have hp := interiorBlockCells_connected P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)
  have ht := interiorBlockCells_connected T e.val.val
    (originalBlockSelected_nonempty T e.val e.property)
  have hc := (transpose_profile_endpoints P T a ha).2
  have hm := congrArg minContent he
  have hM := congrArg maxContent he
  rw [minContent_transpose _ hp.2.1, minContent_translate ht.2.1] at hm
  rw [maxContent_transpose _ hp.2.1, maxContent_translate ht.2.1] at hM
  constructor <;> omega

/-- The complete normalized transpose swaps the two actual exterior cap tops. -/
theorem original_cap_tops_transpose {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hT : 0 < originalSelectedCount (hD := isConnectedSkew_transpose hD) T) :
    originalHessenbergDistance (hD := isConnectedSkew_transpose hD) T 0 0 =
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) ∧
      originalHessenbergDistance (hD := isConnectedSkew_transpose hD) T (Fin.last _) (Fin.last _) =
        originalHessenbergDistance (hD := hD) P 0 0 := by
  let pF := originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩
  let pL := originalSelectedEnumeration (hD := hD) P
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  let tF := originalSelectedEnumeration (hD := isConnectedSkew_transpose hD) T ⟨0, hT⟩
  let tL := originalSelectedEnumeration (hD := isConnectedSkew_transpose hD) T
    ⟨originalSelectedCount (hD := isConnectedSkew_transpose hD) T - 1, by omega⟩
  obtain ⟨e, he⟩ := selected_block_transpose_exists (hD := hD) P T a ha pF
  obtain ⟨f, hf⟩ := selected_block_transpose_exists (hD := hD) P T a ha pL
  have heC := selected_transpose_content_extrema P T a ha pF e he
  have hfC := selected_transpose_content_extrema P T a ha pL f hf
  have heLast : e = tL := by
    obtain ⟨b, hb⟩ := selected_block_transpose_exists_reverse (hD := hD) P T a ha tL
    have hbC := selected_transpose_content_extrema P T a ha b tL hb
    have hp := (originalSelected_maxContent_strictAnti (hD := hD) P).antitone
      (selected_first_le P hB b)
    have ht := (originalSelected_minContent_strictAnti
      (hD := isConnectedSkew_transpose hD) T).antitone (selected_le_last T hT e)
    change maxContent (interiorBlockCells P b.val.val) ≤
      maxContent (interiorBlockCells P pF.val.val) at hp
    change minContent (interiorBlockCells T tL.val.val) ≤
      minContent (interiorBlockCells T e.val.val) at ht
    have hc : minContent (interiorBlockCells T e.val.val) =
        minContent (interiorBlockCells T tL.val.val) := by omega
    exact (originalSelected_minContent_strictAnti
      (hD := isConnectedSkew_transpose hD) T).injective hc
  have hfFirst : f = tF := by
    obtain ⟨b, hb⟩ := selected_block_transpose_exists_reverse (hD := hD) P T a ha tF
    have hbC := selected_transpose_content_extrema P T a ha b tF hb
    have hp := (originalSelected_minContent_strictAnti (hD := hD) P).antitone
      (selected_le_last P hB b)
    have ht := (originalSelected_maxContent_strictAnti
      (hD := isConnectedSkew_transpose hD) T).antitone (selected_first_le T hT f)
    change minContent (interiorBlockCells P pL.val.val) ≤
      minContent (interiorBlockCells P b.val.val) at hp
    change maxContent (interiorBlockCells T f.val.val) ≤
      maxContent (interiorBlockCells T tF.val.val) at ht
    have hc : maxContent (interiorBlockCells T f.val.val) =
        maxContent (interiorBlockCells T tF.val.val) := by omega
    exact (originalSelected_maxContent_strictAnti
      (hD := isConnectedSkew_transpose hD) T).injective hc
  rw [heLast] at heC
  rw [hfFirst] at hfC
  have hxi := (transpose_profile_endpoints P T a ha).1
  rw [originalHessenbergDistance_first T hT, originalHessenbergDistance_last P hB,
    originalHessenbergDistance_last T hT, originalHessenbergDistance_first P hB,
    originalFirstCapDistance_contents, originalLastCapDistance_contents,
    originalLastCapDistance_contents, originalFirstCapDistance_contents]
  change (T.xi 0 - minContent (interiorBlockCells T tF.val.val) =
      maxContent (interiorBlockCells P pL.val.val) + 1) ∧
    (maxContent (interiorBlockCells T tL.val.val) + 1 =
      P.xi 0 - minContent (interiorBlockCells P pF.val.val))
  constructor <;> omega

/-- Equality of the two true exterior cap tops is invariant under the whole
normalized transpose. The target inventory's nonemptiness is produced from a
complete selected-component witness rather than assumed. -/
theorem original_cap_coincidence_transpose {n m : ℕ} (P : Profile n) (T : Profile m)
    (a : ℤ × ℤ) (ha : transpose P.cells = translate a T.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    (originalHessenbergDistance (hD := isConnectedSkew_transpose hD) T 0 0 =
        originalHessenbergDistance (hD := isConnectedSkew_transpose hD) T
          (Fin.last _) (Fin.last _)) ↔
      (originalHessenbergDistance (hD := hD) P 0 0 =
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)) := by
  obtain ⟨e, _⟩ := selected_block_transpose_exists (hD := hD) P T a ha
    (originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩)
  have ht := originalSelectedCount_pos T e
  obtain ⟨hp, hq⟩ := original_cap_tops_transpose P T a ha hB ht
  rw [hp, hq]
  exact eq_comm

end SkewCornerDescent.Matrix.SelectedCoordinate
