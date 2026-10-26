/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowEndLogLocality
import SkewCornerDescent.Matrix.OriginalVerticalSelectedCopies
import SkewCornerDescent.Matrix.OriginalVerticalInterior

/-!
# Complete actual vertical-closure endpoint logarithms

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual vertical source copies are complete full windows at the private join.
Every component bound, full cap neighborhood and normal inverse jet is transported
from the unchanged source, including the additional empty central pivot. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual vertical-closure component inherits the source span bound. -/
theorem originalVerticalClosure_profile_component_span {n m : ℕ}
    (P : Profile n) (V : Profile m) (v : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∀ C ∈ edgeComponents (diagramInterior V.cells), span C ≤ (c.top : ℕ) := by
  intro C hC
  have ht : translate v C ∈ edgeComponents (diagramInterior (originalVerticalClosure P)) := by
    rw [hV, interior_translate, edgeComponents_translate]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  rw [originalVerticalClosure_components] at ht
  rcases Finset.mem_union.mp ht with ht | ht
  · have h := hmax (translate v C) ht
    rwa [span_translate] at h
  · obtain ⟨T, hT, he⟩ := Finset.mem_image.mp ht
    have h := hmax T hT
    have hs := congrArg span he
    simp only [span_translate] at hs
    rwa [hs] at h

/-- The actual central vertical join excludes every interior cell in the normalized profile.
Its private diagonal and normalization content are produced from literal closure geometry. -/
theorem originalVerticalClosure_profile_join_no_interior {n m : ℕ}
    (P : Profile n) (V : Profile m) (v : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells) :
    ∀ x ∈ diagramInterior V.cells, content x ≠ P.xi 0 := by
  intro x hx he
  have ht : x + v ∈ diagramInterior (originalVerticalClosure P) := by
    rw [hV, interior_translate]
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right] using hx
  have hn := private_diagonal_no_interior (originalVerticalClosure_join_private P).1 (x + v) ht
  have hv := originalVerticalClosure_profile_content P V v hV
  apply hn
  simp only [content, Prod.fst_add, Prod.snd_add] at *
  omega

/-- The complete actual vertical closure has the source's full left-cap logarithmic jets
below the source selected count, without a supplied inverse or cap-jet correspondence. -/
theorem originalVerticalClosure_left_log_coeff {n m : ℕ}
    (P : Profile n) (V : Profile m) (v : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P) :
    PowerSeries.coeff k (leftCap (c.originalNormalExtension V)
      (originalSelectedCount (hD := hD) V)) =
    PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
      (originalSelectedCount (hD := hD) P)) := by
  let w := vH P.cells - eCell - v
  have htop := originalVerticalClosure_profile_top P V v hV
  have hw : P.cells = translate (-w)
      (V.cells.filter fun x => P.xi 0 ≤ content x ∧ content x < V.xi 0) := by
    rw [htop, originalVerticalClosure_upper_window P V v hV]
    change P.cells = translate (-w) (translate w P.cells)
    rw [translate_translate, neg_add_cancel, translate_zero]
  have hjoin := originalVerticalClosure_profile_join_no_interior P V v hV
  have hend : ∀ x ∈ diagramInterior V.cells, content x ≠ V.xi 0 := by
    intro x hx
    have h := interior_content_strict V.isConnectedSkew_cells hx
    rw [V.maxContent_cells] at h
    omega
  exact (c.originalWindow_left_log_coeff V P (P.xi 0) (-w) hw hjoin hend
    (c.originalVerticalClosure_profile_component_span P V v hV hmax) hmax k hk).symm

/-- The full original right-cap logarithmic jets also survive actual vertical closure.
The entire lower source copy, not a horizontal surrogate, supplies the suffix window. -/
theorem originalVerticalClosure_right_log_coeff {n m : ℕ}
    (P : Profile n) (V : Profile m) (v : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P) :
    PowerSeries.coeff k (rightCap (c.originalNormalExtension V) 0
      (originalSelectedCount (hD := hD) V)) =
    PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
      (originalSelectedCount (hD := hD) P)) := by
  have htop := originalVerticalClosure_profile_top P V v hV
  have hw : P.cells = translate v
      (V.cells.filter fun x => 0 ≤ content x ∧ content x < V.xi 0 - P.xi 0) := by
    rw [htop, show 2 * P.xi 0 - P.xi 0 = P.xi 0 by omega,
      originalVerticalClosure_lower_window P V v hV,
      translate_translate, add_neg_cancel, translate_zero]
  have hjoin : ∀ x ∈ diagramInterior V.cells, content x ≠ V.xi 0 - P.xi 0 := by
    rw [htop, show 2 * P.xi 0 - P.xi 0 = P.xi 0 by omega]
    exact originalVerticalClosure_profile_join_no_interior P V v hV
  have hstart : ∀ x ∈ diagramInterior V.cells, content x ≠ 0 := by
    intro x hx
    have h := interior_content_strict V.isConnectedSkew_cells hx
    rw [V.minContent_cells] at h
    omega
  exact (c.originalWindow_right_log_coeff V P (P.xi 0) v hw hstart hjoin
    (c.originalVerticalClosure_profile_component_span P V v hV hmax) hmax k hk).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
