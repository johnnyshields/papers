/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFilteredCapProjection
import SkewCornerDescent.Matrix.OriginalPrivateWindowMembership
import SkewCornerDescent.Matrix.OriginalClosureHalfWindows

/-!
# Complete source-cap beta lists in a literal whole window

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
A full source cap transports to its clipped target window with every original
remaining index and both complete endpoint lists. No inverse or scalar-response
match is supplied. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Equal window bounds transport the complete cap type while preserving
both underlying beta lists. This also handles arithmetic-equal dependent bounds. -/
theorem originalWindow_cap_bound_vectors {n : ℕ} (P : Profile n)
    (lo hi lo' hi' : ℤ) (hlo : lo = lo') (hhi : hi = hi')
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P) :
    ∃ e : {i : OriginalWholeWindowRemaining (hD := hD) P lo hi //
        originalCapBlockSide upper b i.1.val} ≃
      {i : OriginalWholeWindowRemaining (hD := hD) P lo' hi' //
        originalCapBlockSide upper b i.1.val},
      ∀ i, originalResponseRows P ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows P ⟨i.val.1.val, i.val.2⟩ ∧
        originalResponseCols P ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols P ⟨i.val.1.val, i.val.2⟩ := by
  cases hlo
  cases hhi
  exact ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩

/-- Complete source-cap indices, including proper strips and every full unit
component, agree with the actual clipped target cap by one common content shift. -/
theorem originalCompleteWindow_cap_vectors {n m : ℕ} (P : Profile n) (Q : Profile m)
    (shift : ℤ) (v : ℤ × ℤ) (hv : content v = shift)
    (hwindow : Q.cells.filter (fun x => shift ≤ content x ∧ content x < P.xi 0 + shift) =
      translate v P.cells)
    (hlo : ∀ x ∈ diagramInterior Q.cells, content x ≠ shift)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ P.xi 0 + shift)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P)
    (d : OriginalSelectedBlocks (hD := hD) Q)
    (hd : originalBlockInWindow Q shift (P.xi 0 + shift) d.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q d.val.val) :
    ∃ e : OriginalResponseInterval (hD := hD) P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) ≃
      {i : OriginalWholeWindowRemaining (hD := hD) Q shift (P.xi 0 + shift) //
        originalCapBlockSide upper d i.1.val},
      ∀ i, originalResponseRows Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows P i.1.1 + shift ∧
        originalResponseCols Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols P i.1.1 + shift := by
  have hP : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0) = P.cells := by
    ext x
    rw [Finset.mem_filter]
    exact ⟨And.left, fun hx => ⟨hx, P.content_bounds_cells hx⟩⟩
  have hbound0 := profile_normalized_lower_private_boundaries P
  have hbound1 := profile_normalized_upper_private_boundaries P
  obtain ⟨e, hend⟩ := originalLiteralWindow_filtered_cap_equiv P Q 0 (P.xi 0) shift v hv
    (by simpa only [zero_add, hP] using hwindow)
    (private_diagonal_no_interior hbound0.1)
    (by simpa only [zero_add] using hlo)
    (private_diagonal_no_interior hbound1.1) hhi upper b d
    (originalBlockInWindow_full P b.val) (by simpa only [zero_add] using hd) he
  let f := originalWindowCapIntervalEquiv P 0 (P.xi 0) upper b
    (fun a _ => originalBlockInWindow_full P a)
  obtain ⟨t, ht⟩ := originalWindow_cap_bound_vectors Q (0 + shift) (P.xi 0 + shift)
    shift (P.xi 0 + shift) (zero_add shift) rfl upper d
  refine ⟨(f.trans e).trans t, ?_⟩
  intro i
  have hsource := hend (f i)
  have htarget := ht (e (f i))
  exact ⟨htarget.1.trans hsource.1, htarget.2.trans hsource.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
