/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowProfile
import SkewCornerDescent.Matrix.OriginalWindowSelectedRanks

/-!
# Actual source ranks in a complete lower-content window profile

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). A literal
lower-content end window is the entire final selected source segment. Its independent
profile enumeration therefore removes exactly the omitted prefix of whole occurrences. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every selected rank of the actual lower-content window has the exact source prefix offset. -/
theorem originalWindow_lower_restriction_selected_rank {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (i : Fin (originalSelectedCount (hD := hD) Q)) :
    ∃ j : Fin (originalSelectedCount (hD := hD) P),
      j.val = i.val + (originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) Q) ∧
      (∀ x ∈ interiorBlockCells P (originalSelectedEnumeration (hD := hD) P j).val.val,
        0 ≤ content x ∧ content x < P.xi 0 - q) ∧
      translate v (interiorBlockCells P
        (originalSelectedEnumeration (hD := hD) P j).val.val) =
        interiorBlockCells Q (originalSelectedEnumeration (hD := hD) Q i).val.val := by
  classical
  obtain ⟨e, he⟩ := originalLiteralWindow_profile_selected_orderIso (hD := hD)
    P Q 0 (P.xi 0 - q) v hwindow hq hL
  let EP := originalSelectedEnumeration (hD := hD) P
  let EQ := originalSelectedEnumeration (hD := hD) Q
  let b := e.symm (EQ i)
  let j := EP.symm b.val
  let p : Fin (originalSelectedCount (hD := hD) P) → Prop := fun k =>
    ∀ x ∈ interiorBlockCells P (EP k).val.val, 0 ≤ content x ∧ content x < P.xi 0 - q
  have hjband : p j := by
    change ∀ x ∈ interiorBlockCells P (EP (EP.symm b.val)).val.val, _
    rw [EP.apply_symm_apply]
    exact b.property
  have hup : ∀ i j, i ≤ j → p i → p j := by
    intro i j hij hi
    exact originalWindow_prefix_upper P q (EP i) (EP j) (EP.monotone hij) hi
  let R := (originalWindowEnumeration (hD := hD) P 0 (P.xi 0 - q)).trans
    (e.trans EQ.symm)
  have hr := fin_final_window_orderIso_rank p hup R ⟨j, hjband⟩
  have hR : R ⟨j, hjband⟩ = i := by
    change EQ.symm (e ⟨EP j, hjband⟩) = i
    have hB : (⟨EP j, hjband⟩ : OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = b :=
      Subtype.ext (EP.apply_symm_apply b.val)
    rw [hB]
    change EQ.symm (e (e.symm (EQ i))) = i
    rw [e.apply_symm_apply, EQ.symm_apply_apply]
  rw [hR] at hr
  refine ⟨j, hr.symm, hjband, ?_⟩
  have hc := he b
  change interiorBlockCells Q (e (e.symm (EQ i))).val.val =
    translate v (interiorBlockCells P b.val.val.val) at hc
  rw [e.apply_symm_apply] at hc
  change translate v (interiorBlockCells P (EP (EP.symm b.val)).val.val) = _
  rw [EP.apply_symm_apply]
  exact hc.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
