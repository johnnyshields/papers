/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPhaseHessianProjection
import SkewCornerDescent.Matrix.OriginalClosureResponse
import SkewCornerDescent.Matrix.OriginalClosureResponses
import SkewCornerDescent.Matrix.OriginalClosureEnumeration

/-!
# The actual horizontal reference Hessian has source phase weights

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual closure copying supplies the selected proper cores, endpoint distance,
interval order, and the maximal-component span bound. No equality of reference
weights or Hessians is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The join response's full Hessian uses the actual source proper cores.
Its complete reference interval and all retained within-block entries remain. -/
theorem originalHorizontalClosure_phase_hessian {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (i j : Fin (originalSelectedCount (hD := hD) P))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hsum : (p : ℤ) + (q : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration (hD := hD) P i)))) + P.xi 0 -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration (hD := hD) P j))))) :
    let b := originalHorizontalClosureSelectedCopy P Q v hQ true
      (originalSelectedEnumeration (hD := hD) P i)
    let d := originalHorizontalClosureSelectedCopy P Q v hQ false
      (originalSelectedEnumeration (hD := hD) P j)
    let x := P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration (hD := hD) P i)))) + P.xi 0
    let A := (c.originalSelectedCoreLeft P i).toLaurent
    let T := (c.originalSelectedCoreRight P j).toLaurent
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalLocalResponse Q (some b) (some d)))) =
      -c.originalIntervalInverseProjection Q (some b) (some d) A T (x - (q : ℤ)) -
        c.originalIntervalInverseProjection Q (some b) (some d) A T (x - (p : ℤ)) := by
  let bi := originalSelectedEnumeration (hD := hD) P i
  let dj := originalSelectedEnumeration (hD := hD) P j
  let b := originalHorizontalClosureSelectedCopy P Q v hQ true bi
  let d := originalHorizontalClosureSelectedCopy P Q v hQ false dj
  have horder : interiorBlock Q b.val.val ≤ interiorBlock Q d.val.val := by
    dsimp only [b, d]
    rw [originalHorizontalClosure_selected_label, originalHorizontalClosure_selected_label]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hb : interiorBlock P bi.val.val ≤ (interiorCuts P).card := Finset.card_filter_le _ _
    omega
  have hx := (originalHorizontalClosure_retained_endpoints P Q v hQ true bi).1
  have hy := (originalHorizontalClosure_retained_endpoints P Q v hQ false dj).2
  simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte,
    sub_zero, add_sub_cancel_right] at hx hy
  have hsumQ : (p : ℤ) + (q : ℤ) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some b))) -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some d))) := by
    rw [hx, hy]
    exact hsum
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    intro C hC
    have hCt : translate v C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)) := by
      rw [hQ, interior_translate, edgeComponents_translate]
      exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
    have ht := c.originalHorizontalClosure_component_span P hmax _ hCt
    rwa [span_translate] at ht
  have h := c.originalLocalResponse_proper_core_hessian Q b d horder
    hmaxQ p q hp hq hsumQ
  have hleft := (c.originalSelectedCore_closure_copy P Q v hQ true i).1
  have hright := (c.originalSelectedCore_closure_copy P Q v hQ false j).2
  dsimp only at hleft hright h
  rw [← hleft, ← hright, hx] at h
  exact h

/-- The actual middle Hessenberg state is the same complete local join
response used by the private-cap Hessian comparison. -/
theorem originalHorizontalClosure_middle_local_response {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
        omega⟩
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    c.originalHessenbergResponse Q middle middle =
      c.originalLocalResponse Q
        (some (originalHorizontalClosureSelectedCopy P Q v hQ true
          (originalSelectedEnumeration (hD := hD) P last)))
        (some (originalHorizontalClosureSelectedCopy P Q v hQ false
          (originalSelectedEnumeration (hD := hD) P first))) := by
  intro middle first last
  let B := originalSelectedCount (hD := hD) P
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  let a : Fin (originalSelectedCount (hD := hD) Q) := ⟨B - 1, by dsimp only [B]; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) Q) := ⟨B, by dsimp only [B]; omega⟩
  have ha : middle = a.succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp only [middle, a, B]
    omega
  have hb : middle = b.castSucc := rfl
  have hea := originalHorizontalClosureEnumeration_eq_original P Q v hQ
    (⟨B - 1, by dsimp only [B]; omega⟩ : Fin (2 * B))
  have heb := originalHorizontalClosureEnumeration_eq_original P Q v hQ
    (⟨B, by dsimp only [B]; omega⟩ : Fin (2 * B))
  have hBa : B - 1 < B := by dsimp only [B]; omega
  dsimp only [B] at hea heb hBa
  simp only [originalHorizontalClosureEnumeration, hBa, ↓reduceDIte] at hea
  simp only [originalHorizontalClosureEnumeration, lt_self_iff_false, ↓reduceDIte,
    Nat.sub_self] at heb
  unfold originalHessenbergResponse
  change c.originalLocalResponse Q (originalHessenbergRows (hD := hD) Q middle)
    (originalHessenbergCols (hD := hD) Q middle) = _
  rw [ha, originalHessenbergRows_succ, ← ha, hb, originalHessenbergCols_castSucc]
  rw [← hea, ← heb]

end SkewCornerDescent.Matrix.SelectedCoordinate
