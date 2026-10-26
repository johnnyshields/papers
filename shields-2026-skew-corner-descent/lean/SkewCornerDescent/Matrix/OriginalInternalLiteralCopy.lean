/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIncomingLiteral
import SkewCornerDescent.Matrix.OriginalInternalSelfJet
import SkewCornerDescent.Matrix.OriginalInternalHeights

/-!
# Complete original literal copies between internal states

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
The actual interval type and its endpoint beta translation describe literal
paired row and column equality.  Equal full incoming profiles at equal actual
heights and residues produce that whole equivalence by early recovery, without
an outgoing-profile or matrix-copy hypothesis.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete actual retained interval at an internal state. -/
abbrev OriginalInternalInterval {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :=
  OriginalResponseInterval (hD := hD) P
    (some (originalSelectedEnumeration P ⟨i.val, by have := i.isLt; omega⟩))
    (some (originalSelectedEnumeration P ⟨i.val+1, by have := i.isLt; omega⟩))

/-- The common original beta translation from one internal state to another. -/
noncomputable def originalInternalIntervalShift {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) : ℤ :=
  P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P ⟨j.val, by have := j.isLt; omega⟩)))) -
    P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P ⟨i.val, by have := i.isLt; omega⟩))))

/-- Literal equality of both complete original interval beta lists under the
actual common translation; every retained position is paired. -/
def originalInternalLiteralCopy {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) : Prop :=
  ∃ e : OriginalInternalInterval P i ≃ OriginalInternalInterval P j,
    ∀ p, originalResponseRows P (e p).1.1 =
        originalResponseRows P p.1.1 + originalInternalIntervalShift P i j ∧
      originalResponseCols P (e p).1.1 =
        originalResponseCols P p.1.1 + originalInternalIntervalShift P i j

/-- Equal full incoming profiles at actual equal-height, equal-response
internal states produce a complete paired original interval copy.  No outgoing
profile equality or interval-copy compatibility is assumed. -/
theorem originalInternal_literal_copy_of_incoming_eq {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hresponse : c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hincoming : (c.originalInternalEndpointProfiles P i).1 =
      (c.originalInternalEndpointProfiles P j).1) :
    originalInternalLiteralCopy P i j := by
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let H := originalHessenbergDistance (hD := hD) P
    (originalInternalStateIndex P i) (originalInternalStateIndex P i)
  have hHN : 2 * (c.top : ℤ) < H := c.originalInternal_height_gt_twice_top P i
  have hHpos : 0 < H := by have := c.top.pos; omega
  let K : ℕ+ := ⟨H.toNat, by omega⟩
  have hK : (K : ℤ) = H := Int.toNat_of_nonneg hHpos.le
  have hKN : 2 * (c.top : ℕ) < (K : ℕ) := by
    have hh : 2 * (c.top : ℤ) < (K : ℤ) := by rw [hK]; exact hHN
    exact_mod_cast hh
  have hi : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E ai)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E bi)))) = (K : ℤ) := by
    rw [hK]
    change _ = P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (originalHessenbergRows P ai.succ))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (originalHessenbergCols P bi.castSucc)))
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hj : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E aj)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E bj)))) = (K : ℤ) := by
    rw [hK]
    change _ = originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i)
    rw [hheight]
    change _ = P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (originalHessenbergRows P aj.succ))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (originalHessenbergCols P bj.castSucc)))
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hr : c.regularResidue (c.originalLocalResponse P (some (E ai)) (some (E bi))) =
      c.regularResidue (c.originalLocalResponse P (some (E aj)) (some (E bj))) := by
    rw [← c.originalInternalResponseMatrix_selected_entry P i i,
      ← c.originalInternalResponseMatrix_selected_entry P j j]
    exact hresponse
  exact (c.original_interval_literal_iff_incoming_eq P P ai bi (by rfl) aj bj (by rfl)
    K hKN hi hj hmax hmax hr).mpr hincoming

end SkewCornerDescent.Matrix.SelectedCoordinate
