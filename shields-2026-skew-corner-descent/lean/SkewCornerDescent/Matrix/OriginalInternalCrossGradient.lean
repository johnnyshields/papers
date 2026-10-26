/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedProfileLocality
import SkewCornerDescent.Matrix.OriginalInternalSelfJet

/-!
# Complete cross-profile gradient at the actual internal matrix interface

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Original selected endpoints and the full long interval inverse supply the
cross coefficient of two complete actual endpoint profiles. This applies
to the genuine crossing matrix entry, not a cyclic column-zero surrogate.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual internal endpoint distance in its source selected beta coordinates. -/
theorem originalInternal_endpoint_distance {n : ℕ} (P : Profile n)
    (u v : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P u) (originalInternalStateIndex P v) =
    P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P ⟨u.val, by have := u.isLt; omega⟩)))) -
    P.zeta (originalColSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P ⟨v.val + 1, by have := v.isLt; omega⟩)))) := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨u.val, by have := u.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨v.val+1, by have := v.isLt; omega⟩
  change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
    P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))) = _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]

/-- Adjacent actual intervals share exactly one selected component span. -/
theorem originalInternal_adjacent_distance {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) (hji : j.val = i.val + 1) :
    originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P j) =
    originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) +
    originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P j) (originalInternalStateIndex P j) - (c.top : ℤ) := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  have hab : a = b := Fin.ext hji
  have ht := c.originalSelected_endpoint_distance P (originalSelectedEnumeration P a)
  have he : P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P a)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P b)))) = (c.top : ℤ) := by
    rw [← hab, originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
    exact ht
  simp only [originalInternal_endpoint_distance]
  dsimp only [a, b] at he
  omega

/-- Differentiate an actual ordered internal pair entry using its complete
left and right local profiles. Both local height bounds are explicit. -/
theorem originalInternal_cross_residue_gradient {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) (hij : i ≤ j)
    (H : ℕ+) (hH : c.top < H) (k : ℕ)
    (hdegree : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P j) - (H : ℤ) = (k : ℤ))
    (hki : (k : ℤ) ≤ originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i))
    (hkj : (k : ℤ) ≤ originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P j) (originalInternalStateIndex P j)) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.regularResidue (c.originalInternalResponseMatrix P i j)) =
      ((c.originalInternalEndpointProfiles P i).1 *
        (c.originalInternalEndpointProfiles P j).2).coeff k := by
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  rw [originalInternal_endpoint_distance] at hdegree hki hkj
  have hab : ai ≤ bi := by change i.val ≤ i.val+1; omega
  have hbt : bi ≤ bj := by change i.val+1 ≤ j.val+1; exact Nat.add_le_add_right hij 1
  have hae : ai ≤ aj := hij
  have het : aj ≤ bj := by change j.val ≤ j.val+1; omega
  rw [c.originalInternalResponseMatrix_selected_entry P i j]
  exact c.original_long_response_local_gradient P (E ai) (E bi) (E aj) (E bj)
    ⟨E.monotone hab, E.monotone hbt⟩ ⟨E.monotone hae, E.monotone het⟩
    H hH k hdegree hki hkj

end SkewCornerDescent.Matrix.SelectedCoordinate
