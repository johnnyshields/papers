/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.UnitVertexGeometry
import SkewCornerDescent.Matrix.OrderedLocality
import SkewCornerDescent.Matrix.OriginalResidueResponses

/-!
# Strictly lower effective corrections at an original midpoint vertex

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Ordered
prefix and suffix locality restrict the full inverse contractions to the appropriate
side of the actual vertex. Every retained entry then has index below the protected
midpoint generator. Full unit inverses and all within-side couplings remain.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem vertex_early_col {ν : Type*} (row col : ν → ℤ) (m : ℤ)
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (i : {i : ν // vertexBlockOrder row m i < 0}) : m < col i.val := by
  have hRi : m < row i.val := by
    by_contra hnot
    have hi := i.property
    simp only [vertexBlockOrder, ite_eq_right hnot] at hi
    omega
  exact ((hsep i.val).resolve_left (fun h => lt_asymm hRi h.1)).2

private theorem vertex_late_row {ν : Type*} (row col : ν → ℤ) (m : ℤ)
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (i : {i : ν // 0 < vertexBlockOrder row m i}) : row i.val < m := by
  have hRi : ¬ m < row i.val := by
    intro hpos
    have hi := i.property
    simp only [vertexBlockOrder, ite_eq_left hpos] at hi
    omega
  exact ((hsep i.val).resolve_right (fun h => hRi h.1)).1

/-- The actual effective incoming vertex correction is strictly below its
original endpoint-to-vertex generator. No inverse entry is independently assigned. -/
theorem geometric_vertex_left_correction_lower {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m x : ℤ) (J : ℕ+) (hJ : c.top < J)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (hx : ∀ i, row i < x) (hxm : x - m = (J : ℤ)) :
    inverseContraction (fun i => c.residueMap (hh (x - col i)))
      (fun i => c.residueMap (hh (row i - m))) (vertexBetaMatrix c.residueMap row col) ∈
        residueLowerField c.top J := by
  let order := vertexBlockOrder row m
  have htri := vertexBetaMatrix_blockTriangular c.residueMap row col m hsep
  have hcut : ∀ i, ¬ order i < 0 → c.residueMap (hh (row i - m)) = 0 := by
    intro i hi
    have hRi : ¬ m < row i := by
      intro hpos
      simp only [order, vertexBlockOrder, ite_eq_left hpos] at hi
      omega
    have hneg := ((hsep i).resolve_right (fun h => hRi h.1)).1
    rw [hh_of_neg (by omega), map_zero]
  rw [inverseContraction_prefix _ _ _ order htri 0 hcut]
  let := htri.invertibleToBlock (0 : ℤ)
  apply inverseContraction_mem_subfield
  · intro i
    apply c.residue_hh_mem_lower J hJ
    have hm := vertex_early_col row col m hsep i
    omega
  · intro i
    apply c.residue_hh_mem_lower J hJ
    have hi := hx i.val
    omega
  · intro i j
    apply c.residue_hh_mem_lower J hJ
    have hi := hx i.val
    have hm := vertex_early_col row col m hsep j
    omega

/-- The actual effective outgoing correction is also strictly lower, using the
entire ordered suffix inverse rather than a diagonal-only approximation. -/
theorem geometric_vertex_right_correction_lower {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m y : ℤ) (J : ℕ+) (hJ : c.top < J)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (hy : ∀ i, y < col i) (hmy : m - y = (J : ℤ)) :
    inverseContraction (fun i => c.residueMap (hh (m - col i)))
      (fun i => c.residueMap (hh (row i - y))) (vertexBetaMatrix c.residueMap row col) ∈
        residueLowerField c.top J := by
  let order := vertexBlockOrder row m
  have htri := vertexBetaMatrix_blockTriangular c.residueMap row col m hsep
  have hcut : ∀ i, ¬ 0 < order i → c.residueMap (hh (m - col i)) = 0 := by
    intro i hi
    have hRi : m < row i := by
      by_contra hnot
      simp only [order, vertexBlockOrder, ite_eq_right hnot] at hi
      omega
    have hm := ((hsep i).resolve_left (fun h => lt_asymm hRi h.1)).2
    rw [hh_of_neg (by omega), map_zero]
  rw [inverseContraction_suffix _ _ _ order htri 0 hcut]
  let inv := htri.transpose.invertibleToBlock (OrderDual.toDual (0 : ℤ))
  change Invertible (Matrix.transpose ((vertexBetaMatrix c.residueMap row col).toBlock
    (fun i => 0 < order i) (fun i => 0 < order i))) at inv
  let := inv
  let := Matrix.invertibleOfInvertibleTranspose ((vertexBetaMatrix c.residueMap row col).toBlock
    (fun i => 0 < order i) (fun i => 0 < order i))
  apply inverseContraction_mem_subfield
  · intro i
    apply c.residue_hh_mem_lower J hJ
    have hi := hy i.val
    omega
  · intro i
    apply c.residue_hh_mem_lower J hJ
    have hm := vertex_late_row row col m hsep i
    omega
  · intro i j
    apply c.residue_hh_mem_lower J hJ
    have hm := vertex_late_row row col m hsep i
    have hj := hy j.val
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
