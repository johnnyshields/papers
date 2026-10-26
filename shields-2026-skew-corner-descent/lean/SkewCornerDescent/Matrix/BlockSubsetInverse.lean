/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Invertibility after retaining complete triangular blocks

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Deleting whole blocks preserves each retained diagonal determinant. This proves
invertibility, not equality with the corresponding full inverse submatrix for a
noncontiguous selection. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν α F : Type*} [Fintype ν] [DecidableEq ν]
  [Finite α] [LinearOrder α] [Field F]

/-- Every complete-block principal selection of an invertible triangular matrix
has nonzero determinant, including an empty selection. -/
theorem blockTriangular_kept_det_ne_zero (M : Matrix ν ν F) [Invertible M]
    (label : ν → α) (hM : M.BlockTriangular label)
    (keep : α → Prop) [DecidablePred keep] :
    (M.toBlock (fun i => keep (label i)) (fun i => keep (label i))).det ≠ 0 := by
  classical
  let := Fintype.ofFinite α
  have hdet : M.det ≠ 0 := (Matrix.isUnit_det_of_invertible M).ne_zero
  rw [hM.det_fintype] at hdet
  have hdiag (a : α) : (M.toSquareBlock label a).det ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hdet) a (Finset.mem_univ a)
  let N := M.toBlock (fun i => keep (label i)) (fun i => keep (label i))
  let label' := fun i : {i : ν // keep (label i)} => label i.val
  have hN : N.BlockTriangular label' := hM.submatrix
  change N.det ≠ 0
  rw [hN.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  by_cases ha : keep a
  · have hkeep (i : ν) (hi : label i = a) : keep (label i) := by
      rw [hi]
      exact ha
    let e : {i : {i : ν // keep (label i)} // label' i = a} ≃ {i : ν // label i = a} :=
      Equiv.subtypeSubtypeEquivSubtype (p := fun i => keep (label i))
        (q := fun i => label i = a) (fun {i} hi => hkeep i hi)
    have hm : N.toSquareBlock label' a = (M.toSquareBlock label a).submatrix e e := by
      apply Matrix.ext
      intro i j
      rfl
    rw [hm, Matrix.det_submatrix_equiv_self]
    exact hdiag a
  · have : IsEmpty {i : {i : ν // keep (label i)} // label' i = a} := ⟨by
      intro i
      apply ha
      rw [← i.property]
      exact i.val.property⟩
    rw [Matrix.toSquareBlock_def, Matrix.det_isEmpty]
    exact one_ne_zero

/-- The retained complete matrix receives its own genuine inverse. Off-diagonal
entries are not copied from the full inverse when blocks were removed in between. -/
@[instance_reducible]
noncomputable def blockTriangularKeptInverse (M : Matrix ν ν F) [Invertible M]
    (label : ν → α) (hM : M.BlockTriangular label)
    (keep : α → Prop) [DecidablePred keep] :
    Invertible (M.toBlock (fun i => keep (label i)) (fun i => keep (label i))) :=
  Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr
    (blockTriangular_kept_det_ne_zero M label hM keep))

end SkewCornerDescent.Matrix
