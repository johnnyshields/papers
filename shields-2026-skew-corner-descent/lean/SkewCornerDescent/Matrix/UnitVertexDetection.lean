/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.UnitVertexLowerResponses
import SkewCornerDescent.Matrix.MidpointCorrection

/-!
# The original response decides a separating midpoint unit vertex

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Original
beta geometry supplies acyclicity and both strict lower effective corrections.
Their shared midpoint generator survives the selected relation, so adjoining its
literal h-zero vertex necessarily changes the full original residue response.
All inverse entries and endpoint couplings remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing
open scoped BigOperators

/-- The scalar entry of the full original boundary contraction is its complete
double inverse sum, with no entry discarded. -/
theorem vertex_boundary_contraction_eq {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (x y : ℤ)
    [Invertible (vertexBetaMatrix ι row col)] :
    (vertexOutgoing ι col x * ⅟(vertexBetaMatrix ι row col) * vertexIncoming ι row y) () () =
      inverseContraction (fun i => ι (hh (x - col i)))
        (fun i => ι (hh (row i - y))) (vertexBetaMatrix ι row col) := by
  unfold inverseContraction
  simp only [Matrix.mul_apply, vertexOutgoing, vertexIncoming, Matrix.of_apply,
    Matrix.invOf_eq_nonsing_inv, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem unit_matrix_product_apply {R : Type*} [CommRing R]
    (A B : Matrix Unit Unit R) : (A * B) () () = A () () * B () () := by
  simp only [Matrix.mul_apply, Fintype.sum_unique]

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual full residue response distinguishes presence of a separating
midpoint h-zero vertex when its midpoint lies above the selected span. The old
full inverse is retained; acyclicity, the augmented inverse, and both strict lower
corrections are produced from the original beta geometry. -/
theorem original_midpoint_vertex_changes_response {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m x y : ℤ) (J : ℕ+) (hJ : c.top < J)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (hx : ∀ i, row i < x) (hy : ∀ i, y < col i)
    (hxm : x - m = (J : ℤ)) (hmy : m - y = (J : ℤ)) :
    let P := vertexBetaMatrix c.residueMap row col
    let u := vertexIncoming c.residueMap row m
    let v := vertexOutgoing c.residueMap col m
    let r := vertexOutgoing c.residueMap col x
    let s := vertexIncoming c.residueMap row y
    let a : Matrix Unit Unit (OtherField c.top) := Matrix.of fun _ _ => c.residueMap (hh (x - m))
    let b : Matrix Unit Unit (OtherField c.top) := Matrix.of fun _ _ => c.residueMap (hh (m - y))
    let top : Matrix Unit Unit (OtherField c.top) := Matrix.of fun _ _ => c.residueMap (hh (x - y))
    letI := unitVertexInverse P u v
      (geometric_unit_vertex_feedback_zero c.residueMap row col m hsep)
    (top - Matrix.fromCols r a * ⅟(Matrix.fromBlocks P u v 1) * Matrix.fromRows s b) () () ≠
      (top - r * ⅟P * s) () () := by
  let P := vertexBetaMatrix c.residueMap row col
  let u := vertexIncoming c.residueMap row m
  let v := vertexOutgoing c.residueMap col m
  let r := vertexOutgoing c.residueMap col x
  let s := vertexIncoming c.residueMap row y
  let a : Matrix Unit Unit (OtherField c.top) := Matrix.of fun _ _ => c.residueMap (hh (x - m))
  let b : Matrix Unit Unit (OtherField c.top) := Matrix.of fun _ _ => c.residueMap (hh (m - y))
  let top : Matrix Unit Unit (OtherField c.top) := Matrix.of fun _ _ => c.residueMap (hh (x - y))
  let := unitVertexInverse P u v (geometric_unit_vertex_feedback_zero c.residueMap row col m hsep)
  have hmodel := geometric_unit_vertex_response_correction c.residueMap row col m x y hsep
  change top - Matrix.fromCols r a * ⅟(Matrix.fromBlocks P u v 1) * Matrix.fromRows s b =
    (top - r * ⅟P * s) - (a - r * ⅟P * u) * (b - v * ⅟P * s) at hmodel
  have hscalar := congrArg (fun A : Matrix Unit Unit (OtherField c.top) => A () ()) hmodel
  simp only [Matrix.sub_apply, unit_matrix_product_apply] at hscalar
  have ha : a () () = c.residueMap (hh (x - m)) := rfl
  have hb : b () () = c.residueMap (hh (m - y)) := rfl
  have hl := vertex_boundary_contraction_eq c.residueMap row col x m
  have hr := vertex_boundary_contraction_eq c.residueMap row col m y
  change (r * ⅟P * u) () () = _ at hl
  change (v * ⅟P * s) () () = _ at hr
  rw [ha, hb, hl, hr, hxm, hmy, hh_pnat, c.residueMap_other J (ne_of_gt hJ)] at hscalar
  have hgen : algebraMap (OtherPolynomial c.top) (OtherField c.top)
      (MvPolynomial.X ⟨J, ne_of_gt hJ⟩) = residueGenerator c.top ⟨J, ne_of_gt hJ⟩ := rfl
  rw [hgen] at hscalar
  let A := inverseContraction (fun i => c.residueMap (hh (x - col i)))
    (fun i => c.residueMap (hh (row i - m))) P
  let B := inverseContraction (fun i => c.residueMap (hh (m - col i)))
    (fun i => c.residueMap (hh (row i - y))) P
  have hA : A ∈ residueLowerField c.top J :=
    c.geometric_vertex_left_correction_lower row col m x J hJ hsep hx hxm
  have hB : B ∈ residueLowerField c.top J :=
    c.geometric_vertex_right_correction_lower row col m y J hJ hsep hy hmy
  have hnonzero : -((residueGenerator c.top ⟨J, ne_of_gt hJ⟩ - A) *
      (residueGenerator c.top ⟨J, ne_of_gt hJ⟩ - B)) ≠ 0 := by
    simpa only [sub_eq_add_neg] using midpoint_correction_ne_zero c.top J hJ (-A) (-B)
      ((residueLowerField c.top J).neg_mem hA) ((residueLowerField c.top J).neg_mem hB)
  change (top - Matrix.fromCols r a * ⅟(Matrix.fromBlocks P u v 1) * Matrix.fromRows s b) () () ≠
    (top - r * ⅟P * s) () ()
  intro heq
  simp only [Matrix.sub_apply] at heq
  rw [heq] at hscalar
  apply hnonzero
  linear_combination -hscalar

end SelectedCoordinate
end SkewCornerDescent.Matrix
