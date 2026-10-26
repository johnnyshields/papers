/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.UnitVertexDetection
import SkewCornerDescent.Matrix.ResidueProtectedTop

/-!
# Complete endpoint coefficients of literal h-zero vertices

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Each
unit vertex has a monic protected incoming or outgoing coefficient whenever
that endpoint distance exceeds the selected span. Its full inverse is produced
from original acyclicity, including all earlier and later couplings. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The complete incoming coefficient of the adjoined unit vertex is its full
effective incoming coordinate; no off-diagonal inverse is omitted. -/
theorem unit_vertex_incoming_coefficient {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (P : Matrix ν ν F) [Invertible P] (u : Matrix ν Unit F) (v : Matrix Unit ν F)
    (hfeedback : v * ⅟P * u = 0) (row : Matrix Unit ν F) (a : Matrix Unit Unit F) :
    letI := unitVertexInverse P u v hfeedback
    (Matrix.fromCols row a * ⅟(Matrix.fromBlocks P u v 1)) () (.inr ()) =
      (a - row * ⅟P * u) () () := by
  let : Invertible ((1 : Matrix Unit Unit F) - v * ⅟P * u) :=
    ⟨1, by rw [hfeedback, sub_zero, Matrix.one_mul],
      by rw [hfeedback, sub_zero, Matrix.mul_one]⟩
  let := unitVertexInverse P u v hfeedback
  have hSchur : ⅟((1 : Matrix Unit Unit F) - v * ⅟P * u) = 1 := rfl
  rw [Matrix.invOf_fromBlocks₁₁_eq, hSchur, Matrix.fromCols_mul_fromBlocks]
  simp only [Matrix.mul_one, Matrix.fromCols, Matrix.of_apply, Sum.elim_inr,
    Matrix.mul_neg, Matrix.mul_assoc, Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply]
  ring

/-- The complete outgoing coefficient is the symmetric effective coordinate. -/
theorem unit_vertex_outgoing_coefficient {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (P : Matrix ν ν F) [Invertible P] (u : Matrix ν Unit F) (v : Matrix Unit ν F)
    (hfeedback : v * ⅟P * u = 0) (col : Matrix ν Unit F) (b : Matrix Unit Unit F) :
    letI := unitVertexInverse P u v hfeedback
    (⅟(Matrix.fromBlocks P u v 1) * Matrix.fromRows col b) (.inr ()) () =
      (b - v * ⅟P * col) () () := by
  let : Invertible ((1 : Matrix Unit Unit F) - v * ⅟P * u) :=
    ⟨1, by rw [hfeedback, sub_zero, Matrix.one_mul],
      by rw [hfeedback, sub_zero, Matrix.mul_one]⟩
  let := unitVertexInverse P u v hfeedback
  have hSchur : ⅟((1 : Matrix Unit Unit F) - v * ⅟P * u) = 1 := rfl
  rw [Matrix.invOf_fromBlocks₁₁_eq, hSchur, Matrix.fromBlocks_mul_fromRows]
  change (-((1 : Matrix Unit Unit F) * v * ⅟P) * col +
    (1 : Matrix Unit Unit F) * b) () () = _
  simp only [Matrix.one_mul, Matrix.neg_mul, Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply]
  ring

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The inverse of the literal augmented beta matrix is constructed from the
full old inverse and the geometric no-feedback producer. -/
@[instance_reducible]
noncomputable def geometricUnitVertexBetaInverse {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i)) :
    Invertible (vertexBetaMatrix c.residueMap (Sum.elim row (fun _ : Unit => m))
      (Sum.elim col (fun _ : Unit => m))) := by
  rw [vertexBetaMatrix_insert]
  exact unitVertexInverse _ _ _ (geometric_unit_vertex_feedback_zero c.residueMap row col m hsep)

/-- The actual incoming coefficient at a literal unit vertex retains its
original monic high generator and cannot vanish in the strict lower field. -/
theorem original_unit_vertex_incoming_protected {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m x : ℤ) (J : ℕ+) (hJ : c.top < J)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (hx : ∀ i, row i < x) (hxm : x - m = (J : ℤ)) :
    letI := c.geometricUnitVertexBetaInverse row col m hsep
    let rows := Sum.elim row (fun _ : Unit => m)
    let cols := Sum.elim col (fun _ : Unit => m)
    ∃ R ∈ residueLowerField c.top J,
      (vertexOutgoing c.residueMap cols x * ⅟(vertexBetaMatrix c.residueMap rows cols))
          () (.inr ()) = residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  let P := vertexBetaMatrix c.residueMap row col
  let u := vertexIncoming c.residueMap row m
  let v := vertexOutgoing c.residueMap col m
  have hfeedback := geometric_unit_vertex_feedback_zero c.residueMap row col m hsep
  let := unitVertexInverse P u v hfeedback
  let := c.geometricUnitVertexBetaInverse row col m hsep
  let A := inverseContraction (fun i => c.residueMap (hh (x - col i)))
    (fun i => c.residueMap (hh (row i - m))) P
  have hA : A ∈ residueLowerField c.top J :=
    c.geometric_vertex_left_correction_lower row col m x J hJ hsep hx hxm
  have hinv :
      ⅟(vertexBetaMatrix c.residueMap (Sum.elim row (fun _ : Unit => m))
        (Sum.elim col (fun _ : Unit => m))) = ⅟(Matrix.fromBlocks P u v 1) := by
    rw [Matrix.invOf_eq_nonsing_inv, vertexBetaMatrix_insert, Matrix.invOf_eq_nonsing_inv]
  have hvec : vertexOutgoing c.residueMap (Sum.elim col (fun _ : Unit => m)) x =
      Matrix.fromCols (vertexOutgoing c.residueMap col x)
        (Matrix.of fun (_ _ : Unit) => c.residueMap (hh (x - m))) := by
    ext i j
    cases j <;> rfl
  refine ⟨-A, (residueLowerField c.top J).neg_mem hA, ?_⟩
  rw [hinv, hvec, unit_vertex_incoming_coefficient P u v hfeedback]
  change c.residueMap (hh (x - m)) -
    (vertexOutgoing c.residueMap col x * ⅟P * vertexIncoming c.residueMap row m) () () = _
  rw [vertex_boundary_contraction_eq, hxm, hh_pnat, c.residueMap_other J (ne_of_gt hJ)]
  exact sub_eq_add_neg _ _

/-- The full actual outgoing coefficient has the same monic protected
generator, with the entire original later inverse correction retained. -/
theorem original_unit_vertex_outgoing_protected {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m y : ℤ) (J : ℕ+) (hJ : c.top < J)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (hy : ∀ i, y < col i) (hmy : m - y = (J : ℤ)) :
    letI := c.geometricUnitVertexBetaInverse row col m hsep
    let rows := Sum.elim row (fun _ : Unit => m)
    let cols := Sum.elim col (fun _ : Unit => m)
    ∃ R ∈ residueLowerField c.top J,
      (⅟(vertexBetaMatrix c.residueMap rows cols) * vertexIncoming c.residueMap rows y)
          (.inr ()) () = residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  let P := vertexBetaMatrix c.residueMap row col
  let u := vertexIncoming c.residueMap row m
  let v := vertexOutgoing c.residueMap col m
  have hfeedback := geometric_unit_vertex_feedback_zero c.residueMap row col m hsep
  let := unitVertexInverse P u v hfeedback
  let := c.geometricUnitVertexBetaInverse row col m hsep
  let A := inverseContraction (fun i => c.residueMap (hh (m - col i)))
    (fun i => c.residueMap (hh (row i - y))) P
  have hA : A ∈ residueLowerField c.top J :=
    c.geometric_vertex_right_correction_lower row col m y J hJ hsep hy hmy
  have hinv :
      ⅟(vertexBetaMatrix c.residueMap (Sum.elim row (fun _ : Unit => m))
        (Sum.elim col (fun _ : Unit => m))) = ⅟(Matrix.fromBlocks P u v 1) := by
    rw [Matrix.invOf_eq_nonsing_inv, vertexBetaMatrix_insert, Matrix.invOf_eq_nonsing_inv]
  have hvec : vertexIncoming c.residueMap (Sum.elim row (fun _ : Unit => m)) y =
      Matrix.fromRows (vertexIncoming c.residueMap row y)
        (Matrix.of fun (_ _ : Unit) => c.residueMap (hh (m - y))) := by
    ext i j
    cases i <;> rfl
  refine ⟨-A, (residueLowerField c.top J).neg_mem hA, ?_⟩
  rw [hinv, hvec, unit_vertex_outgoing_coefficient P u v hfeedback]
  change c.residueMap (hh (m - y)) -
    (vertexOutgoing c.residueMap col m * ⅟P * vertexIncoming c.residueMap row y) () () = _
  rw [vertex_boundary_contraction_eq, hmy, hh_pnat, c.residueMap_other J (ne_of_gt hJ)]
  exact sub_eq_add_neg _ _

end SelectedCoordinate
end SkewCornerDescent.Matrix
