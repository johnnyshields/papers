/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueProfileDifference

/-!
# Reindexing complete actual residue endpoint polynomials

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). A produced finite beta-index equivalence preserves each
full inverse coefficient and its original endpoint distance. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The reindexed inverse is exposed at the exact beta-matrix type used by
the profile API, rather than relying on an implicit submatrix unfolding. -/
@[instance_reducible]
noncomputable def residueBetaReindexInverse {ν κ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]
    (row col : ν → ℤ) (e : κ ≃ ν)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    Invertible (vertexBetaMatrix c.residueMap (row ∘ e) (col ∘ e)) := by
  have hM : vertexBetaMatrix c.residueMap (row ∘ e) (col ∘ e) =
      (vertexBetaMatrix c.residueMap row col).submatrix e e := rfl
  rw [hM]
  exact Matrix.submatrixEquivInvertible _ e e

/-- Reindexing the whole original beta matrix preserves its incoming polynomial. -/
theorem residueIntervalLeftPolynomial_equiv {ν κ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]
    (row col : ν → ℤ) (x : ℤ) (e : κ ≃ ν)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    letI := c.residueBetaReindexInverse row col e
    c.residueIntervalLeftPolynomial (row ∘ e) (col ∘ e) x =
      c.residueIntervalLeftPolynomial row col x := by
  let := c.residueBetaReindexInverse row col e
  have hweights (i : κ) :
      (vertexOutgoing c.residueMap (col ∘ e) x *
        ⅟(vertexBetaMatrix c.residueMap (row ∘ e) (col ∘ e))) () i =
      (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col)) () (e i) := by
    simp only [Matrix.mul_apply, vertexOutgoing, Matrix.of_apply, Matrix.invOf_eq_nonsing_inv]
    change (∑ j, c.residueMap (hh (x - col (e j))) *
      ((vertexBetaMatrix c.residueMap row col).submatrix e e)⁻¹ j i) = _
    rw [Matrix.inv_submatrix_equiv]
    apply Fintype.sum_equiv e
    intro j
    rfl
  simp only [residueIntervalLeftPolynomial, ordinaryEndpointProfile]
  apply congrArg (fun p : Polynomial (OtherField c.top) => 1 - p)
  apply Fintype.sum_equiv e
  intro i
  rw [hweights]
  rfl

/-- The symmetric complete outgoing polynomial is preserved by the same
original beta-index equivalence. -/
theorem residueIntervalRightPolynomial_equiv {ν κ : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]
    (row col : ν → ℤ) (y : ℤ) (e : κ ≃ ν)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    letI := c.residueBetaReindexInverse row col e
    c.residueIntervalRightPolynomial (row ∘ e) (col ∘ e) y =
      c.residueIntervalRightPolynomial row col y := by
  let := c.residueBetaReindexInverse row col e
  have hweights (i : κ) :
      (⅟(vertexBetaMatrix c.residueMap (row ∘ e) (col ∘ e)) *
        vertexIncoming c.residueMap (row ∘ e) y) i () =
      (⅟(vertexBetaMatrix c.residueMap row col) * vertexIncoming c.residueMap row y) (e i) () := by
    simp only [Matrix.mul_apply, vertexIncoming, Matrix.of_apply, Matrix.invOf_eq_nonsing_inv]
    change (∑ j, ((vertexBetaMatrix c.residueMap row col).submatrix e e)⁻¹ i j *
      c.residueMap (hh (row (e j) - y))) = _
    rw [Matrix.inv_submatrix_equiv]
    apply Fintype.sum_equiv e
    intro j
    rfl
  simp only [residueIntervalRightPolynomial, ordinaryEndpointProfile]
  apply congrArg (fun p : Polynomial (OtherField c.top) => 1 - p)
  apply Fintype.sum_equiv e
  intro i
  rw [hweights]
  rfl

/-- A common beta translation leaves every original matrix entry unchanged. -/
theorem residueBetaMatrix_translate {ν : Type*} (row col : ν → ℤ) (τ : ℤ) :
    vertexBetaMatrix c.residueMap (fun i => row i + τ) (fun i => col i + τ) =
      vertexBetaMatrix c.residueMap row col := by
  ext i j
  change c.residueMap (hh (row i + τ - (col j + τ))) = c.residueMap (hh (row i - col j))
  congr 2
  ring

/-- The inverse of the translated original beta matrix is supplied by the
unchanged original matrix, not assumed independently. -/
@[instance_reducible]
noncomputable def residueBetaTranslateInverse {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (τ : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)] :
    Invertible (vertexBetaMatrix c.residueMap (fun i => row i + τ) (fun i => col i + τ)) := by
  rw [c.residueBetaMatrix_translate row col τ]
  infer_instance

/-- Incoming endpoint polynomials retain their exact original distances after
a common translation of the entire beta frame and its boundary endpoint. -/
theorem residueIntervalLeftPolynomial_translate {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x τ : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)] :
    letI := c.residueBetaTranslateInverse row col τ
    c.residueIntervalLeftPolynomial (fun i => row i + τ) (fun i => col i + τ) (x + τ) =
      c.residueIntervalLeftPolynomial row col x := by
  let := c.residueBetaTranslateInverse row col τ
  have hr : vertexOutgoing c.residueMap (fun i => col i + τ) (x + τ) =
      vertexOutgoing c.residueMap col x := by
    ext i j
    change c.residueMap (hh (x + τ - (col j + τ))) = c.residueMap (hh (x - col j))
    congr 2
    ring
  have hd (i) : x + τ - (row i + τ) = x - row i := by ring
  simp only [residueIntervalLeftPolynomial, ordinaryEndpointProfile,
    Matrix.invOf_eq_nonsing_inv, c.residueBetaMatrix_translate row col τ, hr, hd]

/-- The corresponding exact translation invariance for the outgoing profile. -/
theorem residueIntervalRightPolynomial_translate {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (y τ : ℤ) [Invertible (vertexBetaMatrix c.residueMap row col)] :
    letI := c.residueBetaTranslateInverse row col τ
    c.residueIntervalRightPolynomial (fun i => row i + τ) (fun i => col i + τ) (y + τ) =
      c.residueIntervalRightPolynomial row col y := by
  let := c.residueBetaTranslateInverse row col τ
  have hc : vertexIncoming c.residueMap (fun i => row i + τ) (y + τ) =
      vertexIncoming c.residueMap row y := by
    ext i j
    change c.residueMap (hh (row i + τ - (y + τ))) = c.residueMap (hh (row i - y))
    congr 2
    ring
  have hd (i) : col i + τ - (y + τ) = col i - y := by ring
  simp only [residueIntervalRightPolynomial, ordinaryEndpointProfile,
    Matrix.invOf_eq_nonsing_inv, c.residueBetaMatrix_translate row col τ, hc, hd]

end SkewCornerDescent.Matrix.SelectedCoordinate
