/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.UnitVertexGeometry
import SkewCornerDescent.Matrix.EndpointProfiles

/-!
# Complete beta endpoint polynomials over a coefficient ring

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The coefficient ring may be the full normal power-series ring. Literal reindexing
and translation preserve all inverse entries and endpoint exponents. Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix

open SkewGluing

variable {R ν : Type*} [CommRing R] [Fintype ν] [DecidableEq ν]

/-- Incoming endpoint polynomial using the complete beta-matrix inverse. -/
def betaEndpointLeftPolynomial (φ : Lambda →+* R) (row col : ν → ℤ) (x : ℤ) : Polynomial R :=
  ordinaryEndpointProfile (fun i => (x - row i).toNat)
    (fun i => (vertexOutgoing φ col x * (vertexBetaMatrix φ row col)⁻¹) () i)

/-- Outgoing endpoint polynomial using the same complete beta-matrix inverse. -/
def betaEndpointRightPolynomial (φ : Lambda →+* R) (row col : ν → ℤ) (y : ℤ) : Polynomial R :=
  ordinaryEndpointProfile (fun i => (col i - y).toNat)
    (fun i => ((vertexBetaMatrix φ row col)⁻¹ * vertexIncoming φ row y) i ())

/-- Complete incoming endpoint polynomials survive an actual finite index equivalence. -/
theorem betaEndpointLeftPolynomial_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (φ : Lambda →+* R) (row col : ν → ℤ) (x : ℤ) (e : κ ≃ ν) :
    betaEndpointLeftPolynomial φ (row ∘ e) (col ∘ e) x =
      betaEndpointLeftPolynomial φ row col x := by
  have hw (i : κ) :
      (vertexOutgoing φ (col ∘ e) x * (vertexBetaMatrix φ (row ∘ e) (col ∘ e))⁻¹) () i =
      (vertexOutgoing φ col x * (vertexBetaMatrix φ row col)⁻¹) () (e i) := by
    change (∑ j, φ (hh (x - col (e j))) *
      ((vertexBetaMatrix φ row col).submatrix e e)⁻¹ j i) =
        ∑ j, φ (hh (x - col j)) * (vertexBetaMatrix φ row col)⁻¹ j (e i)
    rw [Matrix.inv_submatrix_equiv]
    apply Fintype.sum_equiv e
    intro j
    rfl
  unfold betaEndpointLeftPolynomial ordinaryEndpointProfile
  apply congrArg (fun p : Polynomial R => 1 - p)
  apply Fintype.sum_equiv e
  intro i
  exact congrArg (Polynomial.monomial (x - row (e i)).toNat) (hw i)

/-- Complete outgoing endpoint polynomials survive the same actual index equivalence. -/
theorem betaEndpointRightPolynomial_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (φ : Lambda →+* R) (row col : ν → ℤ) (y : ℤ) (e : κ ≃ ν) :
    betaEndpointRightPolynomial φ (row ∘ e) (col ∘ e) y =
      betaEndpointRightPolynomial φ row col y := by
  have hw (i : κ) :
      ((vertexBetaMatrix φ (row ∘ e) (col ∘ e))⁻¹ * vertexIncoming φ (row ∘ e) y) i () =
      ((vertexBetaMatrix φ row col)⁻¹ * vertexIncoming φ row y) (e i) () := by
    change (∑ j, ((vertexBetaMatrix φ row col).submatrix e e)⁻¹ i j *
      φ (hh (row (e j) - y))) =
        ∑ j, (vertexBetaMatrix φ row col)⁻¹ (e i) j * φ (hh (row j - y))
    rw [Matrix.inv_submatrix_equiv]
    apply Fintype.sum_equiv e
    intro j
    rfl
  unfold betaEndpointRightPolynomial ordinaryEndpointProfile
  apply congrArg (fun p : Polynomial R => 1 - p)
  apply Fintype.sum_equiv e
  intro i
  exact congrArg (Polynomial.monomial (col (e i) - y).toNat) (hw i)

omit [Fintype ν] [DecidableEq ν] in
/-- A common content translation preserves every full beta-matrix entry. -/
theorem beta_matrix_translate (φ : Lambda →+* R) (row col : ν → ℤ) (τ : ℤ) :
    vertexBetaMatrix φ (fun i => row i + τ) (fun i => col i + τ) =
      vertexBetaMatrix φ row col := by
  ext i j : 1
  change φ (hh (row i + τ - (col j + τ))) = φ (hh (row i - col j))
  congr 2
  ring

/-- Translating the whole incoming beta frame and its endpoint preserves its polynomial. -/
theorem betaEndpointLeftPolynomial_translate (φ : Lambda →+* R) (row col : ν → ℤ)
    (x τ : ℤ) :
    betaEndpointLeftPolynomial φ (fun i => row i + τ) (fun i => col i + τ) (x + τ) =
      betaEndpointLeftPolynomial φ row col x := by
  have hv : vertexOutgoing φ (fun i => col i + τ) (x + τ) = vertexOutgoing φ col x := by
    ext u i : 1
    change φ (hh (x + τ - (col i + τ))) = φ (hh (x - col i))
    congr 2
    ring
  have hd i : x + τ - (row i + τ) = x - row i := by ring
  simp only [betaEndpointLeftPolynomial, ordinaryEndpointProfile,
    beta_matrix_translate, hv, hd]

/-- Translating the whole outgoing beta frame and its endpoint preserves its polynomial. -/
theorem betaEndpointRightPolynomial_translate (φ : Lambda →+* R) (row col : ν → ℤ)
    (y τ : ℤ) :
    betaEndpointRightPolynomial φ (fun i => row i + τ) (fun i => col i + τ) (y + τ) =
      betaEndpointRightPolynomial φ row col y := by
  have hv : vertexIncoming φ (fun i => row i + τ) (y + τ) = vertexIncoming φ row y := by
    ext i u : 1
    change φ (hh (row i + τ - (y + τ))) = φ (hh (row i - y))
    congr 2
    ring
  have hd i : col i + τ - (y + τ) = col i - y := by ring
  simp only [betaEndpointRightPolynomial, ordinaryEndpointProfile,
    beta_matrix_translate, hv, hd]

end SkewCornerDescent.Matrix
