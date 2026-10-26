/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BetaEndpointPolynomial
import SkewCornerDescent.Matrix.BlockResponse

/-!
# Linear entry variation of a complete retained response

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The entry variation is linear before selecting any original generator.
Both endpoint paths and the full internal inverse path remain present.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

variable {F ν : Type*} [CommRing F] [Fintype ν] [DecidableEq ν]

/-- The complete four-path first variation, as a linear map of the entry directions. -/
noncomputable def endpointVariation (row col : ν → ℤ) (x y : ℤ)
    (incoming outgoing : ν → F) : (ℤ → F) →ₗ[F] F :=
  LinearMap.proj (x - y) -
    ∑ i, outgoing i • LinearMap.proj (x - col i) -
    ∑ i, incoming i • LinearMap.proj (row i - y) +
    ∑ i, ∑ j, (incoming i * outgoing j) • LinearMap.proj (row i - col j)

omit [DecidableEq ν] in
/-- A single original index selector gives exactly the full endpoint-product coefficient. -/
theorem endpointVariation_indicator (row col : ν → ℤ) (x y j : ℤ)
    (incoming outgoing : ν → F) :
    endpointVariation row col x y incoming outgoing (fun z => if z = j then 1 else 0) =
      (endpointProfile (fun i => x - row i) incoming *
        endpointProfile (fun i => col i - y) outgoing).coeff (x - y - j) := by
  classical
  simp only [endpointVariation, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, endpointProfile_mul_coeff]
  have hz : (x - y - j = 0) ↔ x - y = j := by omega
  have hl (i : ν) : (x - row i = x - y - j) ↔ row i - y = j := by omega
  have hr (i : ν) : (col i - y = x - y - j) ↔ x - col i = j := by omega
  have hi (i k : ν) : (x - row i + (col k - y) = x - y - j) ↔
      row i - col k = j := by omega
  simp only [hz, hl, hr, hi]
  abel

/-- Full inverse differentiation is the linear variation evaluated on the actual entry
values. Its domain includes arbitrary entry directions, not only surviving higher indices. -/
theorem retainedResponse_endpointVariation {R : Type*} [CommRing R] [Algebra R F]
    (δ : Derivation R F F) (φ : Lambda →+* F) (row col : ν → ℤ) (x y : ℤ)
    [Invertible (vertexBetaMatrix φ row col)] :
    δ (φ (hh (x - y)) -
      (vertexOutgoing φ col x * ⅟(vertexBetaMatrix φ row col) *
        vertexIncoming φ row y) () ()) =
      endpointVariation row col x y
        (fun i => (vertexOutgoing φ col x * ⅟(vertexBetaMatrix φ row col)) () i)
        (fun i => (⅟(vertexBetaMatrix φ row col) * vertexIncoming φ row y) i ())
        (fun z => δ (φ (hh z))) := by
  classical
  let B := vertexOutgoing φ col x
  let C := vertexIncoming φ row y
  let P := vertexBetaMatrix φ row col
  let Q := ⅟P
  have h := congrFun (congrFun (entryDeriv_retainedResponse δ
    (fun _ _ : Unit => φ (hh (x - y))) B C P) ()) ()
  change δ (retainedResponse (fun _ _ : Unit => φ (hh (x - y))) B C P () ()) =
    (entryDeriv δ (fun _ _ : Unit => φ (hh (x - y))) -
      entryDeriv δ B * Q * C - B * Q * entryDeriv δ C +
      B * Q * entryDeriv δ P * Q * C) () () at h
  change δ (retainedResponse (fun _ _ : Unit => φ (hh (x - y))) B C P () ()) = _
  rw [h]
  change (entryDeriv δ (fun _ _ : Unit => φ (hh (x - y))) -
    entryDeriv δ B * Q * C - B * Q * entryDeriv δ C +
    B * Q * entryDeriv δ P * Q * C) () () = _
  rw [Matrix.mul_assoc (entryDeriv δ B) Q C,
    Matrix.mul_assoc (B * Q * entryDeriv δ P) Q C]
  have hI : (B * Q * entryDeriv δ P * (Q * C)) () () =
      ∑ i, ∑ k, (B * Q) () i * (Q * C) k () * δ (φ (hh (row i - col k))) := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply (M := B * Q) (N := entryDeriv δ P), Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    change (B * Q) () i * δ (φ (hh (row i - col k))) * (Q * C) k () = _
    ring
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [hI]
  simp only [endpointVariation, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
    Matrix.mul_apply, entryDeriv,
    B, C, vertexOutgoing, vertexIncoming, Matrix.of_apply]
  simp only [Q, P, mul_comm]

end SkewCornerDescent.Matrix
