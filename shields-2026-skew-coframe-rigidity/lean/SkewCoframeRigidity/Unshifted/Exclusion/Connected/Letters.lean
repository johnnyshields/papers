/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Ports

/-!
# Dependence on the letters

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`): the quadratic coefficient `[y^2]` commutes with a field homomorphism of
the letters, and the coframe, the endpoint columns and the clipped operator depend only on the
letters below their span.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {K K' : Type*} [Field K] [Field K'] (f : K →+* K') {n : ℕ}

theorem portIndicator_map (D : BetaDiagram (n + 1)) :
    (fun i => f (portIndicator (K := K) D i)) = portIndicator (K := K') D := by
  funext i
  simp only [portIndicator]
  split_ifs <;> simp

theorem colIndicator_map (D : BetaDiagram (n + 1)) :
    (fun i => f (colIndicator (K := K) D i)) = colIndicator (K := K') D := by
  funext i
  simp only [colIndicator]
  split_ifs <;> simp

theorem endpointA_map (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    endpointA (fun j => f (h j)) D = (endpointA h D).map f := by
  have hv : endpointAVec (fun j => f (h j)) D = fun j => f (endpointAVec h D j) := by
    funext j
    unfold endpointAVec
    rw [properMatrixOf_map, matrix_inv_map, ← portIndicator_map f D]
    simp [Matrix.mulVec, dotProduct, map_sum]
  unfold endpointA
  rw [hv]
  simp [Polynomial.map_sum]

theorem endpointB_map (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    endpointB (fun j => f (h j)) D = (endpointB h D).map f := by
  unfold endpointB
  rw [properMatrixOf_map, matrix_inv_map, ← colIndicator_map f D]
  simp [Matrix.mulVec, dotProduct, map_sum, Matrix.transpose_apply, Polynomial.map_sum]

theorem Eop_map (p M : ℕ) (A B : K[X]) (u : PowerSeries K) :
    Eop p M (A.map f) (B.map f) (PowerSeries.map f u) = PowerSeries.map f (Eop p M A B u) := by
  unfold Eop
  have e1 := clippedOp_map f M A B (u ^ p)
  have e2 := clippedOp_map f M A B u
  rw [map_pow] at e1
  rw [← e1, ← e2, map_sub, map_mul, map_mul, map_pow, Polynomial.polynomial_map_coe,
    Polynomial.polynomial_map_coe, PowerSeries.map_C]
  simp only [map_natCast]

theorem genPDiff_map (p : ℕ) (h : ℕ → K) (V : BetaDiagram (n + 1)) :
    genPDiff p (fun j => f (h j)) V = PowerSeries.map f (genPDiff p h V) := by
  unfold genPDiff
  rw [map_mul, map_mul, map_sub, map_pow, map_pow, PowerSeries.map_C, PowerSeries.map_C,
    ← map_seriesOf f h, map_pow, PowerSeries.map_X]
  simp only [map_natCast]

theorem genY2_map (p : ℕ) (h : ℕ → K) (V W : BetaDiagram (n + 1)) :
    genY2 p (fun j => f (h j)) V W = PowerSeries.map f (genY2 p h V W) := by
  unfold genY2
  rw [map_add, map_mul, genPDiff_map, endpointA_map, endpointB_map, map_seriesOf f h |>.symm,
    Eop_map, ← Polynomial.map_sub, Polynomial.polynomial_map_coe]

theorem coframeOf_eq_of_letters {h h' : ℕ → K} (D : BetaDiagram (n + 1))
    (hh : ∀ j < span D, h j = h' j) : coframeOf h D = coframeOf h' D := by
  have hT : properMatrixOf h D = properMatrixOf h' D :=
    properMatrixOf_congr D fun j hj => hh j (by omega)
  have hv : topVecOf h D = topVecOf h' D := by
    funext i
    have e : D.row i.succ - D.col (Fin.last n) = (rowPos D i : ℤ) := (rowPos_cast D i).symm
    simp only [topVecOf, e, letterOf_natCast]
    exact hh _ (rowPos_lt_span D i)
  unfold coframeOf coframeVecOf
  rw [hT, hv]

theorem clippedOp_congr_series (M : ℕ) (G C : K[X]) {u u' : PowerSeries K}
    (hu : ∀ j < M, PowerSeries.coeff j u = PowerSeries.coeff j u') :
    clippedOp M G C u = clippedOp M G C u' := by
  have key : ∀ F : PowerSeries K, PowerSeries.trunc M (u * F) = PowerSeries.trunc M (u' * F) := by
    intro F
    ext i
    simp only [PowerSeries.coeff_trunc]
    split_ifs with hi
    · rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [hu x.1 (by omega)]
    · rfl
  unfold clippedOp
  rw [key, key]

theorem det_properMatrixOf_map (h : ℕ → K) (D : BetaDiagram (n + 1))
    (hT : (properMatrixOf h D).det ≠ 0) :
    (properMatrixOf (fun j => f (h j)) D).det ≠ 0 := by
  rw [properMatrixOf_map]
  have : ((properMatrixOf h D).map f).det = f (properMatrixOf h D).det := (f.map_det _).symm
  rw [this]
  exact (map_ne_zero f).2 hT

end SkewCoframeRigidity.Unshifted
