/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Expansion
import SkewCoframeRigidity.Unshifted.First

/-!
# The coefficients of the expansion in the top letter

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`): the unshifted identity at the generic letters holds at the shifted
letters `H_m ↦ H_m + s`, so the polynomial `[y^0] + y [y^1] + y² [y^2]` in `y = H_m` vanishes at
three values of `y`, and each coefficient vanishes.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

section Map

variable {K K' : Type*} [Field K] [Field K'] (f : K →+* K')

theorem clippedOp_map_letters (p : ℕ) (h : ℕ → K) (V W : BetaDiagram (n + 1)) :
    clippedOp (span V) (coframeOf (fun j => f (h j)) V) (coframeOf (fun j => f (h j)) W)
      (seriesOf (fun j => f (h j)) ^ p) =
      (clippedOp (span V) (coframeOf h V) (coframeOf h W) (seriesOf h ^ p)).map f := by
  rw [coframeOf_map, coframeOf_map, ← map_seriesOf f h, ← map_pow, clippedOp_map]

theorem unshiftedEq_map {p : ℕ} {h : ℕ → K} {V W : BetaDiagram (n + 1)}
    (H : UnshiftedEq p h V W) : UnshiftedEq p (fun j => f (h j)) V W := by
  intro k hk
  have e1 := clippedOp_map_letters f p h V W
  have e2 := clippedOp_map_letters f 1 h V W
  simp only [pow_one] at e2
  rw [e1, e2, Polynomial.coeff_map, H k hk, map_mul, map_natCast, ← map_seriesOf f h, ← map_pow,
    Polynomial.polynomial_map_coe, ← map_mul (PowerSeries.map f), PowerSeries.coeff_map]

end Map

section Main

variable {V W : BetaDiagram (n + 1)} {p : ℕ}

theorem zeroTop_zero (hM : 2 ≤ span V) : zeroTop V 0 = cohLetters 0 := by
  unfold zeroTop
  exact Function.update_of_ne (by omega) _ _

theorem coefY1_eq (hM : 2 ≤ span V) : coefY1 p V W = genY1 p (zeroTop V) V W := by
  unfold coefY1 genY1 pDiff genPDiff
  rw [zeroTop_zero hM]
  rfl

theorem coefY2_eq (hM : 2 ≤ span V) : coefY2 p V W = genY2 p (zeroTop V) V W := by
  unfold coefY2 genY2 pDiff genPDiff
  rw [zeroTop_zero hM]
  rfl

theorem coefY0_eq : coefY0 p V W = genY0 p (zeroTop V) V W := rfl

theorem shifted_identity (H : ExclusionHyp V W p) (s : ℤ) :
    ∀ k < 2 * span V, PowerSeries.coeff k
      (genY0 p (zeroTop V) V W + PowerSeries.C (cohLetters (span V - 1) + s) *
        genY1 p (zeroTop V) V W +
        PowerSeries.C ((cohLetters (span V - 1) + s) ^ 2) * genY2 p (zeroTop V) V W) = 0 := by
  have hWV := eq_rotation_of_rotationEquivalent H.colV H.colW H.rot
  have hsch : V.schur = W.schur := by rw [hWV, BetaDiagram.schur_rotation]
  have hD0 := (coequal_data H.conn hsch).2.2.2.2.1
  have hh : (fun j => shiftField (span V - 1) s (cohLetters j)) =
      Function.update (zeroTop V) (span V - 1) (cohLetters (span V - 1) + s) := by
    funext j
    rw [shiftField_cohLetters]
    unfold zeroTop
    rw [Function.update_idem]
  have hr : ∀ i, W.row i = (V.largestLabel : ℤ) - V.col i.rev := fun i => by rw [hWV]; simp
  have hc : ∀ i, W.col i = (V.largestLabel : ℤ) - V.row i.rev := fun i => by rw [hWV]; simp
  apply expand_at hr hc H.colW p H.hp (zeroTop V) (by simp [zeroTop]) H.span3
  · rw [← hh]
    intro k hk
    have e := clippedOp_map_letters (shiftField (span V - 1) s) 1 cohLetters V W
    simp only [pow_one] at e
    rw [e, Polynomial.coeff_map]
    have := hD0 k hk
    change (clippedOp (span V) (coframe V) (coframe W) letterSeries).coeff k = 0 at this
    erw [this]
    exact map_zero _
  · rw [← hh]
    exact unshiftedEq_map _ H.eq

theorem coef_vanish (H : ExclusionHyp V W p) {k : ℕ} (hk : k < 2 * span V) :
    PowerSeries.coeff k (genY0 p (zeroTop V) V W) = 0 ∧
    PowerSeries.coeff k (genY1 p (zeroTop V) V W) = 0 ∧
    PowerSeries.coeff k (genY2 p (zeroTop V) V W) = 0 := by
  have e : ∀ s : ℤ, PowerSeries.coeff k (genY0 p (zeroTop V) V W) +
      (cohLetters (span V - 1) + s) * PowerSeries.coeff k (genY1 p (zeroTop V) V W) +
      (cohLetters (span V - 1) + s) ^ 2 * PowerSeries.coeff k (genY2 p (zeroTop V) V W) = 0 := by
    intro s
    have := shifted_identity H s k hk
    rwa [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at this
  set y := cohLetters (span V - 1)
  set c0 := PowerSeries.coeff k (genY0 p (zeroTop V) V W)
  set c1 := PowerSeries.coeff k (genY1 p (zeroTop V) V W)
  set c2 := PowerSeries.coeff k (genY2 p (zeroTop V) V W)
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp only [Int.cast_zero, Int.cast_one, Int.cast_ofNat, add_zero] at e0 e1 e2
  have h2 : (2 : CohField) * c2 = 0 := by linear_combination e2 - 2 * e1 + e0
  have hc2 : c2 = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hc1 : c1 = 0 := by
    rw [hc2] at e0 e1
    linear_combination e1 - e0
  refine ⟨?_, hc1, hc2⟩
  rw [hc1, hc2] at e0
  linear_combination e0

end Main

end SkewCoframeRigidity.Unshifted
