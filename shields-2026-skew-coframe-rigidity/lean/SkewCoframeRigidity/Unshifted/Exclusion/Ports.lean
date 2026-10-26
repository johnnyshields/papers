/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Interface

/-!
# The extreme ports

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`): if neither extreme port occurs the linear equation forces
`Δ = 0`; if exactly one occurs the quadratic equation forces `a - b = 0`; both contradict
`V ≠ W`.  The scalar factor of the explicit-`y` terms has order exactly one.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ} {V W : BetaDiagram (n + 1)} {p : ℕ}

theorem clippedOp_zero_left {K : Type*} [Field K] (M : ℕ) (C : K[X]) (u : PowerSeries K) :
    clippedOp M 0 C u = 0 := by
  simp [clippedOp]

theorem clippedOp_zero_right {K : Type*} [Field K] (M : ℕ) (G : K[X]) (u : PowerSeries K) :
    clippedOp M G 0 u = 0 := by
  simp [clippedOp]

theorem Eop_zero_left {K : Type*} [Field K] (p M : ℕ) (C : K[X]) (u : PowerSeries K) :
    Eop p M 0 C u = 0 := by
  simp [Eop, clippedOp_zero_left]

theorem Eop_zero_right {K : Type*} [Field K] (p M : ℕ) (G : K[X]) (u : PowerSeries K) :
    Eop p M G 0 u = 0 := by
  simp [Eop, clippedOp_zero_right]

theorem hSer_const (V : BetaDiagram (n + 1)) (hM : 2 ≤ span V) :
    PowerSeries.constantCoeff (hSer V) = cohLetters 0 := by
  unfold hSer
  rw [constantCoeff_seriesOf, zeroTop_zero hM]

theorem hSer_coeff_one (V : BetaDiagram (n + 1)) (hM : 3 ≤ span V) :
    PowerSeries.coeff 1 (hSer V) = cohLetters 1 := by
  unfold hSer zeroTop seriesOf
  rw [PowerSeries.coeff_mk, Function.update_of_ne (by omega)]

/-- The scalar factor `p (ϑ^{p-1} - h^{p-1}) z^m` is `z^M` times a unit. -/
theorem pDiff_factor (hM : 3 ≤ span V) (hp : 2 ≤ p) :
    ∃ U : PowerSeries CohField, IsUnit U ∧ pDiff p V = PowerSeries.X ^ span V * U := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  set d : PowerSeries CohField :=
    PowerSeries.C (cohLetters 0) ^ (q + 1) - hSer V ^ (q + 1) with hd
  have hd0 : PowerSeries.constantCoeff d = 0 := by
    rw [hd, map_sub, map_pow, map_pow, PowerSeries.constantCoeff_C, hSer_const V (by omega),
      sub_self]
  obtain ⟨d', hd'⟩ := PowerSeries.X_dvd_iff.2 hd0
  have hd1 : PowerSeries.constantCoeff d' =
      -(((q + 1 : ℕ) : CohField) * cohLetters 0 ^ q * cohLetters 1) := by
    have h1 := congrArg (PowerSeries.coeff 1) hd'
    rw [PowerSeries.coeff_succ_X_mul] at h1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1, hd, map_sub, ← map_pow,
      PowerSeries.coeff_C, if_neg one_ne_zero, coeff_one_pow, hSer_const V (by omega),
      hSer_coeff_one V hM]
    simp only [Nat.add_sub_cancel]
    ring
  have hne : PowerSeries.constantCoeff d' ≠ 0 := by
    rw [hd1, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 (by omega))
      (pow_ne_zero _ (cohLetters_ne_zero 0))) (cohLetters_ne_zero 1)
  refine ⟨PowerSeries.C ((q + 2 : ℕ) : CohField) * d', ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, map_mul, PowerSeries.constantCoeff_C]
    exact (mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) hne).isUnit
  · have hm : span V = (span V - 1) + 1 := by omega
    unfold pDiff
    rw [show q + 2 - 1 = q + 1 from rfl, ← hd, hd']
    conv_rhs => rw [hm]
    rw [pow_succ]
    ring

theorem eq_zero_of_pDiff_vanish (hM : 3 ≤ span V) (hp : 2 ≤ p) {F : CohField[X]}
    (hF : F.natDegree < span V)
    (h : ∀ k < 2 * span V,
      PowerSeries.coeff k (pDiff p V * (F : PowerSeries CohField)) = 0) : F = 0 := by
  obtain ⟨U, hU, hpd⟩ := pDiff_factor hM hp
  have hdvd : PowerSeries.X ^ span V ∣ U * (F : PowerSeries CohField) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    have := h (span V + j) (by omega)
    rw [hpd, mul_assoc, PowerSeries.coeff_X_pow_mul', if_pos (by omega)] at this
    simpa using this
  rw [hU.dvd_mul_left] at hdvd
  ext j
  rw [Polynomial.coeff_zero]
  by_cases hj : j < span V
  · have := (PowerSeries.X_pow_dvd_iff.1 hdvd) j hj
    rwa [Polynomial.coeff_coe] at this
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

section Endpoints

variable {K : Type*} [Field K]

theorem natDegree_endpointA_le (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    (endpointA h D).natDegree ≤ span D - 1 := by
  unfold endpointA
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  have := colPos_lt_span D j
  omega

theorem natDegree_endpointB_le (h : ℕ → K) (D : BetaDiagram (n + 1)) :
    (endpointB h D).natDegree ≤ span D - 1 := by
  unfold endpointB
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  have := rowPos_pos D i
  omega

theorem endpointA_ne_zero (h : ℕ → K) (D : BetaDiagram (n + 1))
    (hT : (properMatrixOf h D).det ≠ 0) (hport : ∃ i, rowPos D i + 1 = span D) :
    endpointA h D ≠ 0 := by
  obtain ⟨i0, hi0⟩ := hport
  intro h0
  have hv : ∀ j, endpointAVec h D j = 0 := by
    intro j
    have := congrArg (fun F : K[X] => F.coeff (colPos D j)) h0
    simp only [endpointA, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      simp [colPos_injective D |>.ne hb.symm]
    · simp
  have hv0 : endpointAVec h D = 0 := funext hv
  have hu : IsUnit (properMatrixOf h D).det := hT.isUnit
  have h1 : (properMatrixOf h D)⁻¹ *ᵥ portIndicator D = 0 := by
    unfold endpointAVec at hv0
    simpa using hv0
  have h2 : portIndicator (K := K) D = 0 := by
    have := congrArg (fun v => (properMatrixOf h D) *ᵥ v) h1
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu] using this
  have := congrFun h2 i0
  simp [portIndicator, hi0] at this

theorem endpointB_ne_zero (h : ℕ → K) (D : BetaDiagram (n + 1))
    (hT : (properMatrixOf h D).det ≠ 0) (hcol : ∃ j, colPos D j = 1) : endpointB h D ≠ 0 := by
  obtain ⟨j0, hj0⟩ := hcol
  intro h0
  have hv : ∀ i, (((properMatrixOf h D)⁻¹)ᵀ *ᵥ colIndicator D) i = 0 := by
    intro i
    have := congrArg (fun F : K[X] => F.coeff (span D - rowPos D i)) h0
    simp only [endpointB, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro b _ hb
      have h1 := rowPos_lt_span D b
      have h2 := rowPos_lt_span D i
      have : span D - rowPos D i ≠ span D - rowPos D b := fun e =>
        hb ((rowPos_injective D) (by omega))
      simp [this]
    · simp
  have hv0 : ((properMatrixOf h D)⁻¹)ᵀ *ᵥ colIndicator D = 0 := funext hv
  have hu : IsUnit (properMatrixOf h D).det := hT.isUnit
  have h2 : colIndicator (K := K) D = 0 := by
    have := congrArg (fun v => (properMatrixOf h D)ᵀ *ᵥ v) hv0
    simpa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu] using this
  have := congrFun h2 j0
  simp [colIndicator, hj0] at this

end Endpoints

section Main

theorem exclusion_expansion (H : ExclusionHyp V W p) :
    (∀ k < 2 * span V, PowerSeries.coeff k (coefY0 p V W) = 0) ∧
    (∀ k < 2 * span V, PowerSeries.coeff k (coefY1 p V W) = 0) ∧
    (∀ k < 2 * span V, PowerSeries.coeff k (coefY2 p V W) = 0) := by
  have h2 : 2 ≤ span V := by have := H.span3; omega
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [coefY0_eq]; exact (coef_vanish H hk).1
  · rw [coefY1_eq h2]; exact (coef_vanish H hk).2.1
  · rw [coefY2_eq h2]; exact (coef_vanish H hk).2.2

/-- Both extreme ports occur. -/
theorem exclusion_ports (H : ExclusionHyp V W p) :
    (∃ i, rowPos V i + 1 = span V) ∧ ∃ j, colPos V j = 1 := by
  have hM3 := H.span3
  have hWV := eq_rotation_of_rotationEquivalent H.colV H.colW H.rot
  have hsch : V.schur = W.schur := by rw [hWV, BetaDiagram.schur_rotation]
  have hWc : W.Connected := V.connected_of_schur_eq W H.conn hsch
  have hr : ∀ i, W.row i = (V.largestLabel : ℤ) - V.col i.rev := fun i => by rw [hWV]; simp
  have hc : ∀ i, W.col i = (V.largestLabel : ℤ) - V.row i.rev := fun i => by rw [hWV]; simp
  have hspan : span V = span W := (span_rot hr hc H.colW).symm
  have hlow : ∀ k, k + 1 < span V → zeroTop V k = cohLetters k := fun k hk => by
    unfold zeroTop; exact Function.update_of_ne (by omega) _ _
  have hT : (properMatrixOf (zeroTop V) V).det ≠ 0 := by
    rw [properMatrixOf_congr V hlow]
    exact properDet_cohLetters_ne_zero H.conn
  have hGV : coframe V = G0 V + C (topY V) * aVec V := by
    have := coframeOf_eq cohLetters V
    rw [endpointA_congr V (h' := zeroTop V) (fun k hk => (hlow k hk).symm)] at this
    exact this
  have hCW : coframe W = C0 V W + C (topY V) * bVec V := by
    have := coframeOf_rot_eq cohLetters hr hc H.colW
    rw [endpointB_congr V (h' := zeroTop V) (fun k hk => (hlow k hk).symm)] at this
    exact this
  have hY1 := (exclusion_expansion H).2.1
  have hY2 := (exclusion_expansion H).2.2
  have hno_a : ¬ (∃ i, rowPos V i + 1 = span V) → aVec V = 0 := fun hP =>
    endpointA_eq_zero_of_no_port _ V fun i hi => hP ⟨i, hi⟩
  have hno_b : ¬ (∃ j, colPos V j = 1) → bVec V = 0 := fun hQ => by
    have : colIndicator (K := CohField) V = 0 := by
      funext j; simp only [colIndicator, Pi.zero_apply]
      rw [if_neg fun h => hQ ⟨j, h⟩]
    unfold bVec endpointB
    simp [this]
  have hdeg : ∀ F : CohField[X], F.natDegree ≤ span V - 1 → F.natDegree < span V :=
    fun F hF => by omega
  by_cases hP : ∃ i, rowPos V i + 1 = span V
  · refine ⟨hP, ?_⟩
    by_contra hQ
    have hb := hno_b hQ
    have ha := endpointA_ne_zero _ V hT hP
    have := eq_zero_of_pDiff_vanish (V := V) (p := p) hM3 H.hp
      (F := aVec V - bVec V) (hdeg _ ((Polynomial.natDegree_sub_le _ _).trans
        (max_le (natDegree_endpointA_le _ V) (natDegree_endpointB_le _ V)))) (fun k hk => by
        have := hY2 k hk
        simpa [coefY2, hb, Eop_zero_right] using this)
    rw [hb, sub_zero] at this
    exact ha this
  · by_cases hQ : ∃ j, colPos V j = 1
    · exfalso
      have ha := hno_a hP
      have hb := endpointB_ne_zero _ V hT hQ
      have := eq_zero_of_pDiff_vanish (V := V) (p := p) hM3 H.hp
        (F := aVec V - bVec V) (hdeg _ ((Polynomial.natDegree_sub_le _ _).trans
          (max_le (natDegree_endpointA_le _ V) (natDegree_endpointB_le _ V)))) (fun k hk => by
          have := hY2 k hk
          simpa [coefY2, ha, Eop_zero_left] using this)
      rw [ha, zero_sub, neg_eq_zero] at this
      exact hb this
    · exfalso
      have ha := hno_a hP
      have hb := hno_b hQ
      rw [ha] at hGV
      rw [hb] at hCW
      have hD : Delta V W = 0 := by
        refine eq_zero_of_pDiff_vanish (V := V) (p := p) hM3 H.hp (F := Delta V W) ?_
          (fun k hk => ?_)
        · have h1 := natDegree_coframe_le V
          have h2 := natDegree_coframe_le W
          have e : Delta V W = coframe V - coframe W := by
            unfold Delta; rw [hGV, hCW]; simp
          rw [e]
          have := Polynomial.natDegree_sub_le (coframe V) (coframe W)
          omega
        · have := hY1 k hk
          simpa [coefY1, ha, hb, Eop_zero_left, Eop_zero_right] using this
      have hGC : coframe V = coframe W := by
        rw [hGV, hCW]
        simp only [mul_zero, add_zero]
        exact sub_eq_zero.1 hD
      obtain ⟨-, hheq⟩ := eq_of_coframe_eq H.colV H.colW H.conn hWc hspan hGC
      exact H.ne (eq_of_heq hheq)

end Main

end SkewCoframeRigidity.Unshifted
