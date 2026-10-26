/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Scale

/-!
# From the generic letters to the scaled letters

Formalizes the specialization step of the unit case of `sc:positive-power` in
`shields-2026-skew-coframe-rigidity.tex`: the injective ring map of `CohField` into `Eps` sending
`ϑ` to itself and each positive generic letter `H_k` to `ε H_k` carries the complete coframes to
the coframes of the scaled normalized letters (the complete coframe is unchanged when all letters
are multiplied by the nonzero scalar `ϑ⁻¹`), and carries the one-power equation and the equality of
top quotients to the corresponding identities for `epsH` and `hatCoframe`.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial

/-- The inclusion of the generic field into `Eps` as constants. -/
noncomputable def constEps : CohField →+* Eps :=
  (algebraMap CohField[X] Eps).comp (Polynomial.C : CohField →+* CohField[X])

/-- The ring map of `CohRing` into `CohField[ε]` sending `H_k` to `ε H_k` for `k > 0` and `ϑ` to
itself. -/
noncomputable def specRing : CohRing →+* CohField[X] :=
  (MvPolynomial.aeval fun k : ℕ =>
    (Polynomial.C (cohLetters k) * (if k = 0 then 1 else Polynomial.X) : CohField[X]) :
      CohRing →ₐ[ℚ] CohField[X]).toRingHom

/-- The ring map `specRing` is injective. -/
theorem specRing_injective : Function.Injective specRing := by
  have h : (Polynomial.evalRingHom (1 : CohField)).comp specRing =
      algebraMap CohRing CohField := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp only [specRing]
      simp only [mul_ite, mul_one, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, coe_evalRingHom,
        RingHom.coe_coe, Function.comp_apply, MvPolynomial.algHom_C, Polynomial.algebraMap_apply,
        eq_ratCast, eval_C]
      exact (eq_ratCast ((algebraMap CohRing CohField).comp MvPolynomial.C) r).symm
    · by_cases hk : k = 0 <;> simp [specRing, hk, cohLetters]
  intro a b hab
  apply IsFractionRing.injective CohRing CohField
  rw [← h]
  simp [RingHom.comp_apply, hab]

/-- The specialization of the generic field into `Eps`. -/
noncomputable def specField : CohField →+* Eps :=
  IsFractionRing.lift (g := (algebraMap CohField[X] Eps).comp specRing)
    ((IsFractionRing.injective CohField[X] Eps).comp specRing_injective)

/-- The specialization sends `H_k` to `ϑ` times the scaled normalized letter. -/
theorem specField_cohLetters (k : ℕ) :
    specField (cohLetters k) = constEps (cohLetters 0) * epsSeq k := by
  have h1 : specField (cohLetters k) =
      algebraMap CohField[X] Eps (Polynomial.C (cohLetters k) *
        (if k = 0 then 1 else Polynomial.X)) := by
    have e : cohLetters k = algebraMap CohRing CohField (MvPolynomial.X k) := rfl
    conv_lhs => rw [e]
    unfold specField
    rw [IsFractionRing.lift_algebraMap]
    simp [specRing]
  rw [h1]
  unfold epsSeq scaledSeq constEps scaledLetter
  rw [RingHom.comp_apply, ← map_mul]
  congr 1
  by_cases hk : k = 0
  · subst hk
    simp
  · have : ((k : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hk
    simp only [hk, ite_false, Int.natCast_nonneg, not_lt.mpr, this, Int.toNat_natCast]
    simp [normLetters, ← mul_assoc, ← Polynomial.C_mul, mul_div_cancel₀ _ cohLetters_zero_ne_zero]

/-- The constants embedding is injective. -/
theorem constEps_ne_zero {x : CohField} (hx : x ≠ 0) : constEps x ≠ 0 :=
  (map_ne_zero_iff _ (RingHom.injective _)).2 hx

/-- A field homomorphism commutes with the complete coframe. -/
theorem coframeOf_map {K L : Type*} [Field K] [Field L] (f : K →+* L) {n : ℕ} (h : ℕ → K)
    (D : BetaDiagram (n + 1)) :
    coframeOf (fun k => f (h k)) D = (coframeOf h D).map f := by
  have hP : properMatrixOf (fun k => f (h k)) D = f.mapMatrix (properMatrixOf h D) := by
    ext i j
    simp only [properMatrixOf, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact letterOf_map f (map_zero _) h _
  have hv : topVecOf (fun k => f (h k)) D = f ∘ topVecOf h D := by
    ext i
    exact letterOf_map f (map_zero _) h _
  have hinv : (f.mapMatrix (properMatrixOf h D))⁻¹ = f.mapMatrix (properMatrixOf h D)⁻¹ := by
    rw [Matrix.inv_def, Matrix.inv_def, ← RingHom.map_adjugate, ← RingHom.map_det]
    ext i j
    simp [Ring.inverse_eq_inv']
  have hvec : coframeVecOf (fun k => f (h k)) D = f ∘ coframeVecOf h D := by
    ext j
    unfold coframeVecOf
    rw [hP, hv, hinv]
    simp only [Pi.neg_apply, Function.comp_apply, map_neg]
    exact congrArg Neg.neg (RingHom.map_mulVec f _ _ j).symm
  unfold coframeOf
  rw [hvec]
  simp [Polynomial.map_sum]

/-- The complete coframe for the scaled letters is the specialization of the generic one. -/
theorem hatCoframe_eq {n : ℕ} (D : BetaDiagram (n + 1)) :
    hatCoframe D = (coframe D).map specField := by
  unfold hatCoframe coframe
  rw [← coframeOf_map]
  simp only [specField_cohLetters]
  exact (scale_coframeOf epsSeq _ (constEps_ne_zero cohLetters_zero_ne_zero) D).symm

/-- The specialization carries the generic letter series to `ϑ` times the scaled series. -/
theorem map_letterSeries :
    PowerSeries.map specField letterSeries =
      PowerSeries.C (constEps (cohLetters 0)) * epsH := by
  ext k
  simp [letterSeries, seriesOf, epsH, specField_cohLetters]

/-- The clipped operator commutes with ring homomorphisms. -/
theorem clippedOp_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (M : ℕ) (G C : R[X])
    (u : PowerSeries R) :
    clippedOp M (G.map f) (C.map f) (PowerSeries.map f u) = (clippedOp M G C u).map f := by
  unfold clippedOp
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.polynomial_map_coe,
    ← PowerSeries.trunc_map, map_mul]

/-- The clipped operator is linear over constants. -/
theorem clippedOp_C_mul {R : Type*} [CommRing R] (M : ℕ) (G C : R[X]) (c : R)
    (u : PowerSeries R) :
    clippedOp M G C (PowerSeries.C c * u) = Polynomial.C c * clippedOp M G C u := by
  unfold clippedOp
  rw [mul_assoc, mul_assoc, PowerSeries.trunc_C_mul, PowerSeries.trunc_C_mul]
  ring

/-- The scaled letter series over `Eps` is the image of `AH`. -/
theorem epsH_eq : epsH = PowerSeries.map (algebraMap CohField[X] Eps) AH := by
  ext k
  simp only [epsH, epsSeq, scaledSeq, PowerSeries.coeff_mk, PowerSeries.coeff_map, AH,
    map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, Ubar]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [scaledLetter]
  · have h0 : k ≠ 0 := hk.ne'
    have h1 : ((k : ℕ) : ℤ) ≠ 0 := by exact_mod_cast h0
    simp only [scaledLetter, Int.natCast_nonneg, not_lt.mpr, h1, h0, ite_false, Int.toNat_natCast,
      map_mul]
    simp [mul_comm]

/-- The one-power equation with potential `-H^{p-1}` for the scaled letters. -/
theorem hat_power {n : ℕ} {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hs : span D = span E) {p : ℕ} (hp : 1 ≤ p)
    (h : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) -
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) *
          letterSeries ^ (p - 1)) = 0) :
    ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (hatCoframe D) (hatCoframe E) (PowerSeries.X * epsH ^ p) : Eps[X]) :
          PowerSeries Eps) -
        PowerSeries.X * ((clippedOp (span D) (hatCoframe D) (hatCoframe E) epsH : Eps[X]) :
          PowerSeries Eps) * epsH ^ (p - 1)) = 0 := by
  intro k hk
  have hA : ∀ u : PowerSeries CohField,
      PowerSeries.map specField ((clippedOp (span D) (coframe D) (coframe E) u : CohField[X]) :
        PowerSeries CohField) =
      ((clippedOp (span D) (hatCoframe D) (hatCoframe E) (PowerSeries.map specField u) :
        Eps[X]) : PowerSeries Eps) := by
    intro u
    rw [← Polynomial.polynomial_map_coe, hatCoframe_eq, hs, hatCoframe_eq, clippedOp_map]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  set θ := constEps (cohLetters 0) with hθdef
  have hθ : θ ≠ 0 := constEps_ne_zero cohLetters_zero_ne_zero
  have e1 : PowerSeries.map specField (PowerSeries.X * letterSeries ^ (q + 1)) =
      PowerSeries.C (θ ^ (q + 1)) * (PowerSeries.X * epsH ^ (q + 1)) := by
    rw [map_mul, map_pow, PowerSeries.map_X, map_letterSeries, mul_pow, map_pow]
    ring
  have e2 : PowerSeries.map specField ((defect D E : CohField[X]) : PowerSeries CohField) =
      PowerSeries.C θ * ((clippedOp (span D) (hatCoframe D) (hatCoframe E) epsH : Eps[X]) :
        PowerSeries Eps) := by
    unfold defect
    rw [hA, map_letterSeries, clippedOp_C_mul, Polynomial.coe_mul, Polynomial.coe_C]
  have e3 : PowerSeries.map specField
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ (q + 1)) :
          CohField[X]) : PowerSeries CohField)) =
      PowerSeries.C (θ ^ (q + 1)) * ((clippedOp (span D) (hatCoframe D) (hatCoframe E)
        (PowerSeries.X * epsH ^ (q + 1)) : Eps[X]) : PowerSeries Eps) := by
    rw [hA, e1, clippedOp_C_mul, Polynomial.coe_mul, Polynomial.coe_C]
  have key : PowerSeries.map specField
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ (q + 1)) :
          CohField[X]) : PowerSeries CohField) -
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) *
          letterSeries ^ (q + 1 - 1)) =
      PowerSeries.C (θ ^ (q + 1)) *
        (((clippedOp (span D) (hatCoframe D) (hatCoframe E) (PowerSeries.X * epsH ^ (q + 1)) :
          Eps[X]) : PowerSeries Eps) -
        PowerSeries.X * ((clippedOp (span D) (hatCoframe D) (hatCoframe E) epsH : Eps[X]) :
          PowerSeries Eps) * epsH ^ (q + 1 - 1)) := by
    rw [map_sub, map_mul, map_mul, e2, e3, PowerSeries.map_X, Nat.add_sub_cancel,
      map_pow (PowerSeries.map specField) letterSeries q, map_letterSeries,
      map_pow PowerSeries.C θ (q + 1)]
    ring
  have h1 : PowerSeries.coeff k (PowerSeries.map specField
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ (q + 1)) :
          CohField[X]) : PowerSeries CohField) -
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) *
          letterSeries ^ (q + 1 - 1))) = 0 := by
    rw [PowerSeries.coeff_map, h k hk, map_zero]
  rw [key, PowerSeries.coeff_C_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hθ)

/-- Equal top quotients for the scaled letters. -/
theorem hat_top {n : ℕ} {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hs : span D = span E) (hq : topQuotient D = topQuotient E) :
    PowerSeries.coeff (span D) (epsH * (hatCoframe D : PowerSeries Eps)) =
      PowerSeries.coeff (span D) (epsH * (hatCoframe E : PowerSeries Eps)) := by
  have key : ∀ {m : ℕ} (F : BetaDiagram (m + 1)), span F = span D →
      specField (topQuotient F) = constEps (cohLetters 0) *
        PowerSeries.coeff (span D) (epsH * (hatCoframe F : PowerSeries Eps)) := by
    intro m F hF
    have e : topQuotient F = PowerSeries.coeff (span D) (letterSeries *
        (coframe F : PowerSeries CohField)) := by
      rw [← hF]
      rfl
    rw [e, ← PowerSeries.coeff_map, map_mul, Polynomial.polynomial_map_coe.symm,
      ← hatCoframe_eq, map_letterSeries, mul_assoc, PowerSeries.coeff_C_mul]
  have h1 := key D rfl
  have h2 := key E hs.symm
  rw [hq] at h1
  exact mul_left_cancel₀ (constEps_ne_zero cohLetters_zero_ne_zero) (h1.symm.trans h2)

end SkewCoframeRigidity.UnitCase
