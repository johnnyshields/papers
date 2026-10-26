/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Atlas
import SkewCoframeRigidity.Stationary.ComponentRemainder

/-!
# The coframe and numerator as polynomials in the atlas coordinates

Formalizes the passage to independent coordinates in `shields-2026-skew-coframe-rigidity.tex`,
`sc:atlas` and `sc:component-remainder`.  The generic coframe `G` and numerator
`P = [HG]_{<M}` of a connected diagram are the images, under the evaluation at the atlas
coordinates, of the polynomials `Gm`, `Pm` over the polynomial ring in the atlas indices.  By
the algebraic independence of the atlas, a nonzero polynomial expression in `Gm`, `Pm` has
nonzero image, which reduces nonvanishing of the component remainder to a specialization.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The polynomial ring of the atlas indices. -/
abbrev AtlasRing (D : BetaDiagram (n + 1)) : Type := MvPolynomial (AtlasIdx D) ℚ

/-- The evaluation at the atlas coordinates. -/
noncomputable def atlasEval (D : BetaDiagram (n + 1)) : AtlasRing D →+* CohField :=
  (MvPolynomial.aeval (atlasCoords D) : AtlasRing D →ₐ[ℚ] CohField).toRingHom

/-- The coframe as a polynomial in the atlas coordinates. -/
noncomputable def Gm (D : BetaDiagram (n + 1)) : (AtlasRing D)[X] :=
  1 + ∑ j : Fin n, C (MvPolynomial.X (some (Sum.inl j))) * X ^ colPos D j

/-- The coefficient of the numerator at the position `i`, as an atlas coordinate. -/
noncomputable def pcoord (D : BetaDiagram (n + 1)) (i : ℕ) : AtlasRing D :=
  if i = 0 then MvPolynomial.X none
  else if h : 0 < i ∧ i < span D ∧ i ∉ rowSet D then MvPolynomial.X (some (Sum.inr ⟨i, h⟩))
  else 0

/-- The numerator as a polynomial in the atlas coordinates. -/
noncomputable def Pm (D : BetaDiagram (n + 1)) : (AtlasRing D)[X] :=
  ∑ i ∈ Finset.range (span D), C (pcoord D i) * X ^ i

theorem Gm_map (D : BetaDiagram (n + 1)) : (Gm D).map (atlasEval D) = coframe D := by
  unfold Gm coframe coframeOf
  simp [Polynomial.map_add, Polynomial.map_sum, atlasEval, atlasCoords, coframeVec]

theorem Pm_coeff (D : BetaDiagram (n + 1)) (i : ℕ) :
    (Pm D).coeff i = if i < span D then pcoord D i else 0 := by
  unfold Pm
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hi : i < span D
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.2 hi) h
  · rw [if_neg hi]
    refine Finset.sum_eq_zero fun x hx => ?_
    have := Finset.mem_range.1 hx
    rw [if_neg (by omega), mul_zero]

theorem Pm_map {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    (Pm D).map (atlasEval D) = numerator D := by
  ext i
  rw [Polynomial.coeff_map, Pm_coeff]
  by_cases hi : i < span D
  · rw [if_pos hi]
    unfold pcoord
    by_cases h0 : i = 0
    · subst h0
      simp [atlasEval, atlasCoords, numerator_coeff_zero]
    · rw [if_neg h0]
      by_cases hfree : 0 < i ∧ i < span D ∧ i ∉ rowSet D
      · rw [dif_pos hfree]
        simp [atlasEval, atlasCoords]
      · rw [dif_neg hfree, map_zero]
        have hmem : i ∈ rowSet D := by
          by_contra hn; exact hfree ⟨Nat.pos_of_ne_zero h0, hi, hn⟩
        exact ((numerator_coeff_eq_zero_iff hD (Nat.pos_of_ne_zero h0) hi).2 hmem).symm
  · rw [if_neg hi, map_zero]
    unfold numerator numeratorOf
    rw [PowerSeries.coeff_trunc, if_neg hi]

theorem coeff_zero_Gm (D : BetaDiagram (n + 1)) : (Gm D).coeff 0 = 1 := by
  unfold Gm
  rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.finsetSum_coeff]
  have : ∀ j ∈ Finset.univ, (C (MvPolynomial.X (some (Sum.inl j)) : AtlasRing D) *
      X ^ colPos D j).coeff 0 = 0 := by
    intro j _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (colPos_pos D j).ne, mul_zero]
  rw [Finset.sum_eq_zero this, add_zero]

/-- The inverse series of `Gm`. -/
noncomputable def ginvM (D : BetaDiagram (n + 1)) : PowerSeries (AtlasRing D) :=
  PowerSeries.invOfUnit (Gm D : PowerSeries (AtlasRing D)) 1

theorem Gm_mul_ginvM (D : BetaDiagram (n + 1)) :
    (Gm D : PowerSeries (AtlasRing D)) * ginvM D = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_zero_Gm]
    rfl)

/-- The remainder as a series coefficient in the atlas ring. -/
noncomputable def alphaM (D : BetaDiagram (n + 1)) (p : ℕ) : AtlasRing D :=
  PowerSeries.coeff (span D) ((Pm D : PowerSeries (AtlasRing D)) ^ p * (ginvM D) ^ (p - 1))

theorem map_ginvM (D : BetaDiagram (n + 1)) :
    PowerSeries.map (atlasEval D) (ginvM D) = (coframe D : PowerSeries CohField)⁻¹ := by
  have h1 := congrArg (PowerSeries.map (atlasEval D)) (Gm_mul_ginvM D)
  rw [map_mul, map_one] at h1
  have e : PowerSeries.map (atlasEval D) (Gm D : PowerSeries (AtlasRing D)) =
      (coframe D : PowerSeries CohField) := by
    rw [← Gm_map D]; exact Polynomial.polynomial_map_coe.symm
  rw [e] at h1
  have hg0 : PowerSeries.constantCoeff (coframe D : PowerSeries CohField) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_coframe]
    exact one_ne_zero
  calc PowerSeries.map (atlasEval D) (ginvM D)
      = (coframe D : PowerSeries CohField)⁻¹ * ((coframe D : PowerSeries CohField) *
          PowerSeries.map (atlasEval D) (ginvM D)) := by
        rw [← mul_assoc, mul_comm _ (coframe D : PowerSeries CohField),
          PowerSeries.mul_inv_cancel _ hg0, one_mul]
    _ = _ := by rw [h1, mul_one]

theorem atlasEval_alphaM {D : BetaDiagram (n + 1)} (hD : D.Connected) (p : ℕ) :
    atlasEval D (alphaM D p) =
      PowerSeries.coeff (span D)
        ((numerator D : PowerSeries CohField) ^ p *
          ((coframe D : PowerSeries CohField)⁻¹) ^ (p - 1)) := by
  unfold alphaM
  rw [← PowerSeries.coeff_map, map_mul, map_pow, map_pow, map_ginvM, ← Pm_map hD]
  rw [Polynomial.polynomial_map_coe]

/-- A specialization of the atlas coordinates to rationals. -/
noncomputable def specEval (D : BetaDiagram (n + 1)) (v : AtlasIdx D → ℚ) : AtlasRing D →+* ℚ :=
  (MvPolynomial.aeval v : AtlasRing D →ₐ[ℚ] ℚ).toRingHom

/-- The component remainder is nonzero as soon as one rational specialization of the atlas
coordinates gives a nonzero value of `[P^p G^{1-p}]_L`. -/
theorem remainder_ne_zero_of_specialization {D : BetaDiagram (n + 1)} (hD : D.Connected)
    (p : ℕ) (v : AtlasIdx D → ℚ) (Ginv : PowerSeries ℚ)
    (hG : (((Gm D).map (specEval D v) : Polynomial ℚ) : PowerSeries ℚ) * Ginv = 1)
    (hv : PowerSeries.coeff (span D)
      ((((Pm D).map (specEval D v) : Polynomial ℚ) : PowerSeries ℚ) ^ p * Ginv ^ (p - 1)) ≠ 0) :
    PowerSeries.coeff (span D)
      ((numerator D : PowerSeries CohField) ^ p *
        ((coframe D : PowerSeries CohField)⁻¹) ^ (p - 1)) ≠ 0 := by
  rw [← atlasEval_alphaM hD]
  intro h0
  have hinj : Function.Injective (atlasEval D) :=
    atlasCoords_algebraicIndependent hD
  have h1 : alphaM D p = 0 := hinj (by rw [h0, map_zero])
  apply hv
  have hginv : PowerSeries.map (specEval D v) (ginvM D) = Ginv := by
    have h2 := congrArg (PowerSeries.map (specEval D v)) (Gm_mul_ginvM D)
    rw [map_mul, map_one, ← Polynomial.polynomial_map_coe] at h2
    calc PowerSeries.map (specEval D v) (ginvM D)
        = (((Gm D).map (specEval D v) : Polynomial ℚ) * Ginv) *
            PowerSeries.map (specEval D v) (ginvM D) := by rw [hG, one_mul]
      _ = Ginv * (((Gm D).map (specEval D v) : Polynomial ℚ) *
            PowerSeries.map (specEval D v) (ginvM D)) := by ring
      _ = Ginv := by rw [h2, mul_one]
  have := congrArg (specEval D v) h1
  rw [map_zero] at this
  unfold alphaM at this
  rw [← PowerSeries.coeff_map, map_mul, map_pow, map_pow, hginv,
    ← Polynomial.polynomial_map_coe] at this
  exact this

end SkewCoframeRigidity.Coframe
