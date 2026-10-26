/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadBridge
import SkewCoframeRigidity.UnitRestoration.ZeroRange

/-!
# The first variation of the coframe from physical weights

For constant rational weights `ρ` on genuine vacancies of `B`, with `ṡ_B = 0` and
`ṡ_{K ◁ B} = 0` at the physical unit, `firstVar B ρ` is the first variation
`Q = ∑ ρ_b δ^{(b)}` of the complete coframe over the coherent letters.  This file re-indexes
the weights from `ρ.support` to positions in `Fin μ`, bridges the hypotheses through
`restorationSum_eq_zero_of_dotW_eq_zero`, and applies `linearized_observations` and
`linearized_zero_range_of_observations`.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Polynomial

/-- The positions of the weighted vacancies, enumerated by `Fin ρ.support.card`. -/
noncomputable def vacPos (ρ : ℤ →₀ ℚ) : Fin ρ.support.card → ℕ :=
  fun v => ((ρ.support.equivFin.symm v : ρ.support) : ℤ).toNat

/-- The weights, as elements of the raw field. -/
noncomputable def vacWt (ρ : ℤ →₀ ℚ) : Fin ρ.support.card → CohField :=
  fun v => algebraMap (MvPolynomial ℕ ℚ) CohField
    (MvPolynomial.C (ρ (ρ.support.equivFin.symm v : ρ.support)))

/-- The first variation `Q = ∑ ρ_b δ^{(b)}` of the complete right coframe of `B`. -/
noncomputable def firstVar {b : ℕ} (B : BetaDiagram (b + 1)) (ρ : ℤ →₀ ℚ) : CohField[X] :=
  pulseSum cohLetters (rowPos B) (colPos B) (vacPos ρ)
    (fun v => PowerSeries.coeff (vacPos ρ v) (letterSeries * (coframe B : PowerSeries CohField)))
    (vacWt ρ)

theorem vacWt_mem (ρ : ℤ →₀ ℚ) (m : ℕ) (v : Fin ρ.support.card) :
    vacWt ρ v ∈ letterField m := by
  unfold vacWt
  have : algebraMap (MvPolynomial ℕ ℚ) CohField
      (MvPolynomial.C (ρ (ρ.support.equivFin.symm v : ρ.support))) =
      ((ρ (ρ.support.equivFin.symm v : ρ.support) : ℚ) : CohField) := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, eq_ratCast]
  rw [this]
  exact SubfieldClass.ratCast_mem _ _

section Obs

variable {k b : ℕ}

/-- The data hypotheses of `linearized_observations`, from physical weights. -/
theorem firstVar_hyps (B : BetaDiagram (b + 1)) (hB : IsNorm B) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) :
    (∀ v, 0 < vacPos ρ v ∧ vacPos ρ v < span B) ∧ Function.Injective (vacPos ρ) ∧
      ∀ v j, vacPos ρ v ≠ colPos B j := by
  have hpos : ∀ v, 0 < ((ρ.support.equivFin.symm v : ρ.support) : ℤ) := fun v =>
    (hρ _ (ρ.support.equivFin.symm v).2).1
  refine ⟨fun v => ?_, fun v w hvw => ?_, fun v j hvj => ?_⟩
  · have h := hρ _ (ρ.support.equivFin.symm v).2
    have := h.2.1
    have := h.1
    have hs : (span B : ℤ) = B.largestLabel := by
      unfold span; have := B.largestLabel_pos; omega
    unfold vacPos
    constructor <;> omega
  · unfold vacPos at hvw
    have h1 := hpos v
    have h2 := hpos w
    have : ((ρ.support.equivFin.symm v : ρ.support) : ℤ) =
        ((ρ.support.equivFin.symm w : ρ.support) : ℤ) := by omega
    exact (Equiv.injective _) (Subtype.ext this)
  · have h := hρ _ (ρ.support.equivFin.symm v).2
    have hc : (colPos B j : ℤ) = B.col j.castSucc := by
      have h0 : B.col (Fin.last b) = 0 := hB
      have := colPos_cast B j
      rw [h0, sub_zero] at this
      exact this
    have hv := hpos v
    unfold vacPos at hvj
    exact h.2.2.2 j.castSucc (by omega)


theorem restorationSum_reindex {N : ℕ} (D : BetaDiagram N) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, 0 ≤ x) (h : dotW D ρ = 0) :
    ∑ v, vacWt ρ v * restorationPoly cohLetters D (vacPos ρ v) = 0 := by
  have := restorationSum_eq_zero_of_dotW_eq_zero D ρ hρ h
  rw [← this]
  unfold vacWt vacPos
  rw [← Finset.sum_coe_sort ρ.support]
  exact Fintype.sum_equiv ρ.support.equivFin.symm _ _ (fun v => rfl)

/-- **The linearized observations from physical weights.**  `ṡ_B = 0` and `ṡ_{K ◁ B} = 0` at the
physical unit give `[HQ]_{span B} = 0` and `[H C_K Q]_{span B + span K} = 0` for the first
variation `Q = firstVar B ρ`. -/
theorem firstVar_observations (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) :
    PowerSeries.coeff (span B) (letterSeries * (firstVar B ρ : PowerSeries CohField)) = 0 ∧
    PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * firstVar B ρ : CohField[X]) : PowerSeries CohField)) = 0 := by
  obtain ⟨hpos, hinj, hS⟩ := firstVar_hyps B hB ρ hρ
  have hnn : ∀ x ∈ ρ.support, 0 ≤ x := fun x hx => (hρ x hx).1.le
  exact linearized_observations K B hK hB hKc hBc (vacPos ρ) hpos hinj hS (vacWt ρ)
    (fun v => vacWt_mem ρ _ v) (restorationSum_reindex B ρ hnn h1)
    (restorationSum_reindex (splice K B hK hB) ρ hnn h2)

/-- **The zero range for physical weights**: if the coefficients of `Q = firstVar B ρ` use only
letters of index at most `R`, then `Q_j = 0` for `j < span B + span K - max(R, span K - 1)`. -/
theorem firstVar_zero_range (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (R : ℕ)
    (hR : ∀ s, (firstVar B ρ).coeff s ∈ letterField (R + 1)) (j : ℕ)
    (hj : j + max R (span K - 1) < span B + span K) : (firstVar B ρ).coeff j = 0 := by
  obtain ⟨hpos, hinj, hS⟩ := firstVar_hyps B hB ρ hρ
  have hnn : ∀ x ∈ ρ.support, 0 ≤ x := fun x hx => (hρ x hx).1.le
  exact linearized_zero_range_of_observations K B hK hB hKc hBc (vacPos ρ) hpos hinj hS (vacWt ρ)
    (fun v => vacWt_mem ρ _ v) (restorationSum_reindex B ρ hnn h1)
    (restorationSum_reindex (splice K B hK hB) ρ hnn h2) R hR j hj

end Obs

end SkewCoframeRigidity.UnitRestoration
