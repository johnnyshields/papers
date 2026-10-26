/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadLower
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadObs
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadDeriv
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadUnique

/-!
# Lowering the ceiling of the first variation

If `ṡ_B = 0` and `ṡ_{K ◁ B} = 0`, the coefficients of the first variation `Q = firstVar B ρ` lie
in `letterField (M₀)`, where `M₀` exceeds the head row `t` and every weighted vacancy.  One step:
if the coefficients lie in `letterField (L + 1)` with `L ≥ M₀`, the derivative `∂_L Q` is a
vacancy-pulse tangent with vanishing vacancy values and vanishing row equations (the zero range
removes `Q_{x-L}`), hence zero by `pulse_tangent_unique`; field descent then gives
`letterField L`.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Polynomial

theorem pulseSum_coeff_eq_zero {μ n : ℕ} (U : ℕ → CohField) (I S : Fin n → ℕ)
    (bpos : Fin μ → ℕ) (P ρ : Fin μ → CohField) (j : ℕ) (hb : ∀ v, j ≠ bpos v)
    (hS : ∀ s, j ≠ S s) : (pulseSum U I S bpos P ρ).coeff j = 0 := by
  unfold pulseSum
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [Polynomial.coeff_C_mul, coeff_pulse, if_neg (hb v)]
  rw [Finset.sum_eq_zero (fun s _ => by rw [if_neg (hS s), mul_zero])]
  ring

theorem colPos_injective {n : ℕ} (B : BetaDiagram (n + 1)) (hB : IsNorm B) :
    Function.Injective (colPos B) := by
  intro i j hij
  have h0 : B.col (Fin.last n) = 0 := hB
  have hi := colPos_cast B i
  have hj := colPos_cast B j
  rw [h0, sub_zero] at hi hj
  have : B.col i.castSucc = B.col j.castSucc := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hij
    omega
  exact Fin.castSucc_injective _ (B.col_strictAnti.injective this)

section Step

variable {k n : ℕ}

/-- **One step of the descent.** -/
theorem firstVar_ceiling_step (K : BetaDiagram (k + 1)) (B : BetaDiagram (n + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (M₀ : ℕ)
    (hP : ∀ v, (PowerSeries.coeff (vacPos ρ v) (letterSeries *
      (coframe B : PowerSeries CohField))) ∈ letterField M₀)
    (L : ℕ) (hL : M₀ ≤ L) (hQ : ∀ s, (firstVar B ρ).coeff s ∈ letterField (L + 1)) :
    ∀ s, (firstVar B ρ).coeff s ∈ letterField L := by
  classical
  obtain ⟨hpos, hinj, hbS⟩ := firstVar_hyps B hB ρ hρ
  have hT : (properMat cohLetters (rowPos B) (colPos B)).det ≠ 0 := by
    rw [properMat_eq]; exact properDet_cohLetters_ne_zero hBc
  have hspec := pulseSum_spec cohLetters (rowPos B) (colPos B) hT (vacPos ρ)
    (fun v => PowerSeries.coeff (vacPos ρ v) (letterSeries * (coframe B : PowerSeries CohField)))
    (vacWt ρ) (colPos_pos B) (fun v => (hpos v).1) hinj hbS
  have hQd : dPoly L (firstVar B ρ) = 0 := by
    refine pulse_tangent_unique cohLetters (rowPos B) (colPos B) hT (colPos_injective B hB)
      (vacPos ρ) (dPoly L (firstVar B ρ)) ?_ ?_ ?_
    · intro j hj
      rw [coeff_dPoly] at hj
      by_contra hno
      push Not at hno
      refine hj ?_
      have : (firstVar B ρ).coeff j = 0 := by
        unfold firstVar
        exact pulseSum_coeff_eq_zero _ _ _ _ _ _ j (fun v => (hno.2 v)) (fun s => hno.1 s)
      rw [this, dRaw_zero]
    · intro v
      rw [coeff_dPoly]
      have hv := hspec.2.2 v
      have hvv : (firstVar B ρ).coeff (vacPos ρ v) = -(vacWt ρ v * PowerSeries.coeff (vacPos ρ v)
          (letterSeries * (coframe B : PowerSeries CohField))) := hv
      rw [hvv, dRaw_neg, dRaw_mul, dRaw_eq_zero_of_mem_letterField L (vacWt_mem ρ L v),
        dRaw_eq_zero_of_mem_letterField L (letterField_mono hL (hP v))]
      ring
    · intro i
      have hrow := hspec.2.1 i
      have key := coeff_letterSeries_mul_dPoly L (firstVar B ρ) (rowPos B i)
      have hmain : PowerSeries.coeff (rowPos B i) (letterSeries * (firstVar B ρ : PowerSeries CohField)) = 0 :=
        hrow
      rw [hmain, dRaw_zero] at key
      change PowerSeries.coeff (rowPos B i) (letterSeries * (dPoly L (firstVar B ρ) : PowerSeries CohField)) = 0
      rw [key]
      split_ifs with hle
      · have := firstVar_zero_range K B hK hB hKc hBc ρ hρ h1 h2 L hQ (rowPos B i - L) (by
          have := rowPos_lt_span B i
          omega)
        rw [this]; simp
      · simp
  intro s
  have h0 : dRaw L ((firstVar B ρ).coeff s) = 0 := by
    rw [← coeff_dPoly, hQd, Polynomial.coeff_zero]
  exact mem_letterField_of_dRaw_eq_zero L (hQ s) h0


/-- **The ceiling descent.**  The coefficients of `Q` lie in the field of the letters below `M₀`
whenever the numerator coefficients at the weighted vacancies do. -/
theorem firstVar_ceiling (K : BetaDiagram (k + 1)) (B : BetaDiagram (n + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (M₀ : ℕ)
    (hP : ∀ v, (PowerSeries.coeff (vacPos ρ v) (letterSeries *
      (coframe B : PowerSeries CohField))) ∈ letterField M₀) :
    ∀ s, (firstVar B ρ).coeff s ∈ letterField M₀ := by
  obtain ⟨hpos, hinj, hbS⟩ := firstVar_hyps B hB ρ hρ
  have hnn : ∀ v, vacWt ρ v ∈ letterField (span B) := fun v => vacWt_mem ρ _ v
  have hbase : ∀ s, (firstVar B ρ).coeff s ∈ letterField (span B) := fun s =>
    pulseSum_coeff_mem B hB (vacPos ρ) hpos (vacWt ρ) hnn s
  suffices H : ∀ d : ℕ, (∀ s, (firstVar B ρ).coeff s ∈ letterField (M₀ + d)) →
      ∀ s, (firstVar B ρ).coeff s ∈ letterField M₀ by
    refine H (span B) fun s => letterField_mono (by omega) (hbase s)
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    exact ih (firstVar_ceiling_step K B hK hB hKc hBc ρ hρ h1 h2 M₀ hP (M₀ + d) (by omega) h)

end Step

end SkewCoframeRigidity.UnitRestoration
