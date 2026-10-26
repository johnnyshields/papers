/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadFinal

/-!
# The surviving derivative of the top equation (block case)

`block_survive_coherent` and `block_survive_proof`: for the first block with nonzero restricted
weights, the `h_t`-derivative of `[HQ]_m = 0` gives `∑ ρ_x · survive(x) = 0`.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Polynomial Matrix

theorem coeff_series_mul_pulseSum {μ n : ℕ} (U : ℕ → CohField) (I S : Fin n → ℕ)
    (bpos : Fin μ → ℕ) (P ρ : Fin μ → CohField) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk U * (pulseSum U I S bpos P ρ : PowerSeries CohField)) =
      ∑ v, ρ v * (-(P v) * (letterOf U ((k : ℤ) - bpos v) -
        ∑ s, ((properMat U I S)⁻¹ *ᵥ vacancyVec U I (bpos v)) s *
          letterOf U ((k : ℤ) - S s))) := by
  unfold pulseSum
  rw [show ((∑ v, Polynomial.C (ρ v) * pulse U I S (P v) (bpos v) : CohField[X]) :
      PowerSeries CohField) = ∑ v, ((Polynomial.C (ρ v) * pulse U I S (P v) (bpos v) :
      CohField[X]) : PowerSeries CohField) from
    map_sum (Polynomial.coeToPowerSeries.ringHom (R := CohField)) _ _, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul,
    coeff_series_mul_pulse]


section Main

variable {k n : ℕ}

/-- `A` is invertible over the raw field. -/
theorem leadMatOf_det_ne_zero (B : BetaDiagram (n + 1)) (hBc : B.Connected) {p e : ℕ}
    (hpe : p + e + 1 ≤ n)
    (hq : ∀ hq : p + e + 1 < n, B.row ⟨p + e + 2, by omega⟩ < B.col ⟨p + e, by omega⟩) :
    (leadMatOf B hpe cohLetters).det ≠ 0 := by
  classical
  have hT := properDet_cohLetters_ne_zero hBc
  intro h0
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  obtain ⟨h1, h2⟩ := mulVec_extZero (leadEmb_injective hpe) (leadEmb_range hpe)
    (properMatrixOf cohLetters B) (fun i j hi hj => properMatrix_cut_q B cohLetters hq i j hi hj) y
  have hz : properMatrixOf cohLetters B *ᵥ extZero (leadEmb hpe) y = 0 := by
    funext i
    by_cases hi : i.val < p + e + 1
    · obtain ⟨a, rfl⟩ := (leadEmb_range hpe i).mp hi
      rw [h1, ← leadMatOf_eq_submatrix, hy]; rfl
    · rw [h2 i (by omega)]; rfl
  have := Matrix.eq_zero_of_mulVec_eq_zero hT hz
  apply hy0
  funext a
  have := congrFun this (leadEmb hpe a)
  rwa [extZero_apply (leadEmb_injective hpe)] at this


theorem adjugate_eq_det_smul_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]
    (A : Matrix ι ι F) (h : A.det ≠ 0) : A.adjugate = A.det • A⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ h, one_smul]

/-- **The coherent surviving derivative.** -/
theorem block_coherent (K : BetaDiagram (k + 1)) (B : BetaDiagram (n + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (p e : ℕ) (hpe : p + e + 1 ≤ n)
    (hcut : PrefixCut B p (by omega))
    (hq : ∀ hq : p + e + 1 < n, B.row ⟨p + e + 2, by omega⟩ < B.col ⟨p + e, by omega⟩)
    (hρt : ∀ x ∈ ρ.support, x < blockHead B hpe) :
    ∑ x ∈ ρ.support, algebraMap (MvPolynomial ℕ ℚ) CohField (MvPolynomial.C (ρ x)) *
      surviveOf B hpe cohLetters x = 0 := by
  classical
  obtain ⟨hpos, hinj, hS⟩ := firstVar_hyps B hB ρ hρ
  have hnn : ∀ x ∈ ρ.support, 0 ≤ x := fun x hx => (hρ x hx).1.le
  have h0 : B.col (Fin.last n) = 0 := hB
  have hA := leadMatOf_det_ne_zero B hBc hpe hq
  have hcolpos : ∀ j : Fin (n + 1), 0 ≤ B.col j := col_nonneg B hB
  have hhead : 0 < blockHead B hpe := by
    have := B.row_nonempty ⟨p + 1, by omega⟩
    have := hcolpos ⟨p + 1, by omega⟩
    unfold blockHead; omega
  set t : ℕ := (blockHead B hpe).toNat with htdef
  have ht : (t : ℤ) = B.row ⟨p + 1, by omega⟩ := by
    rw [htdef, Int.toNat_of_nonneg hhead.le]; rfl
  have hv : 0 < span K := by
    rw [span_eq_of_norm K hK]; have := top_pos K hK; omega
  have hspanB : (span B : ℤ) = B.row 0 := by
    have := span_cast B
    unfold BetaDiagram.largestLabel at this
    rw [h0, sub_zero] at this; exact this
  have htm : (t : ℤ) < span B := by
    rw [hspanB, ht]
    exact B.row_strictAnti (show (0 : Fin (n + 1)) < ⟨p + 1, by omega⟩ from by
      rw [Fin.lt_def]; simp)
  -- facts about the weighted vacancies
  have hbt : ∀ v, (vacPos ρ v : ℤ) < t := by
    intro v
    have hx := hρt _ (ρ.support.equivFin.symm v).2
    have hx0 := hnn _ (ρ.support.equivFin.symm v).2
    unfold vacPos; omega
  have hbp : ∀ v, ∀ j : Fin n, j.val < p → (vacPos ρ v : ℤ) < B.col j.castSucc := by
    intro v j hj
    have hp : 0 < p := by omega
    have h1' := hcut hp
    have h3 : B.col ⟨p - 1, by omega⟩ ≤ B.col j.castSucc :=
      B.col_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_castSucc]; omega)
    have := hbt v
    have e1 : (t : ℤ) = B.row ⟨p + 1, by omega⟩ := ht
    omega
  -- the numerator coefficients and the ceiling
  have hP : ∀ v, PowerSeries.coeff (vacPos ρ v) (letterSeries *
      (coframe B : PowerSeries CohField)) ∈ letterField (t + 1) := by
    intro v
    refine numerator_coeff_mem_lower B (by omega) hB hBc hcut (t + 1) ?_ (vacPos ρ v) ?_ (hbp v)
    · intro i hi
      have : B.row i.succ ≤ B.row ⟨p + 1, by omega⟩ :=
        B.row_strictAnti.antitone (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_succ]; omega)
      omega
    · have := hbt v; omega
  have hQ := firstVar_ceiling K B hK hB hKc hBc ρ hρ h1 h2 (t + 1) hP
  have hT : (properMat cohLetters (rowPos B) (colPos B)).det ≠ 0 := by
    rw [properMat_eq]; exact properDet_cohLetters_ne_zero hBc
  have hspec := pulseSum_spec cohLetters (rowPos B) (colPos B) hT (vacPos ρ)
    (fun v => PowerSeries.coeff (vacPos ρ v) (letterSeries * (coframe B : PowerSeries CohField)))
    (vacWt ρ) (colPos_pos B) (fun v => (hpos v).1) hinj hS
  obtain ⟨hobs1, hobs2⟩ := firstVar_observations K B hK hB hKc hBc ρ hρ h1 h2
  have hzr : ∀ j, j + max t (span K - 1) < span B + span K → (firstVar B ρ).coeff j = 0 :=
    fun j hj => firstVar_zero_range K B hK hB hKc hBc ρ hρ h1 h2 t hQ j hj
  -- the derivative of the first variation
  have hrows : ∀ i, PowerSeries.coeff (rowPos B i) (letterSeries *
      (dPoly t (firstVar B ρ) : PowerSeries CohField)) = 0 := by
    intro i
    have key := coeff_letterSeries_mul_dPoly t (firstVar B ρ) (rowPos B i)
    have hmain : PowerSeries.coeff (rowPos B i) (letterSeries *
        (firstVar B ρ : PowerSeries CohField)) = 0 := hspec.2.1 i
    rw [hmain, dRaw_zero] at key
    rw [key]
    split_ifs with hle
    · rw [hzr (rowPos B i - t) (by have := rowPos_lt_span B i; omega)]; simp
    · simp
  have htop : PowerSeries.coeff (span B) (letterSeries *
      (dPoly t (firstVar B ρ) : PowerSeries CohField)) = 0 := by
    have key := coeff_letterSeries_mul_dPoly t (firstVar B ρ) (span B)
    rw [hobs1, dRaw_zero] at key
    rw [key, if_pos (by omega), hzr (span B - t) (by omega)]; simp
  -- `dPoly t Q` is the pulse tangent with numerator derivatives
  set P' : Fin ρ.support.card → CohField := fun v => dRaw t (PowerSeries.coeff (vacPos ρ v)
    (letterSeries * (coframe B : PowerSeries CohField))) with hP'
  have hspec' := pulseSum_spec cohLetters (rowPos B) (colPos B) hT (vacPos ρ) P' (vacWt ρ)
    (colPos_pos B) (fun v => (hpos v).1) hinj hS
  have hDQ : dPoly t (firstVar B ρ) =
      pulseSum cohLetters (rowPos B) (colPos B) (vacPos ρ) P' (vacWt ρ) := by
    have hR : dPoly t (firstVar B ρ) - pulseSum cohLetters (rowPos B) (colPos B) (vacPos ρ) P'
        (vacWt ρ) = 0 := by
      refine pulse_tangent_unique cohLetters (rowPos B) (colPos B) hT (colPos_injective B hB)
        (vacPos ρ) _ ?_ ?_ ?_
      · intro j hj
        by_contra hno
        push Not at hno
        apply hj
        rw [Polynomial.coeff_sub, coeff_dPoly]
        have e1 : (firstVar B ρ).coeff j = 0 := by
          unfold firstVar
          exact pulseSum_coeff_eq_zero _ _ _ _ _ _ j (fun v => hno.2 v) (fun s => hno.1 s)
        rw [e1, dRaw_zero, pulseSum_coeff_eq_zero _ _ _ _ _ _ j (fun v => hno.2 v)
          (fun s => hno.1 s), sub_zero]
      · intro v
        rw [Polynomial.coeff_sub, coeff_dPoly, hspec'.2.2 v]
        have hv1 : (firstVar B ρ).coeff (vacPos ρ v) = -(vacWt ρ v * PowerSeries.coeff (vacPos ρ v)
            (letterSeries * (coframe B : PowerSeries CohField))) := hspec.2.2 v
        rw [hv1, dRaw_neg, dRaw_mul, dRaw_eq_zero_of_mem_letterField t (vacWt_mem ρ t v)]
        simp only [hP']
        ring
      · intro i
        have e : (letterSeries * ((dPoly t (firstVar B ρ) - pulseSum cohLetters (rowPos B)
            (colPos B) (vacPos ρ) P' (vacWt ρ) : CohField[X]) : PowerSeries CohField)) =
            letterSeries * (dPoly t (firstVar B ρ) : PowerSeries CohField) -
            letterSeries * (pulseSum cohLetters (rowPos B) (colPos B) (vacPos ρ) P' (vacWt ρ) :
              PowerSeries CohField) := by
          rw [Polynomial.coe_sub, mul_sub]
        show PowerSeries.coeff (rowPos B i) (PowerSeries.mk cohLetters * _) = 0
        change PowerSeries.coeff (rowPos B i) (letterSeries * _) = 0
        rw [e, map_sub, hrows i]
        have := hspec'.2.1 i
        rw [show PowerSeries.coeff (rowPos B i) (letterSeries * (pulseSum cohLetters (rowPos B)
          (colPos B) (vacPos ρ) P' (vacWt ρ) : PowerSeries CohField)) = 0 from this]
        simp
    exact sub_eq_zero.mp hR
  have htop' : PowerSeries.coeff (span B) (letterSeries * (pulseSum cohLetters (rowPos B)
      (colPos B) (vacPos ρ) P' (vacWt ρ) : PowerSeries CohField)) = 0 := by
    rw [← hDQ]; exact htop
  have hexp := coeff_series_mul_pulseSum cohLetters (rowPos B) (colPos B) (vacPos ρ) P'
    (vacWt ρ) (span B)
  rw [show PowerSeries.mk cohLetters = letterSeries from rfl, htop'] at hexp
  set D := (leadMatOf B hpe cohLetters).det with hD
  set A := leadMatOf B hpe cohLetters with hAdef
  have hleadcol : ∀ a : Fin p ⊕ Fin (e + 1), B.col ⟨p + e, by omega⟩ ≤ leadCol B hpe a := by
    intro a
    refine B.col_strictAnti.antitone ?_
    rw [Fin.le_iff_val_le_val]
    have := leadIdx_lt hpe a
    rcases a with i | i
    · simp only [leadIdx, Sum.elim_inl]; have := i.isLt; omega
    · simp only [leadIdx, Sum.elim_inr]; have := i.isLt; omega
  have hterm : ∀ v, vacWt ρ v * surviveOf B hpe cohLetters (vacPos ρ v : ℤ) =
      D ^ 2 * (vacWt ρ v * (-(P' v) * (letterOf cohLetters ((span B : ℤ) - vacPos ρ v) -
        ∑ s, ((properMat cohLetters (rowPos B) (colPos B))⁻¹ *ᵥ
          vacancyVec cohLetters (rowPos B) (vacPos ρ v)) s *
          letterOf cohLetters ((span B : ℤ) - colPos B s)))) := by
    intro v
    have hxv := ρ.support.equivFin.symm v
    have hvac := hρ _ (ρ.support.equivFin.symm v).2
    set x : ℤ := ((ρ.support.equivFin.symm v : ρ.support) : ℤ) with hx
    have hxb : (vacPos ρ v : ℤ) = x := by
      unfold vacPos; rw [← hx]; exact Int.toNat_of_nonneg (hvac.1.le)
    have hdP := dP_formula B hB hBc hpe hcut hq t ht hA (vacPos ρ v) (hbt v) (hbp v)
    have hP'v : P' v = -(wOf B hpe cohLetters (vacPos ρ v : ℤ) ⬝ᵥ (A⁻¹ *ᵥ Pi.single pivot 1)) :=
      hdP
    rcases lt_or_gt_of_ne (show x ≠ B.col ⟨p + e, by omega⟩ from fun h' => hvac.2.2.2 _ h'.symm)
      with hlt | hgt
    · have hw : wOf B hpe cohLetters (vacPos ρ v : ℤ) = 0 := by
        funext a
        simp only [wOf, Pi.zero_apply]
        exact letterOf_of_neg _ (by have := hleadcol a; omega)
      have hsv : surviveOf B hpe cohLetters (vacPos ρ v : ℤ) = 0 := by
        unfold surviveOf; rw [hw]; simp
      rw [hsv, hP'v, hw]; simp
    · have hW := pulse_factor B hB hBc hpe hq hA (vacPos ρ v) (by
        intro i hi
        have hn : p + e + 1 < n := by have := i.isLt; omega
        have h1' := hq hn
        have h2' : B.row i.succ ≤ B.row ⟨p + e + 2, by omega⟩ :=
          B.row_strictAnti.antitone (by
            rw [Fin.le_iff_val_le_val]; simp only [Fin.val_succ]; omega)
        omega)
      rw [hW, hP'v, hxb]
      unfold surviveOf
      rw [adjugate_eq_det_smul_inv A hA]
      simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← hD]
      ring
  have hsum : ∑ x ∈ ρ.support, algebraMap (MvPolynomial ℕ ℚ) CohField (MvPolynomial.C (ρ x)) *
      surviveOf B hpe cohLetters x = ∑ v, vacWt ρ v * surviveOf B hpe cohLetters (vacPos ρ v : ℤ) := by
    rw [← Finset.sum_coe_sort ρ.support]
    refine Fintype.sum_equiv ρ.support.equivFin _ _ (fun x => ?_)
    have hx0 := hnn x.1 x.2
    simp only [vacWt, vacPos, Equiv.symm_apply_apply, Int.toNat_of_nonneg hx0]
  rw [hsum, Finset.sum_congr rfl fun v _ => hterm v, ← Finset.mul_sum, ← hexp, mul_zero]


/-- **The surviving derivative at the physical unit** (`block_survive`). -/
theorem block_survive_proof (K : BetaDiagram (k + 1)) (B : BetaDiagram (n + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (h1 : dotW B ρ = 0)
    (h2 : dotW (splice K B hK hB) ρ = 0) (p e : ℕ) (hpe : p + e + 1 ≤ n)
    (hcut : PrefixCut B p (by omega))
    (hq : ∀ hq : p + e + 1 < n, B.row ⟨p + e + 2, by omega⟩ < B.col ⟨p + e, by omega⟩)
    (hρt : ∀ x ∈ ρ.support, x < blockHead B hpe) :
    (ρ.sum fun x r => MvPolynomial.C r * survive B hpe x) = 0 := by
  have hcoh := block_coherent K B hK hB hKc hBc ρ hρ h1 h2 p e hpe hcut hq hρt
  set X' : ℕ → MvPolynomial ℕ ℚ := fun k => MvPolynomial.X k with hX'
  set Pσ : MvPolynomial ℕ ℚ := ∑ x ∈ ρ.support, MvPolynomial.C (ρ x) * surviveOf B hpe X' x
    with hPσ
  have hmap : algebraMap (MvPolynomial ℕ ℚ) CohField Pσ = 0 := by
    rw [hPσ, map_sum, ← hcoh]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, map_surviveOf B hpe (algebraMap (MvPolynomial ℕ ℚ) CohField) X' x]
    rfl
  have h0 : Pσ = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ℕ ℚ) CohField)).mp hmap
  have h1' := congrArg deh h0
  rw [hPσ, map_sum, map_zero] at h1'
  rw [← h1']
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun x _ => ?_
  show MvPolynomial.C (ρ x) * survive B hpe x = _
  rw [map_mul, map_surviveOf B hpe deh X' x, survive_eq_surviveOf]
  simp only [hX', deh_X]
  congr 1
  simp [deh]

end Main

end SkewCoframeRigidity.UnitRestoration
