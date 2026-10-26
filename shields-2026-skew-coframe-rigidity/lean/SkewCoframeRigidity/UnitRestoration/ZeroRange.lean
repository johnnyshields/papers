/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.Variation
import SkewCoframeRigidity.FixedCap.StageOne
import SkewCoframeRigidity.Coframe.Coherent

/-!
# The linearized observations and the zero range

Formalizes the two displayed consequences of `ṡ_B = 0` and `ṡ_{K ◁ B} = 0` in the proof of
`sc:linearized-cap` in `shields-2026-skew-coframe-rigidity.tex` (`sc:linearized-observations`,
`sc:linearized-zero-range`), over the raw field of the coherent letters.

For a connected normalized diagram `B` of span `m` with first variation
`Q = ∑_b ρ_b δ^{(b)}` of its coframe, the top-letter coefficient of `ṡ_B = 0` gives `κ̇ = 0`, and
what remains gives `[HQ]_m = 0` (`linearized_top`).  With `ṡ_{K ◁ B} = 0` the differentiated
splice identity then gives `[H C_K Q]_{m+v} = 0` (`linearized_observations`).  Comparing the
high-letter coefficients of the second equation shows `Q_j = 0` for
`j < m + v - max(R, v - 1)`, `R` the raw ceiling of `Q` (`linearized_zero_range`).  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.FixedCap Polynomial Matrix
open scoped Polynomial Matrix

theorem letterField_mono {m m' : ℕ} (h : m ≤ m') : letterField m ≤ letterField m' :=
  Subfield.closure_mono (Set.image_mono fun _ hx => lt_of_lt_of_le hx h)

section ZeroRange

variable {k : ℕ}

/-- **The zero range** (`sc:linearized-zero-range`, in the form of `prefix_zero`): if the
coefficients of `Q` use only letters below `M`, `M` is at least the span of `K`, and
`[z^N] H C_K Q = 0` with `M ≤ N`, then `Q_i = 0` for `i + M ≤ N`. -/
theorem zero_range (K : BetaDiagram (k + 1)) (hK : IsNorm K) (Q : CohField[X]) (M N : ℕ)
    (hKM : K.row 0 ≤ M) (hQ : ∀ s, Q.coeff s ∈ letterField M) (hMN : M ≤ N)
    (hO : PowerSeries.coeff N (letterSeries *
      ((leftCoframe K * Q : CohField[X]) : PowerSeries CohField)) = 0)
    (i : ℕ) (hi : i + M ≤ N) : Q.coeff i = 0 := by
  set V : CohField[X] := leftCoframe K * Q with hV
  have hVm : ∀ s, V.coeff s ∈ letterField M := fun s => by
    rw [hV, Polynomial.coeff_mul]
    exact Subfield.sum_mem _ fun p _ => Subfield.mul_mem _
      (leftCoframe_coeff_mem K hK hKM _) (hQ _)
  have hsum : PowerSeries.coeff N (letterSeries * (V : PowerSeries CohField)) =
      ∑ j ∈ Finset.range M, cohLetters j * V.coeff (N - j) +
        ∑ j ∈ Finset.Icc M N, cohLetters j * V.coeff (N - j) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Finset.sum_range_add_sum_Ico _ (show M ≤ N + 1 by omega)]
    have : Finset.Ico M (N + 1) = Finset.Icc M N := by ext; simp
    rw [this]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>
      simp [letterSeries, seriesOf, Polynomial.coeff_coe]
  have hind := tail_letters_independent M N (fun j => V.coeff (N - j))
    (∑ j ∈ Finset.range M, cohLetters j * V.coeff (N - j)) (fun j => hVm _)
    (Subfield.sum_mem _ fun j hj => Subfield.mul_mem _
      (cohLetters_mem_letterField (Finset.mem_range.1 hj)) (hVm _))
    (by rw [← hsum]; exact hO)
  have hVz : ∀ t, t + M ≤ N → V.coeff t = 0 := by
    intro t ht
    have := hind.2 (N - t) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    simpa [show N - (N - t) = t by omega] using this
  have hunit : IsUnit (leftCoframe K : PowerSeries CohField) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : PowerSeries.constantCoeff (leftCoframe K : PowerSeries CohField) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        leftCoframe_coeff_zero]
    rw [this]; exact isUnit_one
  have hdvd : (PowerSeries.X : PowerSeries CohField) ^ (N - M + 1) ∣
      (Q : PowerSeries CohField) := by
    have h1 : (PowerSeries.X : PowerSeries CohField) ^ (N - M + 1) ∣
        (V : PowerSeries CohField) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro t ht
      rw [Polynomial.coeff_coe]
      exact hVz t (by omega)
    rw [hV, Polynomial.coe_mul] at h1
    exact (hunit.dvd_mul_left).1 h1
  rw [PowerSeries.X_pow_dvd_iff] at hdvd
  have := hdvd i (by omega)
  rwa [Polynomial.coeff_coe] at this

/-- **The zero range** (`sc:linearized-zero-range`).  If every coefficient of `Q` uses letters of
index at most `R` and `[z^{m+v}] H C_K Q = 0`, with `v` the span of `K`, then
`Q_j = 0` for `j < m + v - max(R, v - 1)`. -/
theorem linearized_zero_range (K : BetaDiagram (k + 1)) (hK : IsNorm K) (Q : CohField[X])
    (m R : ℕ) (hQ : ∀ s, Q.coeff s ∈ letterField (R + 1))
    (hO : PowerSeries.coeff (m + span K) (letterSeries *
      ((leftCoframe K * Q : CohField[X]) : PowerSeries CohField)) = 0)
    (j : ℕ) (hj : j + max R (span K - 1) < m + span K) : Q.coeff j = 0 := by
  have hv : 0 < span K := by
    rw [span_eq_of_norm K hK]
    have := top_pos K hK
    omega
  have hKM : K.row 0 ≤ ((max (R + 1) (span K) : ℕ) : ℤ) := by
    have := span_eq_of_norm K hK
    have h1 := top_pos K hK
    have : ((span K : ℕ) : ℤ) = K.row 0 := by omega
    omega
  have hM : max (R + 1) (span K) = max R (span K - 1) + 1 := by omega
  refine zero_range K hK Q (max (R + 1) (span K)) (m + span K) hKM
    (fun s => letterField_mono (le_max_left _ _) (hQ s)) (by omega) hO j (by omega)

end ZeroRange

section Top

theorem mulVec_mem_subfield {K : Type*} [Field K] (S : Subfield K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (hA : ∀ i j, A i j ∈ S) (hv : ∀ j, v j ∈ S)
    (j : Fin n) : (A *ᵥ v) j ∈ S := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subfield.sum_mem _ fun i _ => S.mul_mem (hA j i) (hv i)

variable {n : ℕ}

private theorem rowlt {D : BetaDiagram (n + 1)} (hD : IsNorm D) (i : Fin n) :
    D.row i.succ < (span D : ℤ) := by
  have := span_cast D
  have h1 : D.row i.succ < D.row 0 := D.row_strictAnti (Fin.succ_pos i)
  have h0 : D.col (Fin.last n) = 0 := hD
  unfold BetaDiagram.largestLabel at this
  omega

/-- The coefficients of the first variation of the coframe use only the letters below the span. -/
theorem pulseSum_coeff_mem {μ : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D) (bpos : Fin μ → ℕ)
    (hbpos : ∀ v, 0 < bpos v ∧ bpos v < span D) (ρ : Fin μ → CohField)
    (hρ : ∀ v, ρ v ∈ letterField (span D)) (s : ℕ) :
    (pulseSum cohLetters (rowPos D) (colPos D) bpos (fun v => PowerSeries.coeff (bpos v)
      (letterSeries * (coframe D : PowerSeries CohField))) ρ).coeff s ∈ letterField (span D) := by
  have h0 : D.col (Fin.last n) = 0 := hD
  have hTm : ∀ i j, properMatrixOf cohLetters D i j ∈ letterField (span D) :=
    properMatrix_mem D hD (fun i => rowlt hD i)
  have hvm : ∀ (b : ℕ) (i : Fin n), letterOf cohLetters (D.row i.succ - b) ∈ letterField (span D) :=
    fun b i => letterOf_mem (by have := rowlt hD i; omega)
  have hym : ∀ (b : ℕ) (j : Fin n),
      ((properMatrixOf cohLetters D)⁻¹ *ᵥ fun i : Fin n => letterOf cohLetters (D.row i.succ - b))
        j ∈ letterField (span D) := fun b j =>
    mulVec_mem_subfield _ _ _ (inv_entry_mem_subfield _ _ hTm) (hvm b) j
  have hgm : ∀ j, coframeVecOf cohLetters D j ∈ letterField (span D) := fun j => by
    simp only [coframeVecOf, Pi.neg_apply]
    exact Subfield.neg_mem _ (mulVec_mem_subfield _ _ _ (inv_entry_mem_subfield _ _ hTm)
      (topVec_mem D hD (fun i => rowlt hD i)) j)
  have hite : ∀ (p : Prop) [Decidable p], (if p then (1 : CohField) else 0) ∈
      letterField (span D) := fun p _ => by
    split_ifs
    · exact Subfield.one_mem _
    · exact Subfield.zero_mem _
  have hP : ∀ v, PowerSeries.coeff (bpos v) (letterSeries *
      (coframe D : PowerSeries CohField)) ∈ letterField (span D) := fun v => by
    have hb := hbpos v
    rw [show letterSeries = PowerSeries.mk cohLetters from rfl]
    unfold coframe
    rw [coeff_coframe_vac cohLetters D hD (bpos v)]
    refine Subfield.add_mem _ (letterOf_mem (by omega)) ?_
    refine Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (letterOf_mem ?_) (hgm j)
    have := col_nonneg D hD j.castSucc
    have := hb.2
    omega
  unfold pulseSum
  rw [Polynomial.finsetSum_coeff]
  refine Subfield.sum_mem _ fun v _ => ?_
  rw [Polynomial.coeff_C_mul, coeff_pulse, properMat_eq, vacancyVec_eq cohLetters D hD]
  refine Subfield.mul_mem _ (hρ v) (Subfield.mul_mem _ (Subfield.neg_mem _ (hP v)) ?_)
  exact Subfield.sub_mem _ (hite _) (Subfield.sum_mem _ fun j _ =>
    Subfield.mul_mem _ (hym _ j) (hite _))

theorem cornerOf_mem {m : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hm : ∀ i : Fin n, D.row i.succ < m) : cornerOf cohLetters D ∈ letterField m := by
  unfold cornerOf
  refine Subfield.mul_mem _ ?_ (det_mem_subfield _ _ (properMatrix_mem D hD hm))
  exact Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _

theorem cornerDot_mem {m : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hT : (properMatrixOf cohLetters D).det ≠ 0) (hm : ∀ i : Fin n, D.row i.succ < m) (b : ℕ)
    (hb : b < m) : cornerDot cohLetters D b ∈ letterField m := by
  have h0 : D.col (Fin.last n) = 0 := hD
  have hTm := properMatrix_mem D hD hm
  have hy := mulVec_mem_subfield _ _ (fun i : Fin n => letterOf cohLetters (D.row i.succ - b))
    (inv_entry_mem_subfield _ _ hTm) (fun i => letterOf_mem (by have := hm i; omega))
  rw [cornerDot_eq cohLetters D b
    ((properMatrixOf cohLetters D)⁻¹ *ᵥ fun i : Fin n => letterOf cohLetters (D.row i.succ - b)) (by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT),
      Matrix.one_mulVec])]
  refine Subfield.mul_mem _ (cornerOf_mem D hD hm) (Subfield.neg_mem _ ?_)
  unfold dotProduct
  refine Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (letterOf_mem ?_) (hy j)
  have := col_nonneg D hD j.castSucc
  omega

theorem topQuotient_decomp (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hm : ∀ i : Fin n, D.row i.succ < span D) :
    ∃ r ∈ letterField (span D), topQuotientOf cohLetters D = cohLetters (span D) + r := by
  have h0 : D.col (Fin.last n) = 0 := hD
  have hTm := properMatrix_mem D hD hm
  have hg : ∀ j, coframeVecOf cohLetters D j ∈ letterField (span D) := fun j => by
    simp only [coframeVecOf, Pi.neg_apply]
    exact Subfield.neg_mem _ (mulVec_mem_subfield _ _ _ (inv_entry_mem_subfield _ _ hTm)
      (topVec_mem D hD hm) j)
  refine ⟨∑ j, coframeVecOf cohLetters D j *
    letterOf cohLetters (D.row 0 - D.col j.castSucc), ?_, ?_⟩
  · refine Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (hg j) (letterOf_mem ?_)
    have := col_pos_of_ne_last D hD j.castSucc (Fin.castSucc_lt_last j).ne
    have := span_cast D
    unfold BetaDiagram.largestLabel at this
    omega
  · unfold topQuotientOf seriesOf
    rw [coframeOf_eq_uniPoly, coeff_span, ← letterOf_natCast cohLetters (span D), span_cast D]

theorem cornerOf_ne_zero (D : BetaDiagram (n + 1)) (hT : (properMatrixOf cohLetters D).det ≠ 0) :
    cornerOf cohLetters D ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hT

theorem span_row_lt (D : BetaDiagram (n + 1)) (hD : IsNorm D) (i : Fin n) :
    D.row i.succ < span D := by
  have := rowlt hD i
  omega

/-- The top coefficient of a product with a series vanishing at `0`, with coefficients below the
ceiling, lies in the field of the letters below it. -/
theorem coeff_top_mem {m : ℕ} (Q : CohField[X]) (hQ : ∀ s, Q.coeff s ∈ letterField m)
    (h0 : Q.coeff 0 = 0) :
    PowerSeries.coeff m (letterSeries * (Q : PowerSeries CohField)) ∈ letterField m := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  refine Subfield.add_mem _ (Subfield.sum_mem _ fun j hj => ?_) ?_
  · refine Subfield.mul_mem _ ?_ ?_
    · simpa [letterSeries, seriesOf] using cohLetters_mem_letterField (Finset.mem_range.1 hj)
    · simpa [Polynomial.coeff_coe] using hQ _
  · simp [Polynomial.coeff_coe, h0]

/-- **The differentiated top equation** (`sc:linearized-observations`, first line).  If the whole
equation `ṡ_B = ∑_b ρ_b ṡ^{(b)}_B = 0` holds over the raw field, with weights in the field of the
letters below the span, then `κ̇ = 0` and `[H Q]_m = 0` for the first variation
`Q = ∑_b ρ_b δ^{(b)}` of the coframe.  The top letter `h_m` enters `[HG]_m` linearly and nothing
else in the equation. -/
theorem linearized_top {μ : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hT : (properMatrixOf cohLetters D).det ≠ 0) (bpos : Fin μ → ℕ)
    (hbpos : ∀ v, 0 < bpos v ∧ bpos v < span D) (hbinj : Function.Injective bpos)
    (hbS : ∀ v j, bpos v ≠ colPos D j) (ρ : Fin μ → CohField)
    (hρ : ∀ v, ρ v ∈ letterField (span D))
    (hdot : ∑ v, ρ v * restorationPoly cohLetters D (bpos v) = 0) :
    ∑ v, ρ v * cornerDot cohLetters D (bpos v) = 0 ∧
      PowerSeries.coeff (span D) (letterSeries * (pulseSum cohLetters (rowPos D) (colPos D) bpos
        (fun v => PowerSeries.coeff (bpos v) (letterSeries * (coframe D : PowerSeries CohField)))
        ρ : PowerSeries CohField)) = 0 := by
  set Q := pulseSum cohLetters (rowPos D) (colPos D) bpos
    (fun v => PowerSeries.coeff (bpos v) (letterSeries * (coframe D : PowerSeries CohField))) ρ
    with hQ
  have hrow := span_row_lt D hD
  have hspec := pulseSum_spec cohLetters (rowPos D) (colPos D)
    (by rw [properMat_eq]; exact hT) bpos
    (fun v => PowerSeries.coeff (bpos v) (letterSeries * (coframe D : PowerSeries CohField))) ρ
    (colPos_pos D) (fun v => (hbpos v).1) hbinj hbS
  have hQm : ∀ s, Q.coeff s ∈ letterField (span D) := fun s =>
    pulseSum_coeff_mem D hD bpos hbpos ρ hρ s
  have hB := coeff_top_mem Q hQm hspec.1
  have hA : ∑ v, ρ v * cornerDot cohLetters D (bpos v) ∈ letterField (span D) :=
    Subfield.sum_mem _ fun v _ => Subfield.mul_mem _ (hρ v)
      (cornerDot_mem D hD hT (span_row_lt D hD) _ (hbpos v).2)
  have hκ := cornerOf_mem D hD (span_row_lt D hD)
  obtain ⟨r, hr, hqt⟩ := topQuotient_decomp D hD (span_row_lt D hD)
  have heq := restorationSum_eq cohLetters D hD hT bpos ρ
  rw [hdot, hqt] at heq
  set A := ∑ v, ρ v * cornerDot cohLetters D (bpos v) with hAdef
  have heq' : A * (cohLetters (span D) + r) + cornerOf cohLetters D *
      PowerSeries.coeff (span D) (letterSeries * (Q : PowerSeries CohField)) = 0 := heq.symm
  have hind := tail_letters_independent (span D) (span D) (fun _ => A)
    (A * r + cornerOf cohLetters D *
      PowerSeries.coeff (span D) (letterSeries * (Q : PowerSeries CohField)))
    (fun _ => hA)
    (Subfield.add_mem _ (Subfield.mul_mem _ hA hr) (Subfield.mul_mem _ hκ hB))
    (by
      rw [Finset.Icc_self, Finset.sum_singleton]
      linear_combination heq')
  have h1 : A = 0 := hind.2 (span D) (by simp)
  refine ⟨h1, ?_⟩
  have h2 := hind.1
  rw [h1, zero_mul, zero_add] at h2
  exact (mul_eq_zero.1 h2).resolve_left (cornerOf_ne_zero D hT)

end Top

section Observations

variable {k b μ : ℕ}

/-- **The linearized observations** (`sc:linearized-observations`).  For connected normalized `K`
and `B`, weights `ρ` in the field of the letters below `span B` on vacancies `bpos` of `B`, the
whole identities `ṡ_B = 0` and `ṡ_{K ◁ B} = 0` give
`[H Q]_{span B} = 0` and `[H C_K Q]_{span B + span K} = 0`, where `Q = ∑_β ρ_β δ^{(β)}` is the
first variation of the complete right coframe of `B`. -/
theorem linearized_observations (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected)
    (bpos : Fin μ → ℕ) (hbpos : ∀ v, 0 < bpos v ∧ bpos v < span B)
    (hbinj : Function.Injective bpos) (hbS : ∀ v j, bpos v ≠ colPos B j)
    (ρ : Fin μ → CohField) (hρ : ∀ v, ρ v ∈ letterField (span B))
    (h1 : ∑ v, ρ v * restorationPoly cohLetters B (bpos v) = 0)
    (h2 : ∑ v, ρ v * restorationPoly cohLetters (splice K B hK hB) (bpos v) = 0) :
    PowerSeries.coeff (span B) (letterSeries * (pulseSum cohLetters (rowPos B) (colPos B) bpos
        (fun v => PowerSeries.coeff (bpos v) (letterSeries * (coframe B : PowerSeries CohField)))
        ρ : PowerSeries CohField)) = 0 ∧
    PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * pulseSum cohLetters (rowPos B) (colPos B) bpos
        (fun v => PowerSeries.coeff (bpos v) (letterSeries * (coframe B : PowerSeries CohField)))
        ρ : CohField[X]) : PowerSeries CohField)) = 0 := by
  have hBt := properDet_cohLetters_ne_zero hBc
  have hKt := properDet_cohLetters_ne_zero hKc
  obtain ⟨hA, hq1⟩ := linearized_top B hB hBt bpos hbpos hbinj hbS ρ hρ h1
  refine ⟨hq1, ?_⟩
  have hbr : ∀ v, ((bpos v : ℕ) : ℤ) < B.row 0 := fun v => by
    have := (hbpos v).2
    have e : ((span B : ℕ) : ℤ) = B.row 0 := by
      have := span_eq_of_norm B hB
      have := top_pos B hB
      omega
    omega
  have key := splice_restorationSum_eq cohLetters K B hK hB hKt hBt bpos hbr ρ
  rw [h2, hA, zero_mul, zero_add] at key
  have hκK := cornerOf_ne_zero K hKt
  have hκB := cornerOf_ne_zero B hBt
  have := (mul_eq_zero.1 key.symm).resolve_left hκK
  exact (mul_eq_zero.1 this).resolve_left hκB

/-- **The zero range for the first variation** (`sc:linearized-zero-range`).  Under the
hypotheses of `linearized_observations`, if every coefficient of `Q` uses letters of index at
most `R`, then `Q_j = 0` for `j < span B + span K - max(R, span K - 1)`. -/
theorem linearized_zero_range_of_observations (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected)
    (bpos : Fin μ → ℕ) (hbpos : ∀ v, 0 < bpos v ∧ bpos v < span B)
    (hbinj : Function.Injective bpos) (hbS : ∀ v j, bpos v ≠ colPos B j)
    (ρ : Fin μ → CohField) (hρ : ∀ v, ρ v ∈ letterField (span B))
    (h1 : ∑ v, ρ v * restorationPoly cohLetters B (bpos v) = 0)
    (h2 : ∑ v, ρ v * restorationPoly cohLetters (splice K B hK hB) (bpos v) = 0) (R : ℕ)
    (hR : ∀ s, (pulseSum cohLetters (rowPos B) (colPos B) bpos
        (fun v => PowerSeries.coeff (bpos v) (letterSeries * (coframe B : PowerSeries CohField)))
        ρ).coeff s ∈ letterField (R + 1))
    (j : ℕ) (hj : j + max R (span K - 1) < span B + span K) :
    (pulseSum cohLetters (rowPos B) (colPos B) bpos
      (fun v => PowerSeries.coeff (bpos v) (letterSeries * (coframe B : PowerSeries CohField)))
      ρ).coeff j = 0 :=
  linearized_zero_range K hK _ (span B) R hR
    (linearized_observations K B hK hB hKc hBc bpos hbpos hbinj hbS ρ hρ h1 h2).2 j hj

end Observations

end SkewCoframeRigidity.UnitRestoration
