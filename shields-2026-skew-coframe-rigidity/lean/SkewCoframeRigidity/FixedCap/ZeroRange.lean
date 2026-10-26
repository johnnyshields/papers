/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.CutSeries
import SkewCoframeRigidity.FixedCap.StageOne
import SkewCoframeRigidity.Coframe.Coprime
import SkewCoframeRigidity.FixedCap.Reduction

/-!
# The descent of the zero range

Formalizes the descent of the raw ceiling in the proof of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex`.  For two connected normalized diagrams with a common
prefix of proper rows and columns cut off at `q`, the derivative of the coframe equations in a
letter `h_L` above every row of the remaining part is controlled by the zero range of the
difference of the two right coframes; the zero range then extends one step down
(`zeroRange_step`).  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem letterField_mono {m m' : ℕ} (h : m ≤ m') : letterField m ≤ letterField m' :=
  Subfield.closure_mono (Set.image_mono (Set.Iio_subset_Iio h))

/-- The coefficients of the right coframe as a series. -/
theorem coeff_coframe_series (D : BetaDiagram (n + 1)) (s : ℕ) :
    PowerSeries.coeff s (coframe D : PowerSeries CohField) = (coframe D).coeff s :=
  Polynomial.coeff_coe _ _

/-- The coframe equations: `[z^x](H G) = 0` at every row position. -/
theorem coeff_rowPos_coframe {D : BetaDiagram (n + 1)} (hD : D.Connected) (i : Fin n) :
    PowerSeries.coeff (rowPos D i) (letterSeries * (coframe D : PowerSeries CohField)) = 0 :=
  coeff_rowPos_eq_zero cohLetters D (coframeVecOf cohLetters D)
    (properMatrix_mulVec_coframeVecOf cohLetters D (properDet_cohLetters_ne_zero hD)) i

/-- The derivative of the right coframe, as a series. -/
noncomputable def dCoframe (L : ℕ) (D : BetaDiagram (n + 1)) : PowerSeries CohField :=
  dSeries L (coframe D : PowerSeries CohField)

theorem suppCols_dCoframe (L : ℕ) (D : BetaDiagram (n + 1)) :
    SuppCols D (fun _ => True) (dCoframe L D) := by
  intro s hs
  rw [dCoframe, coeff_dSeries, coeff_coframe_series]
  by_cases h0 : s = 0
  · subst h0
    rw [coframe_coeff_zero, (letterDeriv_one L)]
  · have : (coframe D).coeff s = 0 := by
      unfold coframe coframeOf
      exact uniPoly_coeff_of_ne _ _ _ (Nat.pos_of_ne_zero h0) fun j => hs j trivial
    rw [this, map_zero]

/-- The equations satisfied by the derivative of the coframe at the row positions. -/
theorem coeff_rowPos_dCoframe {D : BetaDiagram (n + 1)} (hD : D.Connected) (L : ℕ) (i : Fin n) :
    PowerSeries.coeff (rowPos D i) (letterSeries * dCoframe L D) =
      -(if L ≤ rowPos D i then (coframe D).coeff (rowPos D i - L) else 0) := by
  have h := congrArg (letterDeriv L) (coeff_rowPos_coframe hD i)
  rw [map_zero, letterDeriv_coeff_mul, dSeries_letterSeries, PowerSeries.coeff_X_pow_mul'] at h
  split_ifs at h ⊢
  · rw [coeff_coframe_series] at h
    unfold dCoframe
    linear_combination h
  · unfold dCoframe
    linear_combination h

/-- **Trailing coordinates vanish.**  If the trailing row equations of a series on the columns of
`D` vanish, so do its trailing coordinates. -/
theorem trail_zero_coords {D : BetaDiagram (n + 1)} (hD : D.Connected) {q : ℕ} (hq : CutAt D q)
    {U : PowerSeries CohField} (hU : SuppCols D (fun _ => True) U)
    (h : ∀ i : Fin n, q ≤ i.val → PowerSeries.coeff (rowPos D i) (letterSeries * U) = 0)
    (j : Fin n) (hj : q ≤ j.val) : PowerSeries.coeff (colPos D j) U = 0 := by
  classical
  have hT := properDet_cohLetters_ne_zero hD
  have hL := lowerZero_of_cutAt hq
  let u : Fin n → CohField := fun j => PowerSeries.coeff (colPos D j) U
  let u' : Fin n → CohField := fun j => if q ≤ j.val then u j else 0
  have hu' : u' = 0 := by
    refine trail_inj hT hL u' (fun j hj => by simp [u', not_le.2 hj]) fun i hi => ?_
    have e : (properMatrixOf cohLetters D *ᵥ u') i = (properMatrixOf cohLetters D *ᵥ u) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : q ≤ j.val
      · simp [u', hj]
      · simp [u', hj, hL i j hi (not_le.1 hj)]
    rw [e, ← coeff_rowPos_supp D hU i]
    exact h i hi
  have := congrFun hu' j
  simpa [u', hj] using this

theorem dSeries_sub (L : ℕ) (f g : PowerSeries CohField) :
    dSeries L (f - g) = dSeries L f - dSeries L g := by
  ext s; simp

theorem dSeries_mul (L : ℕ) (f g : PowerSeries CohField) :
    dSeries L (f * g) = dSeries L f * g + f * dSeries L g := by
  ext s; rw [coeff_dSeries, letterDeriv_coeff_mul, map_add]

/-- **The derivative of the difference of two coframes with a common prefix vanishes** in every
letter above the remaining rows, once the zero range covers the prefix rows. -/
theorem dCoframe_eq {B B' : BetaDiagram (n + 1)} (hBc : B.Connected) (hB'c : B'.Connected)
    {q : ℕ} (hcB : CutAt B q) (hcB' : CutAt B' q)
    (hrow : ∀ i : Fin n, i.val < q → rowPos B i = rowPos B' i)
    (hcol : ∀ j : Fin n, j.val < q → colPos B j = colPos B' j) (L : ℕ)
    (hlow : ∀ i : Fin n, q ≤ i.val → rowPos B i < L ∧ rowPos B' i < L)
    (hZ : ∀ i : Fin n, i.val < q → L ≤ rowPos B i →
      (coframe B).coeff (rowPos B i - L) = (coframe B').coeff (rowPos B i - L)) :
    dCoframe L B = dCoframe L B' := by
  have hW0 : ∀ j : Fin n, q ≤ j.val → PowerSeries.coeff (colPos B j) (dCoframe L B) = 0 := by
    refine trail_zero_coords hBc hcB (suppCols_dCoframe L B) fun i hi => ?_
    rw [coeff_rowPos_dCoframe hBc, if_neg (not_le.2 (hlow i hi).1), neg_zero]
  have hW0' : ∀ j : Fin n, q ≤ j.val → PowerSeries.coeff (colPos B' j) (dCoframe L B') = 0 := by
    refine trail_zero_coords hB'c hcB' (suppCols_dCoframe L B') fun i hi => ?_
    rw [coeff_rowPos_dCoframe hB'c, if_neg (not_le.2 (hlow i hi).2), neg_zero]
  have hsupp : SuppCols B (fun j => j.val < q) (dCoframe L B - dCoframe L B') := by
    intro s hs
    rw [map_sub]
    have h1 : PowerSeries.coeff s (dCoframe L B) = 0 := by
      by_cases hj : ∃ j, colPos B j = s
      · obtain ⟨j, rfl⟩ := hj
        exact hW0 j (not_lt.1 fun hlt => hs j hlt rfl)
      · push Not at hj
        exact suppCols_dCoframe L B s fun j _ => hj j
    have h2 : PowerSeries.coeff s (dCoframe L B') = 0 := by
      by_cases hj : ∃ j, colPos B' j = s
      · obtain ⟨j, rfl⟩ := hj
        refine hW0' j (not_lt.1 fun hlt => hs j hlt ?_)
        exact hcol j hlt
      · push Not at hj
        exact suppCols_dCoframe L B' s fun j _ => hj j
    rw [h1, h2, sub_zero]
  have hrows : ∀ i : Fin n, i.val < q →
      PowerSeries.coeff (rowPos B i) (letterSeries * (dCoframe L B - dCoframe L B')) = 0 := by
    intro i hi
    have e1 := coeff_rowPos_dCoframe hBc L i
    have e2 := coeff_rowPos_dCoframe hB'c L i
    rw [← hrow i hi] at e2
    rw [mul_sub, map_sub, e1, e2]
    by_cases hL : L ≤ rowPos B i
    · rw [if_pos hL, if_pos hL, hZ i hi hL]; ring
    · rw [if_neg hL, if_neg hL]; ring
  have := lead_inj_series hBc hcB hsupp hrows
  exact sub_eq_zero.1 this

variable {k : ℕ}

/-- **One step of the descent of the zero range.**  If the difference `Q` of two coframes with a
common prefix vanishes through degree `c + a - L - 1`, the second observation extends this to
degree `c + a - L`, for every letter `h_L` above the remaining rows and the cap. -/
theorem zeroRange_step (K : BetaDiagram (k + 1)) (hK : IsNorm K) {B B' : BetaDiagram (n + 1)}
    (hBc : B.Connected) (hB'c : B'.Connected) {q : ℕ} (hcB : CutAt B q) (hcB' : CutAt B' q)
    (hrow : ∀ i : Fin n, i.val < q → rowPos B i = rowPos B' i)
    (hcol : ∀ j : Fin n, j.val < q → colPos B j = colPos B' j) (L : ℕ)
    (hlow : ∀ i : Fin n, q ≤ i.val → rowPos B i < L ∧ rowPos B' i < L)
    (hLa : span K ≤ L)
    (hZ : ∀ j, j + (L + 1) ≤ span B + span K → (coframe B - coframe B').coeff j = 0)
    (hO2 : PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0) :
    ∀ j, j + L ≤ span B + span K → (coframe B - coframe B').coeff j = 0 := by
  have hd : dCoframe L B = dCoframe L B' := by
    refine dCoframe_eq hBc hB'c hcB hcB' hrow hcol L hlow fun i hi hL => ?_
    have h1 := rowPos_lt_span B i
    have := hZ (rowPos B i - L) (by omega)
    rwa [Polynomial.coeff_sub, sub_eq_zero] at this
  set Q : CohField[X] := coframe B - coframe B' with hQ
  have hdQ : dSeries L (Q : PowerSeries CohField) = 0 := by
    rw [hQ, Polynomial.coe_sub, dSeries_sub]
    exact sub_eq_zero.2 hd
  have hdC : dSeries L (leftCoframe K : PowerSeries CohField) = 0 := by
    ext s
    rw [coeff_dSeries, Polynomial.coeff_coe, map_zero]
    refine letterDeriv_eq_zero_of_mem (letterField_mono hLa ?_)
    refine leftCoframe_coeff_mem K hK ?_ s
    have := span_eq_of_norm K hK
    omega
  have hdCQ : dSeries L ((leftCoframe K * Q : CohField[X]) : PowerSeries CohField) = 0 := by
    rw [Polynomial.coe_mul, dSeries_mul, hdC, hdQ]; simp
  intro j hj
  have hN := congrArg (letterDeriv L) hO2
  rw [map_zero, letterDeriv_coeff_mul, dSeries_letterSeries, hdCQ, mul_zero, map_zero, add_zero,
    PowerSeries.coeff_X_pow_mul', if_pos (by omega), Polynomial.coeff_coe] at hN
  by_cases hj' : j + (L + 1) ≤ span B + span K
  · exact hZ j hj'
  · have hjN : j = span B + span K - L := by omega
    subst hjN
    rw [Polynomial.coeff_mul, Finset.sum_eq_single (0, span B + span K - L)] at hN
    · rw [leftCoframe_coeff_zero, one_mul] at hN
      exact hN
    · rintro ⟨i, l⟩ hil hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hil
      have hi : i ≠ 0 := fun h => hne (by rw [h] at hil ⊢; simp only [zero_add] at hil; rw [hil])
      rw [hZ l (by omega), mul_zero]
    · intro h; exact absurd (by simp) h

/-- **The descent of the zero range.**  If the second observation holds and `h_L` lies above every
remaining row of both diagrams and above the cap, the difference of the two right coframes
vanishes through degree `c + a - L`. -/
theorem zeroRange (K : BetaDiagram (k + 1)) (hK : IsNorm K) {B B' : BetaDiagram (n + 1)}
    (hBc : B.Connected) (hB'c : B'.Connected) {q : ℕ} (hcB : CutAt B q) (hcB' : CutAt B' q)
    (hrow : ∀ i : Fin n, i.val < q → rowPos B i = rowPos B' i)
    (hcol : ∀ j : Fin n, j.val < q → colPos B j = colPos B' j) (t : ℕ)
    (hlow : ∀ i : Fin n, q ≤ i.val → rowPos B i ≤ t ∧ rowPos B' i ≤ t)
    (hO2 : PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0)
    (L : ℕ) (hLt : t < L) (hLa : span K ≤ L) :
    ∀ j, j + L ≤ span B + span K → (coframe B - coframe B').coeff j = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, L + d = span B + span K + 1 ∨ span B + span K + 1 ≤ L := by
    by_cases h : L ≤ span B + span K + 1
    · exact ⟨span B + span K + 1 - L, Or.inl (by omega)⟩
    · exact ⟨0, Or.inr (by omega)⟩
  clear hd
  have key : ∀ d L : ℕ, L + d = span B + span K + 1 → t < L → span K ≤ L →
      ∀ j, j + L ≤ span B + span K → (coframe B - coframe B').coeff j = 0 := by
    intro d
    induction d with
    | zero => intro L hL _ _ j hj; omega
    | succ d ih =>
      intro L hL hLt hLa
      refine zeroRange_step K hK hBc hB'c hcB hcB' hrow hcol L
        (fun i hi => ⟨by have := (hlow i hi).1; omega, by have := (hlow i hi).2; omega⟩) hLa
        (ih (L + 1) (by omega) (by omega) (by omega)) hO2
  by_cases h : L ≤ span B + span K + 1
  · exact key (span B + span K + 1 - L) L (by omega) hLt hLa
  · intro j hj; omega

end SkewCoframeRigidity.FixedCap
