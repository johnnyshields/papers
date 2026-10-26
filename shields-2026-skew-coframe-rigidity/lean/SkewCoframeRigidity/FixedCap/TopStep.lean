/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.CapPrefix
import SkewCoframeRigidity.FixedCap.ZeroRange

/-!
# The first observation differentiated at the top letter

Formalizes the derivative of the first observation of `sc:fcp-observations` at the top letter `h_t`
in the proof of `sc:fixed-cap` of `shields-2026-skew-coframe-rigidity.tex`.  The part of the
derivative of the right coframe supported on the columns of the next strict block is the
quantity `β`; the derivative of the first observation says that `β` takes the same value on the
two diagrams.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The part of a series supported on the columns of `D` satisfying `P`. -/
noncomputable def maskCols (D : BetaDiagram (n + 1)) (P : Fin n → Prop)
    (U : PowerSeries CohField) : PowerSeries CohField :=
  open Classical in
  PowerSeries.mk fun s => if ∃ j, P j ∧ colPos D j = s then PowerSeries.coeff s U else 0

theorem coeff_maskCols_colPos (D : BetaDiagram (n + 1)) (P : Fin n → Prop)
    (U : PowerSeries CohField) (j : Fin n) :
    PowerSeries.coeff (colPos D j) (maskCols D P U) =
      open Classical in if P j then PowerSeries.coeff (colPos D j) U else 0 := by
  classical
  unfold maskCols
  rw [PowerSeries.coeff_mk]
  by_cases hj : P j
  · rw [if_pos ⟨j, hj, rfl⟩, if_pos hj]
  · rw [if_neg, if_neg hj]
    rintro ⟨j', hj', he⟩
    exact hj (by rwa [← colPos_injective D he])

theorem suppCols_maskCols (D : BetaDiagram (n + 1)) (P : Fin n → Prop)
    (U : PowerSeries CohField) : SuppCols D P (maskCols D P U) := by
  classical
  intro s hs
  unfold maskCols
  rw [PowerSeries.coeff_mk, if_neg]
  rintro ⟨j, hj, he⟩
  exact hs j hj he

/-- The part of `U` beyond the first `q` columns, when the coordinates from `r` on vanish, is
supported on the columns `q ≤ j < r`. -/
theorem suppCols_sub_mask {D : BetaDiagram (n + 1)} {U : PowerSeries CohField} (q r : ℕ)
    (hU : SuppCols D (fun _ => True) U)
    (hr : ∀ j : Fin n, r ≤ j.val → PowerSeries.coeff (colPos D j) U = 0) :
    SuppCols D (fun j => q ≤ j.val ∧ j.val < r) (U - maskCols D (fun j => j.val < q) U) := by
  classical
  intro s hs
  rw [map_sub]
  by_cases h : ∃ j, colPos D j = s
  · obtain ⟨j, rfl⟩ := h
    have hj : ¬ (q ≤ j.val ∧ j.val < r) := fun hj => hs j hj rfl
    rw [coeff_maskCols_colPos]
    by_cases hjq : j.val < q
    · rw [if_pos hjq, sub_self]
    · rw [if_neg hjq, sub_zero]
      exact hr j (by omega)
  · push Not at h
    rw [hU s fun j _ => h j]
    have : PowerSeries.coeff s (maskCols D (fun j => j.val < q) U) = 0 :=
      suppCols_maskCols D _ U s fun j _ => h j
    rw [this, sub_zero]

variable {k : ℕ}

/-- **The top letter of the first observation.**  For a diagram `D` carrying the cap `K` as its
prefix, the coefficient at the span of the derivative of the right coframe in `h_t` is the
quantity `β` plus a term that depends only on the prefix rows and the coframe coefficients there. -/
theorem coeff_span_dCoframe {q : ℕ} {hq : q ≤ n} {t : ℤ} {K : BetaDiagram (q + 1)}
    (hKc : K.Connected) {D : BetaDiagram (n + 1)} (hDc : D.Connected) (hD : IsNorm D)
    (hm : CapMatches D hq t K) (τ : ℕ) :
    PowerSeries.coeff (span D) (letterSeries * dCoframe τ D) =
      PowerSeries.coeff (span D) (letterSeries *
        ((leftCoframe K : CohField[X]) : PowerSeries CohField) *
          (dCoframe τ D - maskCols D (fun j => j.val < q) (dCoframe τ D))) +
      ∑ i : Fin q, leftVecOf cohLetters K i *
        (if τ ≤ rowPos D ⟨i.val, by omega⟩ then
          (coframe D).coeff (rowPos D ⟨i.val, by omega⟩ - τ) else 0) := by
  set W := dCoframe τ D with hW
  have h0 := coeff_cap_prefix hKc hD hm (U := maskCols D (fun j => j.val < q) W)
    (suppCols_maskCols D _ W)
  have hsplit : letterSeries * ((leftCoframe K : CohField[X]) : PowerSeries CohField) * W =
      letterSeries * ((leftCoframe K : CohField[X]) : PowerSeries CohField) *
        maskCols D (fun j => j.val < q) W +
      letterSeries * ((leftCoframe K : CohField[X]) : PowerSeries CohField) *
        (W - maskCols D (fun j => j.val < q) W) := by ring
  have h1 := coeff_cap_expand hD hm W
  rw [hsplit, map_add, h0, zero_add] at h1
  rw [h1]
  have : ∀ i : Fin q, leftVecOf cohLetters K i *
      PowerSeries.coeff (rowPos D ⟨i.val, by omega⟩) (letterSeries * W) =
      -(leftVecOf cohLetters K i * (if τ ≤ rowPos D ⟨i.val, by omega⟩ then
        (coframe D).coeff (rowPos D ⟨i.val, by omega⟩ - τ) else 0)) := fun i => by
    rw [hW, coeff_rowPos_dCoframe hDc]; ring
  simp only [this, Finset.sum_neg_distrib]
  ring

/-- The block quantity `β`: the part of the derivative of the coframe beyond the prefix columns,
read through the left coframe of the cap. -/
noncomputable def betaOf {q : ℕ} (K : BetaDiagram (q + 1)) (D : BetaDiagram (n + 1)) (τ : ℕ) :
    CohField :=
  PowerSeries.coeff (span D) (letterSeries *
    ((leftCoframe K : CohField[X]) : PowerSeries CohField) *
      (dCoframe τ D - maskCols D (fun j => j.val < q) (dCoframe τ D)))

/-- **The derivative of the first observation.**  If the zero range covers the position
`c - τ`, the derivative of the first observation says that the derivatives of the two right
coframes have the same coefficient at the span against `H`. -/
theorem coeff_span_dCoframe_sub {B B' : BetaDiagram (n + 1)} (τ : ℕ)
    (hspan : span B = span B')
    (hO1 : PowerSeries.coeff (span B) (letterSeries *
      ((coframe B - coframe B' : CohField[X]) : PowerSeries CohField)) = 0)
    (hQ : τ ≤ span B → (coframe B - coframe B').coeff (span B - τ) = 0) :
    PowerSeries.coeff (span B) (letterSeries * (dCoframe τ B - dCoframe τ B')) = 0 := by
  have h := congrArg (letterDeriv τ) hO1
  rw [map_zero, letterDeriv_coeff_mul, dSeries_letterSeries, PowerSeries.coeff_X_pow_mul',
    Polynomial.coe_sub, dSeries_sub] at h
  have e : dSeries τ (coframe B : PowerSeries CohField) -
      dSeries τ (coframe B' : PowerSeries CohField) = dCoframe τ B - dCoframe τ B' := rfl
  rw [e] at h
  by_cases hτ : τ ≤ span B
  · rw [if_pos hτ, ← Polynomial.coe_sub, Polynomial.coeff_coe, hQ hτ, zero_add] at h
    exact h
  · rw [if_neg hτ, zero_add] at h
    exact h

/-- **The block quantity is the same on both sides.** -/
theorem betaOf_eq {q : ℕ} {hq : q ≤ n} {t : ℤ} {K : BetaDiagram (q + 1)} (hKc : K.Connected)
    {B B' : BetaDiagram (n + 1)} (hBc : B.Connected) (hB'c : B'.Connected) (hB : IsNorm B)
    (hB' : IsNorm B') (hm : CapMatches B hq t K) (hm' : CapMatches B' hq t K) (τ : ℕ)
    (hspan : span B = span B')
    (hrow : ∀ i : Fin n, i.val < q → rowPos B i = rowPos B' i)
    (hZ : ∀ i : Fin n, i.val < q → τ ≤ rowPos B i →
      (coframe B).coeff (rowPos B i - τ) = (coframe B').coeff (rowPos B i - τ))
    (hO : PowerSeries.coeff (span B) (letterSeries * (dCoframe τ B - dCoframe τ B')) = 0) :
    betaOf K B τ = betaOf K B' τ := by
  have h1 := coeff_span_dCoframe hKc hBc hB hm τ
  have h2 := coeff_span_dCoframe hKc hB'c hB' hm' τ
  rw [← hspan] at h2
  rw [mul_sub, map_sub, h1, h2] at hO
  unfold betaOf
  rw [← hspan]
  have hsum : ∑ i : Fin q, leftVecOf cohLetters K i *
      (if τ ≤ rowPos B ⟨i.val, by omega⟩ then
        (coframe B).coeff (rowPos B ⟨i.val, by omega⟩ - τ) else 0) =
      ∑ i : Fin q, leftVecOf cohLetters K i *
      (if τ ≤ rowPos B' ⟨i.val, by omega⟩ then
        (coframe B').coeff (rowPos B' ⟨i.val, by omega⟩ - τ) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hrow ⟨i.val, by omega⟩ i.2]
    by_cases hτ : τ ≤ rowPos B ⟨i.val, by omega⟩
    · rw [if_pos hτ, if_pos hτ, hZ ⟨i.val, by omega⟩ i.2 hτ]
    · rw [if_neg hτ, if_neg hτ]
  rw [hsum] at hO
  linear_combination hO

/-- **Middle uniqueness.**  A series on the columns `q ≤ j < r` between two cuts whose product with
`H` vanishes at the rows `q ≤ i < r` is zero. -/
theorem mid_inj {D : BetaDiagram (n + 1)} (hD : D.Connected) {q r : ℕ} (hq : CutAt D q)
    (hr : CutAt D r) {U : PowerSeries CohField}
    (hU : SuppCols D (fun j => q ≤ j.val ∧ j.val < r) U)
    (h : ∀ i : Fin n, q ≤ i.val → i.val < r →
      PowerSeries.coeff (rowPos D i) (letterSeries * U) = 0) : U = 0 := by
  have hU' : SuppCols D (fun _ => True) U := hU.mono (fun _ _ => trivial)
  refine trail_inj_series hD hq (hU.mono fun j hj => hj.1) fun i hi => ?_
  by_cases hir : i.val < r
  · exact h i hi hir
  · rw [coeff_rowPos_supp D hU']
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j.val < r
    · rw [lowerZero_of_cutAt hr i j (not_lt.1 hir) hj, zero_mul]
    · rw [hU.apply_not (fun hj' => hj hj'.2), mul_zero]

theorem mid_unique {D : BetaDiagram (n + 1)} (hD : D.Connected) {q r : ℕ} (hq : CutAt D q)
    (hr : CutAt D r) {U V : PowerSeries CohField}
    (hU : SuppCols D (fun j => q ≤ j.val ∧ j.val < r) U)
    (hV : SuppCols D (fun j => q ≤ j.val ∧ j.val < r) V)
    (h : ∀ i : Fin n, q ≤ i.val → i.val < r →
      PowerSeries.coeff (rowPos D i) (letterSeries * U) =
        PowerSeries.coeff (rowPos D i) (letterSeries * V)) : U = V := by
  refine sub_eq_zero.1 (mid_inj hD hq hr (U := U - V) ?_ fun i hi1 hi2 => ?_)
  · intro s hs
    rw [map_sub, hU s hs, hV s hs, sub_zero]
  · rw [mul_sub, map_sub, h i hi1 hi2, sub_self]

/-- The row equations of the part of the derivative beyond the prefix. -/
theorem mid_rows {D : BetaDiagram (n + 1)} (hD : D.Connected) {q : ℕ} (hq : CutAt D q) (τ : ℕ)
    (i : Fin n) (hi : q ≤ i.val) :
    PowerSeries.coeff (rowPos D i) (letterSeries *
      (dCoframe τ D - maskCols D (fun j => j.val < q) (dCoframe τ D))) =
      -(if τ ≤ rowPos D i then (coframe D).coeff (rowPos D i - τ) else 0) := by
  have hpre : PowerSeries.coeff (rowPos D i) (letterSeries *
      maskCols D (fun j => j.val < q) (dCoframe τ D)) = 0 := by
    rw [coeff_rowPos_supp D ((suppCols_maskCols D _ _).mono fun _ _ => trivial)]
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j.val < q
    · rw [lowerZero_of_cutAt hq i j hi hj, zero_mul]
    · rw [(suppCols_maskCols D (fun j => j.val < q) _).apply_not hj, mul_zero]
  rw [mul_sub, map_sub, hpre, sub_zero, coeff_rowPos_dCoframe hD]

end SkewCoframeRigidity.FixedCap
