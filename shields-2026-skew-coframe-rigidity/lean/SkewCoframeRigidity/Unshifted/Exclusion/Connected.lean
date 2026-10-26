/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Connected.Corner
import SkewCoframeRigidity.Unshifted.Exclusion.Connected.Letters

/-!
# The connected proper corner

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`), the case where the entire proper corner is connected: the corner,
translated by `-1`, is a nonself child `E` of span `M - 2`; the quadratic equation becomes the
child equation `ℰ^L_{g,c} + z^L (g α_c - c α_g) = 0` modulo `z^{2L+2}`, whose coefficient of
`H_L z^{2L+1}` is `-p(p-1) ϑ^{p-2} [z^{L+1}] D_E ≠ 0`.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

/-- The proper corner is a single positive strict component: no cut and no unit. -/
def CornerConnected {n : ℕ} (V : BetaDiagram (n + 1)) : Prop :=
  (∀ c, ¬ IsCut V c) ∧ ∀ i, ¬ IsUnit' V i

section Child

variable {k : ℕ} (V : BetaDiagram (k + 1 + 1))
  (hnu : ∀ i : Fin (k + 1), V.col i.castSucc < V.row i.succ)

theorem cornerChild_connected (hcut : ∀ c, ¬ IsCut V c) (hcon : V.Connected) :
    (cornerChild V hnu).Connected := by
  refine ⟨Nat.succ_pos k, fun i hi => ?_⟩
  have h := hcut ⟨i.val + 1, hi⟩
  unfold IsCut at h
  push Not at h
  have := h i rfl
  simp only [cornerChild]
  have e : (⟨i.val + 1, hi⟩ : Fin (k + 1)).succ = (⟨i.val + 1, hi⟩ : Fin (k + 1)).succ := rfl
  change V.col i.castSucc - 1 ≤ V.row (⟨i.val + 1, hi⟩ : Fin (k + 1)).succ - 1
  omega

theorem cornerChild_ne_rotation (hVn : V.col (Fin.last (k + 1)) = 0)
    (hcol1 : V.col (Fin.last k).castSucc = 1) (hport : V.row 1 + 1 = V.row 0)
    (hne : V ≠ V.rotation) : cornerChild V hnu ≠ (cornerChild V hnu).rotation := by
  intro hE
  apply hne
  have e0 : (cornerChild V hnu).largestLabel =
      V.row 1 - 1 - (V.col (Fin.last k).castSucc - 1) := rfl
  have e1 : V.largestLabel = V.row 0 - V.col (Fin.last (k + 1)) := rfl
  have hrow : ∀ j : Fin (k + 1), V.row j.succ - 1 =
      (cornerChild V hnu).largestLabel - (V.col j.rev.castSucc - 1) := fun j => by
    have := congrArg (fun D : BetaDiagram (k + 1) => D.row j) hE
    simpa [BetaDiagram.rotation_row, cornerChild] using this
  have hcol : ∀ j : Fin (k + 1), V.col j.castSucc - 1 =
      (cornerChild V hnu).largestLabel - (V.row j.rev.succ - 1) := fun j => by
    have := congrArg (fun D : BetaDiagram (k + 1) => D.col j) hE
    simpa [BetaDiagram.rotation_col, cornerChild] using this
  have ext : ∀ A B : BetaDiagram (k + 1 + 1), A.row = B.row → A.col = B.col → A = B := by
    intro A B h1 h2
    cases A
    cases B
    simp only at h1 h2
    subst h1 h2
    rfl
  refine ext _ _ (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [BetaDiagram.rotation_row, Fin.rev_zero]
      omega
    · simp only [BetaDiagram.rotation_row, rev_succ_castSucc]
      have := hrow j
      omega
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [BetaDiagram.rotation_col, Fin.rev_last]
      omega
    · simp only [BetaDiagram.rotation_col, rev_castSucc_succ]
      have := hcol j
      omega

end Child

theorem exclusion_connected {n : ℕ} {V W : BetaDiagram (n + 1)} {p : ℕ}
    (H : ExclusionHyp V W p) (hc : CornerConnected V) : False := by
  have hWV := eq_rotation_of_rotationEquivalent H.colV H.colW H.rot
  have hne : V ≠ V.rotation := hWV ▸ H.ne
  obtain ⟨hP, hQ⟩ := exclusion_ports H
  obtain ⟨i0, hi0⟩ := hP
  obtain ⟨j0, hj0⟩ := hQ
  subst hWV
  cases n with
  | zero => exact i0.elim0
  | succ k =>
  have hVn := H.colV
  have hport : V.row 1 + 1 = V.row 0 := by
    have h1 := rowPos_cast V i0
    have h2 := span_cast V
    have e1 : V.largestLabel = V.row 0 - V.col (Fin.last (k + 1)) := rfl
    have h3 : V.row i0.succ ≤ V.row 1 :=
      V.row_strictAnti.antitone (by simp [Fin.le_def])
    have h4 : V.row 1 < V.row 0 := V.row_strictAnti (by simp [Fin.lt_def])
    omega
  have hcol1 : V.col (Fin.last k).castSucc = 1 := by
    have h5 := colPos_cast V j0
    have h6 : V.col (Fin.last k).castSucc ≤ V.col j0.castSucc :=
      V.col_strictAnti.antitone (by simp [Fin.le_def]; omega)
    have h7 : V.col (Fin.last (k + 1)) < V.col (Fin.last k).castSucc :=
      V.col_strictAnti (by simp [Fin.lt_def])
    omega
  have hnu : ∀ i : Fin (k + 1), V.col i.castSucc < V.row i.succ := fun i => by
    have h1 := H.conn.2 i.castSucc (by simp; have := i.isLt; omega)
    have h2 : V.row ⟨i.castSucc.val + 1, by simp; have := i.isLt; omega⟩ = V.row i.succ := rfl
    have h3 := hc.2 i
    unfold IsUnit' at h3
    rw [h2] at h1
    exact lt_of_le_of_ne h1 (fun e => h3 e.symm)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := H.hp; omega⟩
  set E := cornerChild V hnu with hE
  have hspan : span E + 2 = span V := span_cornerChild V hnu hVn hcol1 hport
  have hM3 := H.span3
  have hEc : E.Connected := cornerChild_connected V hnu hc.1 H.conn
  have hEn : E.col (Fin.last k) = 0 := by
    simp only [hE, cornerChild, hcol1]; norm_num
  have hErn := BetaDiagram.rotation_col_last E hEn
  have hEne : E ≠ E.rotation := cornerChild_ne_rotation V hnu hVn hcol1 hport hne
  have hsch : E.schur = E.rotation.schur := (BetaDiagram.schur_rotation E).symm
  have hdist := coequal_distinct hEc hEn hErn hsch hEne
  have hfirst := first_defect_coeff_ne_zero' hEc hEn hErn (BetaDiagram.rotationEquivalent_rotation E)
    hEne hdist.1
  have hcoeq := (coequal_data hEc hsch).2.2.2.2.1
  set L := span E with hL
  have hL3 : 3 ≤ L := hdist.1
  set h₁ : ℕ → CohField := Function.update (zeroTop V) L 0 with hh1
  have hz1 : h₁ L = 0 := Function.update_self _ _ _
  have hlow : ∀ j < L, h₁ j = cohLetters j := fun j hj => by
    rw [hh1, Function.update_of_ne (by omega)]
    unfold zeroTop
    rw [Function.update_of_ne (by omega)]
  have h10 : h₁ 0 = cohLetters 0 := hlow 0 (by omega)
  have hlowR : ∀ j < span E.rotation, h₁ j = cohLetters j := fun j hj => by
    rw [span_rotation] at hj; exact hlow j hj
  set g := coframeOf h₁ E with hg
  set c := coframeOf h₁ E.rotation with hcdef
  have hg' : g = coframe E := coframeOf_eq_of_letters E hlow
  have hc' : c = coframe E.rotation := coframeOf_eq_of_letters E.rotation hlowR
  have hDeq : clippedOp L g c (seriesOf h₁) = defect E E.rotation := by
    rw [hg', hc']
    unfold defect
    refine clippedOp_congr_series L _ _ fun j hj => ?_
    simp only [seriesOf, letterSeries, PowerSeries.coeff_mk, hlow j hj]
  have hd : PowerSeries.coeff (L + 1)
      ((clippedOp L g c (seriesOf h₁) : CohField[X]) : PowerSeries CohField) ≠ 0 := by
    rw [hDeq, Polynomial.coeff_coe]; exact hfirst
  have hD : ∀ j ≤ L, PowerSeries.coeff j
      ((clippedOp L g c (seriesOf h₁) : CohField[X]) : PowerSeries CohField) = 0 := by
    intro j hj
    rw [hDeq, Polynomial.coeff_coe]; exact hcoeq j hj
  have hlowZ : ∀ k', k' + 1 < span V → zeroTop V k' = cohLetters k' := fun k' hk' => by
    unfold zeroTop; exact Function.update_of_ne (by omega) _ _
  have hT0 : (properMatrixOf (zeroTop V) V).det ≠ 0 := by
    rw [properMatrixOf_congr V hlowZ]
    exact properDet_cohLetters_ne_zero H.conn
  have hTE0 : (properMatrixOf (zeroTop V) E).det ≠ 0 := by
    rw [properMatrixOf_congr E (h' := cohLetters) (fun k' hk' => hlowZ k' (by omega))]
    exact properDet_cohLetters_ne_zero hEc
  have hKey : ∀ t : ℤ, PowerSeries.coeff (2 * L + 1)
      (childExpr (q + 2) L (Function.update h₁ L (cohLetters L + t)) g c) = 0 := by
    intro t
    have hℓ : (fun j => shiftField L t (zeroTop V j)) =
        Function.update h₁ L (cohLetters L + t) := by
      funext j
      by_cases hj : j = L
      · rw [hj]
        have : zeroTop V L = cohLetters L := hlowZ L (by omega)
        rw [this, shiftField_cohLetters, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj]
        by_cases hjm : j = span V - 1
        · have : zeroTop V j = 0 := by unfold zeroTop; rw [hjm, Function.update_self]
          rw [this, map_zero, hh1, Function.update_of_ne hj, this]
        · have : zeroTop V j = cohLetters j := by
            unfold zeroTop; exact Function.update_of_ne hjm _ _
          rw [this, shiftField_cohLetters, Function.update_of_ne hj, hh1, Function.update_of_ne hj,
            this]
    have hYt : ∀ j < 2 * span V, PowerSeries.coeff j
        (genY2 (q + 2) (fun j => shiftField L t (zeroTop V j)) V V.rotation) = 0 := by
      intro j hj
      rw [genY2_map, PowerSeries.coeff_map, (coef_vanish H hj).2.2, map_zero]
    have := corner_equation V hnu hVn hcol1 hport (q + 2) _
      (det_properMatrixOf_map (shiftField L t) _ V hT0)
      (det_properMatrixOf_map (shiftField L t) _ E hTE0) hYt (2 * L + 1) (by show 2 * L + 1 < 2 * span E + 2; omega)
    rw [hℓ] at this
    have e1 : coframeOf (Function.update h₁ L (cohLetters L + t)) E = g :=
      coframeOf_eq_of_letters E fun j hj => by rw [Function.update_of_ne (by omega)]
    have e2 : coframeOf (Function.update h₁ L (cohLetters L + t)) E.rotation = c :=
      coframeOf_eq_of_letters E.rotation fun j hj => by
        rw [span_rotation] at hj
        rw [Function.update_of_ne (by omega)]
    rw [e1, e2] at this
    exact this
  have k0 := hKey 0
  have k1 := hKey 1
  rw [childExpr_top_letter q L (by omega) h₁ _ g c (coframeOf_coeff_zero _ _)
    (coframeOf_coeff_zero _ _) hD hz1] at k0 k1
  have hκ : (((q + 2 : ℕ) : CohField) * ((q + 1 : ℕ) : CohField) * h₁ 0 ^ q) ≠ 0 := by
    rw [h10]
    exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 (by omega)))
      (pow_ne_zero _ (cohLetters_ne_zero 0))
  have hprod : (((q + 2 : ℕ) : CohField) * ((q + 1 : ℕ) : CohField) * h₁ 0 ^ q) *
      PowerSeries.coeff (L + 1)
        ((clippedOp L g c (seriesOf h₁) : CohField[X]) : PowerSeries CohField) = 0 := by
    simp only [Int.cast_zero, Int.cast_one] at k0 k1
    linear_combination k0 - k1
  exact hd ((mul_eq_zero.1 hprod).resolve_left hκ)

end SkewCoframeRigidity.Unshifted
