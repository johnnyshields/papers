/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Setup
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Close
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Finale
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.EqualEnds
import SkewCoframeRigidity.Unshifted.UpstreamInputs

/-!
# The disconnected corner of the unshifted exclusion

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, the disconnected corner).  Under `ExclusionHyp V W p`, a proper corner
with two or more strict components contradicts `V ≠ W`, given `EqualEnds V W p`.

The top strict components of `V` and of its rotation carry the endpoint columns
`a = -z^A g / k_E` and `b = -z^B c / k_F`.  The branches `A < B` and `A > B` are excluded by the
coordinates `α_{F,p}`, `α_{E,p}` and the span three numerator.  For `A = B` the input
`EqualEnds` states that the two columns coincide (the fixed-cap rigidity step of the paper);
the remaining steps (order of `Δ` against the half-window, the equation against the two-cell
row, the balanced configurations `M = 7, 8`) are proved here.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- When both endpoint columns start at the same degree, they coincide: the equal-ends step of
the disconnected corner, where the fixed-cap theorem identifies the two end components. -/
def EqualEnds (V W : BetaDiagram (n + 1)) (p : ℕ) : Prop :=
  (∀ k < 2 * span V, PowerSeries.coeff k (coefY2 p V W) = 0) →
    ∀ A : ℕ, (∀ i < A, (aVec V).coeff i = 0 ∧ (bVec V).coeff i = 0) → (aVec V).coeff A ≠ 0 →
      (bVec V).coeff A ≠ 0 → aVec V = bVec V

theorem coefY2_eq_defectExpr {V W : BetaDiagram (n + 1)} {p : ℕ} (hM : 2 ≤ span V) :
    coefY2 p V W = defectExpr (span V) p (zeroTop V) (aVec V) (bVec V) := by
  unfold coefY2 defectExpr Eop pDiff hSer
  rw [zeroTop_zero hM, map_pow, Polynomial.coe_sub]

theorem coefY1_eq_linExpr {V W : BetaDiagram (n + 1)} {p : ℕ} (hM : 2 ≤ span V) :
    coefY1 p V W = linExpr (span V) p (zeroTop V) (G0 V) (C0 V W) (aVec V) (bVec V) := by
  unfold coefY1 linExpr Eop pDiff hSer Delta
  rw [zeroTop_zero hM, map_pow, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_add]
  ring

/-- The equal-ends step, given the descent for the one-cell cap: two top components of the same
start coincide, so the two endpoint columns are equal. -/
theorem equalEnds_of_cap (hcap : FixedCap.CapVanishing cellCap) {V W : BetaDiagram (n + 1)}
    {p : ℕ} (H : ExclusionHyp V W p) (hdisc : ∃ i j : Fin n, blockIdx V i ≠ blockIdx V j) :
    EqualEnds V W p := by
  classical
  intro hY2 A' hav haA' hbA'
  have hM3 := H.span3
  have hWV := eq_rotation_of_rotationEquivalent H.colV H.colW H.rot
  have hsch : V.schur = W.schur := by rw [hWV, BetaDiagram.schur_rotation]
  have hWc : W.Connected := V.connected_of_schur_eq W H.conn hsch
  have hr : ∀ i, W.row i = (V.largestLabel : ℤ) - V.col i.rev := fun i => by rw [hWV]; simp
  have hc : ∀ i, W.col i = (V.largestLabel : ℤ) - V.row i.rev := fun i => by rw [hWV]; simp
  have hspan : span W = span V := span_rot hr hc H.colW
  obtain ⟨hP, hQ⟩ := exclusion_ports H
  have hlow : ∀ k, k + 1 < span V → zeroTop V k = cohLetters k := fun k hk => by
    unfold zeroTop; exact Function.update_of_ne (by omega) _ _
  have hlowW : ∀ k, k + 1 < span W → zeroTop V k = cohLetters k := fun k hk => hlow k (by omega)
  have hh0 : zeroTop V 0 ≠ 0 := by
    rw [zeroTop_zero (by omega)]; exact cohLetters_ne_zero 0
  have hPW : ∃ i, rowPos W i + 1 = span W := by
    obtain ⟨j, hj⟩ := hQ
    refine ⟨j.rev, ?_⟩
    have := rowPos_rot hr hc H.colW j.rev
    rw [Fin.rev_rev] at this
    have := colPos_lt_span V j
    omega
  obtain ⟨A, L, cV, g, k, hA1, hAL, hg0, hgdeg, hk, hk0, ha, hkind, hn0, hcV0, hcVn, hbV, hltV,
    hAcol⟩ := top_data V H.conn H.colV (zeroTop V) hlow hh0 hP
  obtain ⟨B, R, cW, c, kF, hB1, hBR, hc0, hcdeg, hkF, hkF0, hb, hkindW, hn0W, hcW0, hcWn, hbW,
    hltW, hBcol⟩ := top_data W hWc H.colW (zeroTop V) hlowW hh0 hPW
  have hbVec : bVec V = endpointA (zeroTop V) W :=
    (endpointA_rot (zeroTop V) hr hc H.colW).symm
  have hcVn' : cV < n := by
    by_contra hcon
    obtain ⟨i, j, hij⟩ := hdisc
    apply hij
    have a1 := (hbV i).mpr (by have := i.isLt; omega)
    have a2 := (hbV j).mpr (by have := j.isLt; omega)
    rw [a1, a2]
  obtain ⟨hsep, hsum⟩ := separation hr hc H.colV H.colW cV cW hbV hbW hcV0 hcW0 hcWn hcVn'
  rw [hAcol, hBcol] at hsep
  have ae : aVec V = Polynomial.C (-1 / k) * (Polynomial.X ^ A * g) := ha
  have be : bVec V = Polynomial.C (-1 / kF) * (Polynomial.X ^ B * c) := by rw [hbVec]; exact hb
  have haA : (aVec V).coeff A ≠ 0 := by
    rw [ae]
    have := coeff_shift_poly (-1 / k) A g 0
    rw [add_zero, hg0, mul_one] at this
    rw [this]; exact div_ne_zero (by norm_num) hk0
  have hbB : (bVec V).coeff B ≠ 0 := by
    rw [be]
    have := coeff_shift_poly (-1 / kF) B c 0
    rw [add_zero, hc0, mul_one] at this
    rw [this]; exact div_ne_zero (by norm_num) hkF0
  have hlowA : ∀ i < A, (aVec V).coeff i = 0 := fun i hi => by
    rw [ae, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
  have hlowB : ∀ i < B, (bVec V).coeff i = 0 := fun i hi => by
    rw [be, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
  have hAA' : A = A' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact haA ((hav A h1).1)
    · exact haA' (hlowA A' h1)
  have hBA' : B = A' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact hbB ((hav B h1).2)
    · exact hbA' (hlowB A' h1)
  have hAB : A = B := hAA'.trans hBA'.symm
  subst hAB
  have hLR : L = R := by omega
  subst hLR
  have hA2 : 2 ≤ A := by omega
  have hgc : g = c := by
    rcases hkind with ⟨hL0, hg1, -, -⟩ | ⟨e, E, hE, hEn, hsE, hgE, -⟩
    · rcases hkindW with ⟨-, hc1, -, -⟩ | ⟨e', F, hF, hFn, hsF, hgF, -⟩
      · rw [hg1, hc1]
      · have := span_pos F; omega
    · rcases hkindW with ⟨hR0, -⟩ | ⟨e', F, hF, hFn, hsF, hgF, -⟩
      · have := span_pos E; omega
      · by_cases hL1 : L = 1
        · have he := span_eq_one_imp E (hsE.trans hL1)
          have he' := span_eq_one_imp F (hsF.trans hL1)
          subst he he'
          rw [hgE, hgF, coframe_of_zero, coframe_of_zero]
        · have hL2 : 2 ≤ L := by have := span_pos E; rw [hsE] at this; omega
          have hAL2 : L + 2 ≤ A := by omega
          obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := H.hp; omega⟩
          have hkE : k = topQuotient E := by
            have : topQuotient E = PowerSeries.coeff L
                (letterSeries * (coframe E : PowerSeries CohField)) := by
              unfold topQuotient topQuotientOf; rw [hsE]; rfl
            rw [this, hk, hgE]
            rw [mul_comm, mul_comm letterSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            refine Finset.sum_congr rfl fun x hx => ?_
            have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
            congr 1
            unfold letterSeries seriesOf zeroTop
            simp only [PowerSeries.coeff_mk]
            rw [Function.update_of_ne (by omega)]
          have hkF' : kF = topQuotient F := by
            have : topQuotient F = PowerSeries.coeff L
                (letterSeries * (coframe F : PowerSeries CohField)) := by
              unfold topQuotient topQuotientOf; rw [hsF]; rfl
            rw [this, hkF, hgF]
            rw [mul_comm, mul_comm letterSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            refine Finset.sum_congr rfl fun x hx => ?_
            have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
            congr 1
            unfold letterSeries seriesOf zeroTop
            simp only [PowerSeries.coeff_mk]
            rw [Function.update_of_ne (by omega)]
          have hxy : (-1 / k) * (-1 / kF) ≠ 0 :=
            mul_ne_zero (div_ne_zero (by norm_num) hk0) (div_ne_zero (by norm_num) hkF0)
          have e0 : ∀ m < 2 * span E + 2, PowerSeries.coeff m (eqL (span E) (q + 2)
              (coframe E) (coframe F) (topQuotient E) (topQuotient F) letterSeries) = 0 := by
            intro m hm
            rw [hsE] at hm ⊢
            have h2 := hY2 (2 * A + m) (by omega)
            rw [coefY2_eq_defectExpr (by omega), ae, be, hq, hgE, hgF] at h2
            have hsc := defectExpr_scale A L (q + 2) (zeroTop V) (-1 / k) (-1 / kF)
              (div_ne_zero (by norm_num) hk0) (div_ne_zero (by norm_num) hkF0)
              (coframe E) (coframe F)
            have hMA : A + L + 1 = span V := hAL
            rw [hMA] at hsc
            rw [hsc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
              ite_eq_left (by omega), Nat.add_sub_cancel_left] at h2
            have h3 := (mul_eq_zero.mp h2).resolve_left hxy
            have e1 : -1 / (-1 / k) = k := by field_simp
            have e2 : -1 / (-1 / kF) = kF := by field_simp
            rw [e1, e2] at h3
            obtain ⟨R', hR'⟩ := eqL_congr L (q + 2) (coframe E) (coframe F) k kF
              (seriesOf (zeroTop V)) letterSeries
              (PowerSeries.mk fun i => cohLetters (A + L + i) - zeroTop V (A + L + i)) (A + L)
              (by omega) (by
                ext i
                simp only [letterSeries, seriesOf, map_add, PowerSeries.coeff_mk,
                  PowerSeries.coeff_X_pow_mul']
                by_cases hi : A + L ≤ i
                · rw [ite_eq_left hi]
                  have : A + L + (i - (A + L)) = i := by omega
                  simp only [this]; ring
                · rw [ite_eq_right hi, add_zero]
                  unfold zeroTop
                  rw [Function.update_of_ne (by omega)])
            rw [hkE, hkF'] at hR'
            rw [hkE, hkF'] at h3
            rw [hR', map_add, h3, zero_add, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
          have := equal_components hcap E F hE hF (hsE.trans hsF.symm) (by omega) q
            (by rw [hsE] at e0 ⊢; exact e0)
          rw [hgE, hgF]; exact this
  have hkk : k = kF := by rw [hk, hkF, hgc]
  rw [ae, be, hgc, hkk]


theorem exclusion_disconnected {V W : BetaDiagram (n + 1)} {p : ℕ} (H : ExclusionHyp V W p)
    (hdisc : ∃ i j : Fin n, blockIdx V i ≠ blockIdx V j) (hEnds : EqualEnds V W p) : False := by
  classical
  have hM3 := H.span3
  have hWV := eq_rotation_of_rotationEquivalent H.colV H.colW H.rot
  have hsch : V.schur = W.schur := by rw [hWV, BetaDiagram.schur_rotation]
  have hWc : W.Connected := V.connected_of_schur_eq W H.conn hsch
  have hr : ∀ i, W.row i = (V.largestLabel : ℤ) - V.col i.rev := fun i => by rw [hWV]; simp
  have hc : ∀ i, W.col i = (V.largestLabel : ℤ) - V.row i.rev := fun i => by rw [hWV]; simp
  have hspan : span W = span V := span_rot hr hc H.colW
  obtain ⟨hP, hQ⟩ := exclusion_ports H
  obtain ⟨-, hY1, hY2⟩ := exclusion_expansion H
  have hlow : ∀ k, k + 1 < span V → zeroTop V k = cohLetters k := fun k hk => by
    unfold zeroTop; exact Function.update_of_ne (by omega) _ _
  have hlowW : ∀ k, k + 1 < span W → zeroTop V k = cohLetters k := fun k hk => hlow k (by omega)
  have hh0 : zeroTop V 0 ≠ 0 := by
    rw [zeroTop_zero (by omega)]; exact cohLetters_ne_zero 0
  have hPW : ∃ i, rowPos W i + 1 = span W := by
    obtain ⟨j, hj⟩ := hQ
    refine ⟨j.rev, ?_⟩
    have := rowPos_rot hr hc H.colW j.rev
    rw [Fin.rev_rev] at this
    have := colPos_lt_span V j
    omega
  obtain ⟨A, L, cV, g, k, hA1, hAL, hg0, hgdeg, hk, hk0, ha, hkind, hn0, hcV0, hcVn, hbV, hltV,
    hAcol⟩ := top_data V H.conn H.colV (zeroTop V) hlow hh0 hP
  obtain ⟨B, R, cW, c, kF, hB1, hBR, hc0, hcdeg, hkF, hkF0, hb, hkindW, hn0W, hcW0, hcWn, hbW,
    hltW, hBcol⟩ := top_data W hWc H.colW (zeroTop V) hlowW hh0 hPW
  have hbVec : bVec V = endpointA (zeroTop V) W :=
    (endpointA_rot (zeroTop V) hr hc H.colW).symm
  have hcVn' : cV < n := by
    by_contra hcon
    obtain ⟨i, j, hij⟩ := hdisc
    apply hij
    have a1 := (hbV i).mpr (by have := i.isLt; omega)
    have a2 := (hbV j).mpr (by have := j.isLt; omega)
    rw [a1, a2]
  obtain ⟨hsep, hsum⟩ := separation hr hc H.colV H.colW cV cW hbV hbW hcV0 hcW0 hcWn hcVn'
  rw [hAcol, hBcol] at hsep
  have hA2 : 2 ≤ A := by omega
  have hB2 : 2 ≤ B := by omega
  have hBR' : B + R + 1 = span V := by omega
  obtain ⟨hFa, hFn⟩ := comp_facts p H.hp W (zeroTop V) hlowW B R cW c kF hB2 hBR hkindW
  obtain ⟨hEa, hEn⟩ := comp_facts p H.hp V (zeroTop V) hlow A L cV g k hA2 hAL hkind
  have ae : aVec V = Polynomial.C (-1 / k) * (Polynomial.X ^ A * g) := ha
  have be : bVec V = Polynomial.C (-1 / kF) * (Polynomial.X ^ B * c) := by rw [hbVec]; exact hb
  have heq : ∀ m < 2 * span V, PowerSeries.coeff m (defectExpr (span V) p (zeroTop V)
      (Polynomial.C (-1 / k) * (Polynomial.X ^ A * g))
      (Polynomial.C (-1 / kF) * (Polynomial.X ^ B * c))) = 0 := by
    intro m hm
    have := hY2 m hm
    rw [coefY2_eq_defectExpr (by omega)] at this
    rw [ae, be] at this
    exact this
  rcases lt_trichotomy A B with hlt | hAB | hgt
  · refine lt_branch_false (zeroTop V) (span V) A B L R p H.hp hlt hAL hBR' g c k kF hg0 hgdeg hk
      hkF hk0 hkF0 heq ?_ hEn
    rcases hFa with h | ⟨h1, h2, h3, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩
  · -- equal starting degrees
    subst hAB
    have hav : ∀ i < A, (aVec V).coeff i = 0 ∧ (bVec V).coeff i = 0 := by
      intro i hi
      rw [ae, be]
      exact ⟨by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega),
        mul_zero], by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
        ite_eq_right (by omega), mul_zero]⟩
    have haA : (aVec V).coeff A ≠ 0 := by
      rw [ae]
      have := coeff_shift_poly (-1 / k) A g 0
      rw [add_zero, hg0, mul_one] at this
      rw [this]; exact div_ne_zero (by norm_num) hk0
    have hbA : (bVec V).coeff A ≠ 0 := by
      rw [be]
      have := coeff_shift_poly (-1 / kF) A c 0
      rw [add_zero, hc0, mul_one] at this
      rw [this]; exact div_ne_zero (by norm_num) hkF0
    have hab : aVec V = bVec V := hEnds hY2 A hav haA hbA
    have hGV : coframe V = G0 V + Polynomial.C (topY V) * aVec V := by
      have := coframeOf_eq cohLetters V
      rw [endpointA_congr V (h' := zeroTop V) (fun k hk => (hlow k hk).symm)] at this
      exact this
    have hCW : coframe W = C0 V W + Polynomial.C (topY V) * bVec V := by
      have := coframeOf_rot_eq cohLetters hr hc H.colW
      rw [endpointB_congr V (h' := zeroTop V) (fun k hk => (hlow k hk).symm)] at this
      exact this
    have hΔeq : Delta V W = coframe V - coframe W := by
      unfold Delta; rw [hGV, hCW, hab]; ring
    have hΔne : Delta V W ≠ 0 := by
      intro h0
      have : coframe V = coframe W := sub_eq_zero.1 (by rw [← hΔeq]; exact h0)
      obtain ⟨-, hheq⟩ := eq_of_coframe_eq H.colV H.colW H.conn hWc hspan.symm this
      exact H.ne (eq_of_heq hheq)
    have hΔd : (Delta V W).coeff (Delta V W).natTrailingDegree ≠ 0 :=
      Polynomial.trailingCoeff_nonzero_iff_nonzero.2 hΔne
    have hΔlow : ∀ i < (Delta V W).natTrailingDegree, (Delta V W).coeff i = 0 := fun i hi =>
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi
    have hd_le : (Delta V W).natTrailingDegree ≤ span V / 2 := by
      by_contra hcon
      apply H.ne
      refine eq_of_coframe_low hr hc H.conn hWc H.colV H.colW (span V / 2) (by omega)
        (fun i hi => ?_)
      have := hΔlow i (by omega)
      rw [hΔeq, Polynomial.coeff_sub, sub_eq_zero] at this
      exact this
    have hdA : (Delta V W).natTrailingDegree < A := by omega
    have heq1 : ∀ m < 2 * span V, PowerSeries.coeff m (defectExpr (span V) p (zeroTop V)
        (Delta V W) (Polynomial.C (-1 / k) * (Polynomial.X ^ A * g)) +
        PowerSeries.C (p : CohField) * (PowerSeries.C (zeroTop V 0 ^ (p - 1)) -
          seriesOf (zeroTop V) ^ (p - 1)) * PowerSeries.X ^ (span V - 1) *
        ((Polynomial.C (-1 / k) * (Polynomial.X ^ A * g) : CohField[X]) : PowerSeries CohField)) = 0 := by
      intro m hm
      have := hY1 m hm
      rw [coefY1_eq_linExpr (by omega), ← hab, linExpr_same] at this
      rw [ae] at this
      exact this
    have hk' : (-1 / k) * PowerSeries.coeff L (seriesOf (zeroTop V) *
        (g : PowerSeries CohField)) = -1 := by
      rw [← hk]; field_simp
    have hαzero := alphaOf_eq_zero_of_lin (span V) _ A L p H.hp (by omega) hdA (by omega)
      (zeroTop V) (Delta V W) g (-1 / k) hΔlow hΔd (div_ne_zero (by norm_num) hk0) hk' heq1
    rcases hEa with hne | ⟨hp2, hL2, hg1, hcV1⟩
    · exact absurd hαzero hne
    subst hp2
    subst hL2
    subst hg1
    have hMe : span V = A + 3 := by omega
    have hRe : R = 2 := by omega
    have hc1 : c = 1 := by
      have habc := hab
      rw [ae, be] at habc
      have hcoef : ∀ j, (-1 / k) * (1 : CohField[X]).coeff j = (-1 / kF) * c.coeff j := by
        intro j
        have := congrArg (fun F : CohField[X] => F.coeff (A + j)) habc
        simpa only [coeff_shift_poly] using this
      have hkk : kF = k := by
        have := hcoef 0
        rw [Polynomial.coeff_one_zero, hc0] at this
        have h1 : (-1 / k) = (-1 / kF) := by simpa using this
        field_simp at h1
        linear_combination (-1 : CohField) * h1
      ext j
      have := hcoef j
      rw [hkk] at this
      have hne : (-1 / k) ≠ 0 := div_ne_zero (by norm_num) hk0
      exact (mul_left_cancel₀ hne this).symm
    have hcW1 : cW = 1 := by
      rcases hkindW with ⟨hR0, -⟩ | ⟨e, E, hE, hEn', hsE, hgE, hcnt⟩
      · omega
      · have : coframe E = 1 := by rw [← hgE, hc1]
        have := coframe_eq_one_imp E hE this
        omega
    subst hcV1
    subst hcW1
    have hn1 : 1 < n := by omega
    have hβ' : (-1 / k) * zeroTop V 2 = -1 := by
      have : k = zeroTop V 2 := by rw [hk]; simp [coeff_seriesOf]
      rw [← this]; field_simp
    have hord := rowTwo_lin_order A _ (zeroTop V) (Delta V W) (-1 / k) hβ' hΔlow hΔd (by
      intro m hm
      have := heq1 m (by omega)
      rw [hMe] at this
      simpa only [mul_one, Nat.cast_ofNat] using this)
    have hM78 : span V = 7 ∨ span V = 8 := by omega
    have hVA : colPos V ⟨0, by omega⟩ = span V - 3 := by
      have : colPos V ⟨1 - 1, hltV⟩ = A := hAcol
      have e : colPos V ⟨0, by omega⟩ = colPos V ⟨1 - 1, hltV⟩ := rfl
      omega
    have hWA : colPos W ⟨0, by omega⟩ = span V - 3 := by
      have : colPos W ⟨1 - 1, hltW⟩ = A := hBcol
      have e : colPos W ⟨0, by omega⟩ = colPos W ⟨1 - 1, hltW⟩ := rfl
      omega
    have hVp := rowPos_zero_succ H.colV hP (by omega : 0 < n)
    have hWp := rowPos_zero_succ H.colW hPW (by omega : 0 < n)
    rw [hspan] at hWp
    have hsym := small_closure hr hc H.colV H.colW hn1 hM78 hbV hbW hVA hWA hVp hWp
    have := eq_rotation_of_rotationEquivalent H.colV H.colV hsym
    exact H.ne (this.trans hWV.symm)
  · refine gt_branch_false (zeroTop V) (span V) A B L R p H.hp hgt hAL hBR' g c k kF hc0 hcdeg hk
      hkF hk0 hkF0 heq ?_ hFn
    rcases hEa with h | ⟨h1, h2, h3, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩

/-- The disconnected corner, given the descent for the one-cell cap. -/
theorem exclusion_disconnected' (hcap : FixedCap.CapVanishing cellCap) {V W : BetaDiagram (n + 1)}
    {p : ℕ} (H : ExclusionHyp V W p) (hdisc : ∃ i j : Fin n, blockIdx V i ≠ blockIdx V j) :
    False :=
  exclusion_disconnected H hdisc (equalEnds_of_cap hcap H hdisc)

/-- The disconnected corner of the unshifted exclusion. -/
theorem exclusion_disconnected'' {V W : BetaDiagram (n + 1)} {p : ℕ} (H : ExclusionHyp V W p)
    (hdisc : ∃ i j : Fin n, blockIdx V i ≠ blockIdx V j) : False :=
  exclusion_disconnected' cellCap_vanishing H hdisc

end SkewCoframeRigidity.Unshifted
