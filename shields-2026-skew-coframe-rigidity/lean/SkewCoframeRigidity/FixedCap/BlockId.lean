/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.TopStep

/-!
# The block quantity as a splice

Formalizes the identification in the proof of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex` of the part of the derivative of the right coframe on the
columns of the next strict block `E` with the numerator `K_E ◁ E` (`sc:fcp-numerator-flags`,
`sc:fcp-recursive-cap`).  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- `E` is the block of the proper indices `q, …, q + m0` of `D`, translated by `b0`. -/
structure BlockRel (D : BetaDiagram (n + 1)) (q m0 : ℕ) (E : BetaDiagram (m0 + 1)) (b0 : ℤ) :
    Prop where
  hr : q + m0 + 1 ≤ n
  row : ∀ i : Fin (m0 + 1), E.row i + b0 = D.row ⟨q + 1 + i.val, by have := hr; omega⟩
  col : ∀ i : Fin (m0 + 1), E.col i + b0 = D.col ⟨q + i.val, by have := hr; omega⟩

section Rel

variable {D : BetaDiagram (n + 1)} {q m0 : ℕ} {E : BetaDiagram (m0 + 1)} {b0 : ℤ}
  (hD : IsNorm D) (hE : IsNorm E) (hrel : BlockRel D q m0 E b0)

include hD hE hrel

theorem BlockRel.b0_eq : b0 = D.col ⟨q + m0, by have := hrel.hr; omega⟩ := by
  have h := hrel.col (Fin.last m0)
  have h0 : E.col (Fin.last m0) = 0 := hE
  simp only [Fin.val_last] at h
  omega

theorem BlockRel.b0_nonneg : 0 ≤ b0 := by
  have h := hrel.b0_eq hD hE
  have := col_nonneg D hD ⟨q + m0, by have := hrel.hr; omega⟩
  omega

theorem BlockRel.colPos_eq (j : Fin m0) :
    colPos D ⟨q + j.val, by have := hrel.hr; omega⟩ = b0.toNat + colPos E j := by
  have h1 := hrel.col j.castSucc
  have h2 := colPos_cast_of_norm hE j
  have h3 := colPos_cast_of_norm hD ⟨q + j.val, by have := hrel.hr; omega⟩
  have h4 := hrel.b0_nonneg hD hE
  have h5 : D.col (⟨q + j.val, by have := hrel.hr; omega⟩ : Fin n).castSucc =
      D.col ⟨q + (j.castSucc).val, by have := hrel.hr; omega⟩ := rfl
  have h6 : E.col j.castSucc = E.col (Fin.castSucc j) := rfl
  omega

theorem BlockRel.colPos_last :
    colPos D ⟨q + m0, by have := hrel.hr; omega⟩ = b0.toNat := by
  have h3 := colPos_cast_of_norm hD ⟨q + m0, by have := hrel.hr; omega⟩
  have h4 := hrel.b0_eq hD hE
  have h5 := hrel.b0_nonneg hD hE
  have h6 : D.col (⟨q + m0, by have := hrel.hr; omega⟩ : Fin n).castSucc =
      D.col ⟨q + m0, by have := hrel.hr; omega⟩ := rfl
  omega

theorem BlockRel.rowPos_eq (i : Fin (m0 + 1)) :
    rowPos D ⟨q + i.val, by have := hrel.hr; omega⟩ = b0.toNat + (E.row i).toNat := by
  have h1 := hrel.row i
  have h2 := rowPos_cast D ⟨q + i.val, by have := hrel.hr; omega⟩
  have h0 : D.col (Fin.last n) = 0 := hD
  have h3 : D.row (⟨q + i.val, by have := hrel.hr; omega⟩ : Fin n).succ =
      D.row ⟨q + 1 + i.val, by have := hrel.hr; omega⟩ := by
    congr 1; apply Fin.ext; simp; omega
  have h4 := hrel.b0_nonneg hD hE
  have h5 : 0 ≤ E.row i := by
    have := E.row_nonempty i
    have : E.col (Fin.last m0) ≤ E.col i := E.col_strictAnti.antitone (Fin.le_last i)
    have h0' : E.col (Fin.last m0) = 0 := hE
    omega
  omega

theorem BlockRel.span_add :
    span E + b0.toNat = (D.row ⟨q + 1, by have := hrel.hr; omega⟩).toNat := by
  have h1 := hrel.row 0
  have h4 := hrel.b0_nonneg hD hE
  have h5 := span_eq_of_norm E hE
  have h6 : 0 ≤ E.row 0 := by
    have := E.row_nonempty 0
    have : E.col (Fin.last m0) ≤ E.col 0 := E.col_strictAnti.antitone (Fin.le_last 0)
    have h0' : E.col (Fin.last m0) = 0 := hE
    omega
  simp only [Fin.val_zero, add_zero] at h1
  omega

end Rel

theorem cohSchur_ne_zero {m : ℕ} (D : BetaDiagram m) : cohSchur D ≠ 0 := by
  intro h
  have := physSpec_schurOf D
  have h2 : cohSchur D = schurOf (MvPolynomial.X : ℕ → CohRing) D := rfl
  rw [← h2, h, map_zero] at this
  exact D.schur_ne_zero (physInclude_injective (by rw [← this, map_zero]))

theorem schurOf_cohLetters_ne_zero {m : ℕ} (D : BetaDiagram m) : schurOf cohLetters D ≠ 0 := by
  rw [← algebraMap_cohSchur]
  exact (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 (cohSchur_ne_zero D)

theorem cornerOf_cohLetters_ne_zero {m : ℕ} {D : BetaDiagram (m + 1)} (hD : D.Connected) :
    cornerOf cohLetters D ≠ 0 := by
  unfold cornerOf
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (properDet_cohLetters_ne_zero hD)

/-- The top quotient of a connected diagram: `[z^M] H G = s / κ`. -/
theorem coeff_span_coframe {m : ℕ} {D : BetaDiagram (m + 1)} (hD : D.Connected) :
    PowerSeries.coeff (span D) (letterSeries * (coframe D : PowerSeries CohField)) *
      cornerOf cohLetters D = schurOf cohLetters D := by
  have := schurOf_eq_cornerOf_mul_topQuotientOf cohLetters D (properDet_cohLetters_ne_zero hD)
  rw [this, mul_comm]
  rfl

theorem rowPos_lt_of_lt {D : BetaDiagram (n + 1)} (hD : IsNorm D) {q t : ℕ} (hq : q < n)
    (ht : D.row ⟨q + 1, by omega⟩ = t) (i : Fin n) (hi : q < i.val) : rowPos D i < t := by
  have h1 := D.row_strictAnti (show (⟨q + 1, by omega⟩ : Fin (n + 1)) < i.succ from by
    rw [Fin.lt_def]; simp; omega)
  have h2 := rowPos_cast D i
  have h0 : D.col (Fin.last n) = 0 := hD
  omega

theorem rowPos_eq_of_row {D : BetaDiagram (n + 1)} (hD : IsNorm D) {q t : ℕ} (hq : q < n)
    (ht : D.row ⟨q + 1, by omega⟩ = t) : rowPos D ⟨q, hq⟩ = t := by
  have h2 := rowPos_cast D ⟨q, hq⟩
  have h0 : D.col (Fin.last n) = 0 := hD
  have h3 : D.row (⟨q, hq⟩ : Fin n).succ = D.row ⟨q + 1, by omega⟩ := rfl
  omega

/-- **The block quantity is the numerator `K_E ◁ E` over the denominator `s_E`.** -/
theorem betaOf_block {q m0 : ℕ} {b0 : ℤ} {t : ℕ} {hq : q ≤ n} {K : BetaDiagram (q + 1)}
    (hKc : K.Connected) (hKn : IsNorm K) {D : BetaDiagram (n + 1)} (hDc : D.Connected)
    (hD : IsNorm D) (hm : CapMatches D hq (t : ℤ) K) {E : BetaDiagram (m0 + 1)} (hEn : IsNorm E)
    (hEc : E.Connected) (hrel : BlockRel D q m0 E b0) (hcq : CutAt D q)
    (hcr : CutAt D (q + m0 + 1))
    (ht : D.row ⟨q + 1, by have := hrel.hr; omega⟩ = t) :
    betaOf K D t * (cornerOf cohLetters K * schurOf cohLetters E) =
      -schurOf cohLetters (splice K E hKn hEn) := by
  classical
  have hrn := hrel.hr
  have hb0 := hrel.b0_nonneg hD hEn
  set b0n := b0.toNat with hb0n
  have hqn : q < n := by omega
  set κE := cornerOf cohLetters E with hκE
  set sE := schurOf cohLetters E with hsE
  have hκne : κE ≠ 0 := cornerOf_cohLetters_ne_zero hEc
  have hsne : sE ≠ 0 := schurOf_cohLetters_ne_zero E
  have hκK : cornerOf cohLetters K ≠ 0 := cornerOf_cohLetters_ne_zero hKc
  have hq' := coeff_span_coframe hEc
  rw [← hκE, ← hsE] at hq'
  set a : CohField := -(κE / sE) with ha
  set G : PowerSeries CohField := (coframe E : PowerSeries CohField) with hG
  set Γ : PowerSeries CohField := PowerSeries.C a * (PowerSeries.X ^ b0n * G) with hΓ
  -- the coordinates of the derivative beyond the block vanish
  have hW0 : ∀ j : Fin n, q + m0 + 1 ≤ j.val →
      PowerSeries.coeff (colPos D j) (dCoframe t D) = 0 := by
    refine trail_zero_coords hDc hcr (suppCols_dCoframe t D) fun i hi => ?_
    rw [coeff_rowPos_dCoframe hDc, if_neg (not_le.2 (rowPos_lt_of_lt hD hqn ht i (by omega))),
      neg_zero]
  have hMid := suppCols_sub_mask (D := D) q (q + m0 + 1)
    ((suppCols_dCoframe t D)) hW0
  -- support of Γ
  have hΓs : SuppCols D (fun j => q ≤ j.val ∧ j.val < q + m0 + 1) Γ := by
    intro s hs
    rw [hΓ, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hsb : b0n ≤ s
    · rw [if_pos hsb, hG, Polynomial.coeff_coe]
      by_cases h0 : s - b0n = 0
      · exfalso
        refine hs ⟨q + m0, by omega⟩ ⟨by simp, by simp⟩ ?_
        rw [hrel.colPos_last hD hEn]; omega
      · have : (coframe E).coeff (s - b0n) = 0 := by
          unfold coframe coframeOf
          refine uniPoly_coeff_of_ne _ _ _ (Nat.pos_of_ne_zero h0) fun j hj => ?_
          refine hs ⟨q + j.val, by omega⟩ ⟨by simp, by simp⟩ ?_
          rw [hrel.colPos_eq hD hEn j]; omega
        rw [this, mul_zero]
    · rw [if_neg hsb, mul_zero]
  -- the rows of Γ
  have hΓr : ∀ i : Fin n, q ≤ i.val → i.val < q + m0 + 1 →
      PowerSeries.coeff (rowPos D i) (letterSeries * Γ) =
        -(if t ≤ rowPos D i then (coframe D).coeff (rowPos D i - t) else 0) := by
    intro i hi1 hi2
    have hi : i = ⟨q + (i.val - q), by omega⟩ := Fin.ext (by simp; omega)
    set i'' : Fin (m0 + 1) := ⟨i.val - q, by omega⟩ with hi''
    have hrp := hrel.rowPos_eq hD hEn i''
    have hrp' : rowPos D i = b0n + (E.row i'').toNat := by
      rw [hi]; exact hrp
    have hmul : letterSeries * Γ =
        PowerSeries.C a * (PowerSeries.X ^ b0n * (letterSeries * G)) := by
      rw [hΓ]; ring
    rw [hmul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
      show rowPos D i - b0n = (E.row i'').toNat by omega]
    by_cases h0 : i.val = q
    · have hi0 : i'' = 0 := Fin.ext (by simp [hi'']; omega)
      have hi' : i = ⟨q, hqn⟩ := Fin.ext h0
      have hrq := rowPos_eq_of_row hD hqn ht
      rw [hi0, if_pos (by rw [hi', hrq]), hi', hrq, Nat.sub_self, coframe_coeff_zero]
      have := span_eq_of_norm E hEn
      rw [← this, ha]
      field_simp
      linear_combination (-1 : CohField) * hq'
    · have hlt := rowPos_lt_of_lt hD hqn ht i (by omega)
      rw [if_neg (not_le.2 hlt), neg_zero]
      obtain ⟨j, hj⟩ : ∃ j : Fin m0, i'' = j.succ := by
        refine ⟨⟨i.val - q - 1, by omega⟩, Fin.ext ?_⟩
        simp [hi'']; omega
      have hj0 : D.col (Fin.last n) = 0 := hD
      have h1 := coeff_rowPos_coframe hEc j
      have h2 : rowPos E j = (E.row i'').toNat := by
        have := rowPos_cast E j
        have h0' : E.col (Fin.last m0) = 0 := hEn
        rw [hj]; omega
      rw [← h2, hG, h1, mul_zero]
  have hMidΓ : dCoframe t D - maskCols D (fun j => j.val < q) (dCoframe t D) = Γ := by
    refine mid_unique hDc hcq hcr hMid hΓs fun i hi1 hi2 => ?_
    rw [hΓr i hi1 hi2]
    exact (by
      rw [mid_rows hDc hcq t i hi1])
  unfold betaOf
  rw [hMidΓ]
  have hspK : span K + t = span D := by
    have h1 := hm.1 0
    have h1' : D.row (Fin.castLE (by omega : q + 1 ≤ n + 1) 0) = D.row 0 := rfl
    have h2 := span_eq_of_norm K hKn
    have h3 := span_eq_of_norm D hD
    have h4 := top_pos D hD
    have h5 : D.row 0 > D.row ⟨q + 1, by omega⟩ := D.row_strictAnti (by
      rw [Fin.lt_def]; simp)
    omega
  have hspE := hrel.span_add hD hEn
  rw [ht, Int.toNat_natCast] at hspE
  have hsplice := splice_schur_cohLetters K hKn hKc E hEn hEc
  have hspan : span E + span K = span D - b0n := by omega
  rw [hspan] at hsplice
  have hmul : letterSeries * ((leftCoframe K : CohField[X]) : PowerSeries CohField) * Γ =
      PowerSeries.C a * (PowerSeries.X ^ b0n *
        (letterSeries * (((leftCoframe K * coframe E : CohField[X]) : PowerSeries CohField)))) := by
    rw [hΓ, Polynomial.coe_mul]; ring
  rw [hmul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
  rw [hsplice, ha]
  field_simp
  rw [← hκE]
  ring

/-- **No block.**  If every row beyond the cut lies below `τ`, the block quantity vanishes. -/
theorem betaOf_none {q : ℕ} {K : BetaDiagram (q + 1)} {D : BetaDiagram (n + 1)}
    (hDc : D.Connected) {τ : ℕ} (hcq : CutAt D q) (hlow : ∀ i : Fin n, q ≤ i.val → rowPos D i < τ) :
    betaOf K D τ = 0 := by
  have hW0 : ∀ j : Fin n, q ≤ j.val → PowerSeries.coeff (colPos D j) (dCoframe τ D) = 0 := by
    refine trail_zero_coords hDc hcq (suppCols_dCoframe τ D) fun i hi => ?_
    rw [coeff_rowPos_dCoframe hDc, if_neg (not_le.2 (hlow i hi)), neg_zero]
  have hMid := suppCols_sub_mask (D := D) q q (suppCols_dCoframe τ D) hW0
  have h0 : dCoframe τ D - maskCols D (fun j => j.val < q) (dCoframe τ D) = 0 := by
    ext s
    rw [hMid s (fun j hj _ => by omega)]
    simp
  unfold betaOf
  rw [h0]
  simp

end SkewCoframeRigidity.FixedCap
