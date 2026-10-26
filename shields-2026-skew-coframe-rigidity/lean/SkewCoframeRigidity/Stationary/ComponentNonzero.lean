/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.AtlasPolynomials
import SkewCoframeRigidity.Stationary.NonnegSeries

/-!
# Nonvanishing of the component remainder

Formalizes the nonvanishing of `α = [P^p g^{1-p}]_L` in
`shields-2026-skew-coframe-rigidity.tex`, `sc:component-remainder`.  The atlas coordinates are
algebraically independent, so it suffices to exhibit one rational specialization with a nonzero
value.  For a diagram with native columns, the specialization `g = 1 - z^b` with `b` the least
native column and every available numerator coefficient one gives coefficient at least one,
because `g^{-1}` has nonnegative coefficients; for a row the numerator `1 + z + ⋯ + z^{L-1}`
has `P_1 P_{L-1}` among the terms of `[P^p]_L`.  The argument is positivity rather than the
paper's binomial coefficient, and needs no case on `j`.  Sorry-free.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The specialization: every available numerator coordinate is one, and the native
coordinate at the column position `b` is `-1`. -/
noncomputable def vSpec (D : BetaDiagram (n + 1)) (b : ℕ) : AtlasIdx D → ℚ
  | none => 1
  | some (Sum.inl j) => if colPos D j = b then -1 else 0
  | some (Sum.inr _) => 1

theorem specEval_pcoord (D : BetaDiagram (n + 1)) (b i : ℕ) :
    specEval D (vSpec D b) (pcoord D i) =
      if i = 0 ∨ (0 < i ∧ i < span D ∧ i ∉ rowSet D) then 1 else 0 := by
  unfold pcoord specEval
  by_cases h0 : i = 0
  · simp [h0, vSpec]
  · by_cases hf : 0 < i ∧ i < span D ∧ i ∉ rowSet D
    · simp [h0, hf, vSpec]
    · simp [h0, hf]

theorem coeff_Pv (D : BetaDiagram (n + 1)) (b i : ℕ) :
    ((Pm D).map (specEval D (vSpec D b))).coeff i =
      if i < span D ∧ (i = 0 ∨ (0 < i ∧ i ∉ rowSet D)) then 1 else 0 := by
  rw [Polynomial.coeff_map, Pm_coeff]
  by_cases hi : i < span D
  · rw [if_pos hi, specEval_pcoord]
    exact if_congr (by tauto) rfl rfl
  · rw [if_neg hi, map_zero, if_neg (by tauto)]

theorem nonneg_Pv (D : BetaDiagram (n + 1)) (b : ℕ) :
    NonnegSeries ((((Pm D).map (specEval D (vSpec D b))) : Polynomial ℚ) : PowerSeries ℚ) := by
  intro m
  rw [Polynomial.coeff_coe, coeff_Pv]
  split_ifs <;> norm_num

theorem coeff_Pv_zero (D : BetaDiagram (n + 1)) (b : ℕ) :
    1 ≤ ((Pm D).map (specEval D (vSpec D b))).coeff 0 := by
  rw [coeff_Pv, if_pos ⟨span_pos D, Or.inl rfl⟩]

/-- Multiplication by `1 - z^b` is inverted by the geometric series. -/
theorem geom_inv (b : ℕ) (hb : 0 < b) :
    (1 - PowerSeries.X ^ b : PowerSeries ℚ) * PowerSeries.mk (fun m => if b ∣ m then (1 : ℚ) else 0)
      = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  by_cases hm : m = 0
  · subst hm; simp [hb.ne']
  · by_cases hbm : b ≤ m
    · rw [if_pos hbm, PowerSeries.coeff_mk, if_neg hm]
      have : b ∣ m - b ↔ b ∣ m := by
        constructor
        · intro h; have := dvd_add h (dvd_refl b); rwa [Nat.sub_add_cancel hbm] at this
        · intro h; exact Nat.dvd_sub h (dvd_refl b)
      by_cases hd : b ∣ m
      · simp [hd, this.2 hd]
      · simp [hd, mt this.1 hd]
    · rw [if_neg hbm, if_neg hm]
      have : ¬ b ∣ m := fun h => hbm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h)
      simp [this]

theorem nonneg_geom (b : ℕ) :
    NonnegSeries (PowerSeries.mk (fun m => if b ∣ m then (1 : ℚ) else 0)) := by
  intro m
  rw [PowerSeries.coeff_mk]
  split_ifs <;> norm_num

/-- The component remainder of a one-row diagram is nonzero. -/
theorem remainder_ne_zero_row {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : n = 0)
    (hL : 2 ≤ span D) {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.coeff (span D)
      ((numerator D : PowerSeries CohField) ^ p *
        ((coframe D : PowerSeries CohField)⁻¹) ^ (p - 1)) ≠ 0 := by
  subst hn
  have hrow : rowSet D = ∅ := by simp [rowSet]
  refine remainder_ne_zero_of_specialization hD p (vSpec D 0) 1 ?_ ?_
  · simp [Gm]
  · rw [one_pow, mul_one]
    set Pv : PowerSeries ℚ := (((Pm D).map (specEval D (vSpec D 0)) : Polynomial ℚ) :
      PowerSeries ℚ) with hPv
    have hnn : NonnegSeries Pv := nonneg_Pv D 0
    have hc : ∀ i, i < span D → Pv.coeff i = 1 := by
      intro i hi
      rw [hPv, Polynomial.coeff_coe, coeff_Pv, if_pos ⟨hi, by rw [hrow]; simp; omega⟩]
    have h0 : 1 ≤ Pv.coeff 0 := by rw [hc 0 (by omega)]
    have h1 : 1 ≤ Pv.coeff (span D - 1) := by rw [hc _ (by omega)]
    have hq := one_le_coeff_pow hnn h0 h1 (p - 1) (by omega)
    have hmul := coeff_mul_ge hnn (hnn.pow (p - 1)) 1 (span D - 1)
    rw [show 1 + (span D - 1) = span D by omega, ← pow_succ',
      show p - 1 + 1 = p by omega] at hmul
    rw [hc 1 (by omega)] at hmul
    intro h; rw [h] at hmul; linarith

/-- Every row position is at least the least column position. -/
theorem least_col_le_rowPos {m : ℕ} (D : BetaDiagram (m + 1 + 1)) (hD : D.Connected)
    (i : Fin (m + 1)) : colPos D (Fin.last m) ≤ rowPos D i := by
  have h1 : D.col (Fin.last m).castSucc ≤ D.row (Fin.last (m + 1)) := by
    have := hD.2 ⟨m, by omega⟩ (by simp)
    exact this
  have h2 : D.row (Fin.last (m + 1)) ≤ D.row i.succ :=
    D.row_strictAnti.antitone (Fin.le_last _)
  have h3 := colPos_cast D (Fin.last m)
  have h4 := rowPos_cast D i
  omega

theorem Gm_eval_spec {m : ℕ} (D : BetaDiagram (m + 1 + 1)) :
    (Gm D).map (specEval D (vSpec D (colPos D (Fin.last m)))) =
      1 - (X : ℚ[X]) ^ colPos D (Fin.last m) := by
  unfold Gm
  rw [Polynomial.map_add, Polynomial.map_one, Polynomial.map_sum]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp [specEval, vSpec]
    ring
  · intro j _ hj
    have : colPos D j ≠ colPos D (Fin.last m) := fun h => hj (colPos_injective D h)
    simp [specEval, vSpec, this]
  · simp

/-- The component remainder of a diagram with native columns is nonzero. -/
theorem remainder_ne_zero_cols {m : ℕ} {D : BetaDiagram (m + 1 + 1)} (hD : D.Connected)
    {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.coeff (span D)
      ((numerator D : PowerSeries CohField) ^ p *
        ((coframe D : PowerSeries CohField)⁻¹) ^ (p - 1)) ≠ 0 := by
  set b := colPos D (Fin.last m) with hb
  have hb0 : 0 < b := colPos_pos D _
  have hbL : b < span D := colPos_lt_span D _
  refine remainder_ne_zero_of_specialization hD p (vSpec D b)
    (PowerSeries.mk (fun k => if b ∣ k then (1 : ℚ) else 0)) ?_ ?_
  · rw [Gm_eval_spec, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow,
      Polynomial.coe_X]
    exact geom_inv b hb0
  · set Ginf : PowerSeries ℚ := PowerSeries.mk (fun k => if b ∣ k then (1 : ℚ) else 0) with hG
    set Pv : PowerSeries ℚ := (((Pm D).map (specEval D (vSpec D b)) : Polynomial ℚ) :
      PowerSeries ℚ) with hPv
    have hnnP : NonnegSeries Pv := nonneg_Pv D b
    have hnnG : NonnegSeries Ginf := nonneg_geom b
    set r := span D % b with hr
    have hrb : r < b := Nat.mod_lt _ hb0
    have hdiv : b ∣ span D - r := by
      have := Nat.div_add_mod (span D) b
      exact ⟨span D / b, by rw [hr]; omega⟩
    have hPr : 1 ≤ Pv.coeff r := by
      rw [hPv, Polynomial.coeff_coe, coeff_Pv, if_pos]
      refine ⟨by omega, ?_⟩
      by_cases hr0 : r = 0
      · exact Or.inl hr0
      · refine Or.inr ⟨Nat.pos_of_ne_zero hr0, fun hmem => ?_⟩
        simp only [rowSet, Finset.mem_image, Finset.mem_univ, true_and] at hmem
        obtain ⟨i, hi⟩ := hmem
        have := least_col_le_rowPos D hD i
        omega
    have hP0 : 1 ≤ Pv.coeff 0 := by
      rw [hPv, Polynomial.coeff_coe]; exact coeff_Pv_zero D b
    have hG0 : 1 ≤ Ginf.coeff 0 := by rw [hG, PowerSeries.coeff_mk]; simp
    have hGr : 1 ≤ Ginf.coeff (span D - r) := by rw [hG, PowerSeries.coeff_mk, if_pos hdiv]
    have h1 := one_le_coeff_pow hnnP hP0 hPr p (by omega)
    have h2 := one_le_coeff_pow hnnG hG0 hGr (p - 1) (by omega)
    have hmul := coeff_mul_ge (hnnP.pow p) (hnnG.pow (p - 1)) r (span D - r)
    rw [show r + (span D - r) = span D by omega] at hmul
    intro h; rw [h] at hmul; nlinarith

end SkewCoframeRigidity.Coframe
