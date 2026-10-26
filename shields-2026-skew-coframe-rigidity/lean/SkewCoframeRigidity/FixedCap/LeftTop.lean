/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.BlockId
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The top quotient of the left coframe

For a connected normalized diagram `K`, the complete left coframe satisfies
`s_K = κ_K [z^a] H C_K` (the left counterpart of `sc:atlas`).  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

open Matrix in
/-- Eliminating the first row against the others factors the determinant. -/
theorem det_eq_of_eliminated_row {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (t : Fin n → R)
    (ht : ∀ j : Fin n, M 0 j.castSucc + ∑ i, t i * M i.succ j.castSucc = 0) :
    M.det = (-1) ^ n * (M.submatrix Fin.succ Fin.castSucc).det *
      (M 0 (Fin.last n) + ∑ i, t i * M i.succ (Fin.last n)) := by
  classical
  let s : Fin (n + 1) → R := Fin.cons 1 t
  have hdet := Matrix.det_updateRow_sum M 0 s
  have hs0 : s 0 = 1 := rfl
  rw [hs0, one_smul] at hdet
  have hrow : ∀ k, (∑ i, s i • M i) k = M 0 k + ∑ i : Fin n, t i * M i.succ k := by
    intro k
    rw [Finset.sum_apply, Fin.sum_univ_succ]
    simp [s]
  have hsc : M.det = (M.updateRow 0 (∑ i, s i • M i)).det := hdet.symm
  rw [hsc, Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin n, (M.updateRow 0 (∑ i, s i • M i)) 0 j.castSucc = 0 := by
    intro j
    simp only [Matrix.updateRow_apply, ite_true]
    rw [hrow]; exact ht j
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hsub : ((M.updateRow 0 (∑ i, s i • M i)).submatrix Fin.succ
      (Fin.last n).succAbove) = M.submatrix Fin.succ Fin.castSucc := by
    ext i j
    simp [Fin.succAbove_last]
  rw [hsub]
  simp only [Matrix.updateRow_apply, ite_true, hrow, Fin.val_last]
  ring

variable {k : ℕ}

/-- **The top quotient of the left coframe**: `[z^a] H C_K = s_K / κ_K`. -/
theorem coeff_span_leftCoframe {K : BetaDiagram (k + 1)} (hKc : K.Connected) (hK : IsNorm K) :
    PowerSeries.coeff (span K) (letterSeries *
      ((leftCoframe K : CohField[X]) : PowerSeries CohField)) * cornerOf cohLetters K =
      schurOf cohLetters K := by
  have hlvP : leftVecOf cohLetters K ᵥ* properMatrixOf cohLetters K = -topRowOf cohLetters K :=
    leftVecOf_vecMul cohLetters K (isUnit_iff_ne_zero.2 (properDet_cohLetters_ne_zero hKc))
  have hel := det_eq_of_eliminated_row (fullMatrixOf cohLetters K) (leftVecOf cohLetters K) (by
    intro j
    have := congrFun hlvP j
    simp only [Matrix.vecMul, dotProduct, Pi.neg_apply] at this
    simp only [fullMatrixOf, Matrix.of_apply]
    have e : topRowOf cohLetters K j = letterOf cohLetters (K.row 0 - K.col j.castSucc) := rfl
    rw [← e]
    have e2 : ∀ i : Fin k, leftVecOf cohLetters K i * letterOf cohLetters
        (K.row i.succ - K.col j.castSucc) = leftVecOf cohLetters K i *
          properMatrixOf cohLetters K i j := fun i => rfl
    simp only [e2]
    rw [this]; ring)
  have hsub : (fullMatrixOf cohLetters K).submatrix Fin.succ Fin.castSucc =
      properMatrixOf cohLetters K := rfl
  unfold schurOf
  rw [hel, hsub]
  have hcoef := coeff_mk_mul_capPoly cohLetters (leftVecOf cohLetters K) (leftExp K) (span K)
  have hspan := span_eq_of_norm K hK
  have h0 : K.col (Fin.last k) = 0 := hK
  have hpos := top_pos K hK
  have hcoeff : PowerSeries.coeff (span K) (letterSeries *
      ((leftCoframe K : CohField[X]) : PowerSeries CohField)) =
      cohLetters (span K) + ∑ i, leftVecOf cohLetters K i * cohLetters (K.row i.succ).toNat := by
    unfold leftCoframe leftCoframeOf
    rw [letterSeries, seriesOf, hcoef]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have h1 : K.row i.succ < K.row 0 := K.row_strictAnti (Fin.succ_pos i)
    have h2 : K.col (Fin.last k) ≤ K.col i.castSucc := K.col_strictAnti.antitone (Fin.le_last _)
    have h3 := K.row_nonempty i.succ
    have h4 : K.col (Fin.last k) ≤ K.col i.succ := K.col_strictAnti.antitone (Fin.le_last _)
    rw [letterOf_nonneg_eq _ (by unfold leftExp; omega)]
    congr 1
    unfold leftExp
    omega
  rw [hcoeff]
  unfold cornerOf
  have e1 : fullMatrixOf cohLetters K 0 (Fin.last k) = cohLetters (span K) := by
    simp only [fullMatrixOf, Matrix.of_apply]
    rw [letterOf_nonneg_eq _ (by omega)]
    rfl
  have e2 : ∀ i : Fin k, fullMatrixOf cohLetters K i.succ (Fin.last k) =
      cohLetters (K.row i.succ).toNat := fun i => by
    simp only [fullMatrixOf, Matrix.of_apply]
    have h3 := K.row_nonempty i.succ
    have h4 : K.col (Fin.last k) ≤ K.col i.succ := K.col_strictAnti.antitone (Fin.le_last _)
    rw [letterOf_nonneg_eq _ (by omega)]
    congr 1; omega
  rw [e1]
  simp only [e2]
  ring

variable {n : ℕ}

/-- **A unit block.**  If the next strict block is the true unit at `t`, the block quantity is
`-s_K / (κ_K ϑ)`. -/
theorem betaOf_unit {q : ℕ} {t : ℕ} {hq : q ≤ n} {K : BetaDiagram (q + 1)}
    (hKc : K.Connected) (hKn : IsNorm K) {D : BetaDiagram (n + 1)} (hDc : D.Connected)
    (hD : IsNorm D) (hm : CapMatches D hq (t : ℤ) K) (hqn : q < n) (hcq : CutAt D q)
    (hcr : CutAt D (q + 1)) (ht : D.row ⟨q + 1, by omega⟩ = t)
    (hu : D.col ⟨q, by omega⟩ = t) :
    betaOf K D t * (cornerOf cohLetters K * cohLetters 0) = -schurOf cohLetters K := by
  classical
  have hϑ : cohLetters 0 ≠ 0 := by
    unfold cohLetters
    exact (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2
      (MvPolynomial.X_ne_zero 0)
  have hκK : cornerOf cohLetters K ≠ 0 := cornerOf_cohLetters_ne_zero hKc
  set a : CohField := -(cohLetters 0)⁻¹ with ha
  set Γ : PowerSeries CohField := PowerSeries.C a * PowerSeries.X ^ t with hΓ
  have hcolq : colPos D ⟨q, hqn⟩ = t := by
    have h1 := colPos_cast_of_norm hD ⟨q, hqn⟩
    have h2 : D.col (⟨q, hqn⟩ : Fin n).castSucc = D.col ⟨q, by omega⟩ := rfl
    omega
  have hW0 : ∀ j : Fin n, q + 1 ≤ j.val →
      PowerSeries.coeff (colPos D j) (dCoframe t D) = 0 := by
    refine trail_zero_coords hDc hcr (suppCols_dCoframe t D) fun i hi => ?_
    rw [coeff_rowPos_dCoframe hDc, if_neg (not_le.2 (rowPos_lt_of_lt hD hqn ht i (by omega))),
      neg_zero]
  have hMid := suppCols_sub_mask (D := D) q (q + 1) (suppCols_dCoframe t D) hW0
  have hΓs : SuppCols D (fun j => q ≤ j.val ∧ j.val < q + 1) Γ := by
    intro s hs
    rw [hΓ, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    by_cases hst : s = t
    · exfalso
      exact hs ⟨q, hqn⟩ ⟨le_rfl, by simp⟩ (by rw [hcolq, hst])
    · rw [if_neg hst, mul_zero]
  have hΓr : ∀ i : Fin n, q ≤ i.val → i.val < q + 1 →
      PowerSeries.coeff (rowPos D i) (letterSeries * Γ) =
        -(if t ≤ rowPos D i then (coframe D).coeff (rowPos D i - t) else 0) := by
    intro i hi1 hi2
    have hi : i = ⟨q, hqn⟩ := Fin.ext (by simp only; omega)
    have hrq := rowPos_eq_of_row hD hqn ht
    rw [hi, hrq, if_pos le_rfl, Nat.sub_self, coframe_coeff_zero]
    have hmul : letterSeries * Γ = PowerSeries.C a * (PowerSeries.X ^ t * letterSeries) := by
      rw [hΓ]; ring
    rw [hmul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    have : PowerSeries.coeff 0 letterSeries = cohLetters 0 := by
      simp [letterSeries, seriesOf]
    rw [this, ha]
    field_simp
  have hMidΓ : dCoframe t D - maskCols D (fun j => j.val < q) (dCoframe t D) = Γ := by
    refine mid_unique hDc hcq hcr hMid hΓs fun i hi1 hi2 => ?_
    rw [hΓr i hi1 hi2, mid_rows hDc hcq t i hi1]
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
  have hmul : letterSeries * ((leftCoframe K : CohField[X]) : PowerSeries CohField) * Γ =
      PowerSeries.C a * (PowerSeries.X ^ t *
        (letterSeries * ((leftCoframe K : CohField[X]) : PowerSeries CohField))) := by
    rw [hΓ]; ring
  rw [hmul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    show span D - t = span K by omega]
  have := coeff_span_leftCoframe hKc hKn
  rw [ha]
  field_simp
  linear_combination (-1 : CohField) * this

end SkewCoframeRigidity.FixedCap
