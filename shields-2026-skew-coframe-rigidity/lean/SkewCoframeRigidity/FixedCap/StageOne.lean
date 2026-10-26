/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.LeftCoframe
import SkewCoframeRigidity.FixedCap.LetterField

/-!
# The prefix of zero coefficients

Formalizes `sc:fcp-prefix-zero` in the proof of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex`: if the coefficients of the right coframes of `B`, `B'`
and of the left coframe of `K` use only letters below `m`, the second observation forces
`G_B - G_{B'}` to vanish through degree `c + a - m`.  Sorry-free, modulo the statements of
`Coframe` on which `Reduction` rests.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {k : ℕ}

section Membership

variable {K : Type*} [Field K] (S : Subfield K)

theorem det_mem_subfield {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ S) :
    A.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subfield.sum_mem _ fun σ _ => ?_
  have : (Equiv.Perm.sign σ : ℤ) • ∏ i, A (σ i) i =
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • ∏ i, A (σ i) i := rfl
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h] <;>
    simp [Subfield.prod_mem, hA, Subfield.neg_mem, Subfield.prod_mem _ fun i _ => hA _ _]

theorem inv_entry_mem_subfield {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ S)
    (i j : Fin n) : A⁻¹ i j ∈ S := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  refine S.mul_mem (S.inv_mem (det_mem_subfield S A hA)) (det_mem_subfield S _ fun p q => ?_)
  by_cases h : p = j
  · subst h
    by_cases hq : q = i <;> simp [hq, S.one_mem, S.zero_mem]
  · simp [Matrix.updateRow_ne h, hA]

end Membership

section Ceiling

variable {m : ℕ}

theorem letterOf_mem {e : ℤ} (he : e < m) : letterOf cohLetters e ∈ letterField m := by
  by_cases h0 : e < 0
  · rw [letterOf_neg_eq _ h0]; exact Subfield.zero_mem _
  · rw [letterOf_nonneg_eq _ (not_lt.1 h0)]
    exact cohLetters_mem_letterField (by omega)

/-- All letters in the matrix of a diagram lie below `m`. -/
theorem properMatrix_mem {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hm : ∀ i : Fin n, D.row i.succ < m) (i j : Fin n) :
    properMatrixOf cohLetters D i j ∈ letterField m := by
  have h0 : D.col (Fin.last n) = 0 := hD
  have := col_nonneg D hD j.castSucc
  refine letterOf_mem ?_
  change D.row i.succ - D.col j.castSucc < (m : ℤ)
  have := hm i
  omega

theorem topVec_mem {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (hm : ∀ i : Fin n, D.row i.succ < m) (i : Fin n) :
    topVecOf cohLetters D i ∈ letterField m := by
  have h0 : D.col (Fin.last n) = 0 := hD
  refine letterOf_mem ?_
  change D.row i.succ - D.col (Fin.last n) < (m : ℤ)
  have := hm i
  omega

theorem coframe_coeff_mem {b : ℕ} (B : BetaDiagram (b + 1)) (hB : IsNorm B)
    (hm : ∀ i : Fin b, B.row i.succ < m) (s : ℕ) : (coframe B).coeff s ∈ letterField m := by
  have hg : ∀ j, coframeVecOf cohLetters B j ∈ letterField m := by
    intro j
    simp only [coframeVecOf, Pi.neg_apply, Matrix.mulVec, dotProduct]
    refine Subfield.neg_mem _ (Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ ?_ ?_)
    · exact inv_entry_mem_subfield _ _ (properMatrix_mem B hB hm) j i
    · exact topVec_mem B hB hm i
  unfold coframe coframeOf
  rw [Polynomial.coeff_add, Polynomial.finset_sum_coeff]
  refine Subfield.add_mem _ ?_ (Subfield.sum_mem _ fun j _ => ?_)
  · rw [Polynomial.coeff_one]; split_ifs
    · exact Subfield.one_mem _
    · exact Subfield.zero_mem _
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs
    · rw [mul_one]; exact hg j
    · rw [mul_zero]; exact Subfield.zero_mem _

theorem leftCoframe_coeff_mem (K : BetaDiagram (k + 1)) (hK : IsNorm K) (hm : K.row 0 ≤ m)
    (s : ℕ) : (leftCoframe K).coeff s ∈ letterField m := by
  have h0 : K.col (Fin.last k) = 0 := hK
  have hT : ∀ i j, properMatrixOf cohLetters K i j ∈ letterField m := by
    intro i j
    have h1 := K.row_strictAnti (Fin.succ_pos i)
    have := col_nonneg K hK j.castSucc
    refine letterOf_mem ?_
    change K.row i.succ - K.col j.castSucc < (m : ℤ)
    omega
  have hTop : ∀ j, topRowOf cohLetters K j ∈ letterField m := by
    intro j
    have := col_pos_of_ne_last K hK j.castSucc (Fin.castSucc_lt_last j).ne
    refine letterOf_mem ?_
    change K.row 0 - K.col j.castSucc < (m : ℤ)
    omega
  have hw : ∀ j, leftVecOf cohLetters K j ∈ letterField m := by
    intro j
    simp only [leftVecOf, Pi.neg_apply, Matrix.vecMul, dotProduct]
    refine Subfield.neg_mem _ (Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ ?_ ?_)
    · exact hTop i
    · exact inv_entry_mem_subfield _ _ hT i j
  unfold leftCoframe leftCoframeOf capPoly
  rw [Polynomial.coeff_add, Polynomial.finset_sum_coeff]
  refine Subfield.add_mem _ ?_ (Subfield.sum_mem _ fun j _ => ?_)
  · rw [Polynomial.coeff_one]; split_ifs
    · exact Subfield.one_mem _
    · exact Subfield.zero_mem _
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs
    · rw [mul_one]; exact hw j
    · rw [mul_zero]; exact Subfield.zero_mem _

end Ceiling

theorem leftCoframe_coeff_zero (K : BetaDiagram (k + 1)) : (leftCoframe K).coeff 0 = 1 := by
  unfold leftCoframe leftCoframeOf capPoly
  rw [Polynomial.coeff_add, Polynomial.finset_sum_coeff, Polynomial.coeff_one_zero]
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  have h1 : leftExp K j ≠ 0 := by
    have := K.row_strictAnti (Fin.succ_pos j)
    unfold leftExp
    omega
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm h1), mul_zero]

/-- **The prefix of zero coefficients** (`sc:fcp-prefix-zero`): if the coefficients of both right
coframes and of the left coframe use only letters below `m`, the second observation forces the
two right coframes to agree through degree `c + a - m`. -/
theorem prefix_zero {b : ℕ} (K : BetaDiagram (k + 1)) (hK : IsNorm K)
    (B B' : BetaDiagram (b + 1)) (hB : IsNorm B) (hB' : IsNorm B') (m : ℕ)
    (hKm : K.row 0 ≤ m) (hBm : ∀ i : Fin b, B.row i.succ < m)
    (hB'm : ∀ i : Fin b, B'.row i.succ < m)
    (hO2 : PowerSeries.coeff (span B + span K) (letterSeries *
      ((leftCoframe K * (coframe B - coframe B') : CohField[X]) : PowerSeries CohField)) = 0)
    (i : ℕ) (hi : i + m ≤ span B + span K) : (coframe B - coframe B').coeff i = 0 := by
  set Q : CohField[X] := coframe B - coframe B' with hQ
  set V : CohField[X] := leftCoframe K * Q with hV
  have hQm : ∀ s, Q.coeff s ∈ letterField m := fun s => by
    rw [hQ, Polynomial.coeff_sub]
    exact Subfield.sub_mem _ (coframe_coeff_mem B hB hBm s) (coframe_coeff_mem B' hB' hB'm s)
  have hVm : ∀ s, V.coeff s ∈ letterField m := fun s => by
    rw [hV, Polynomial.coeff_mul]
    exact Subfield.sum_mem _ fun p _ => Subfield.mul_mem _
      (leftCoframe_coeff_mem K hK hKm _) (hQm _)
  set N := span B + span K with hN
  have hmN : m ≤ N := by omega
  have hsum : PowerSeries.coeff N (letterSeries * (V : PowerSeries CohField)) =
      ∑ j ∈ Finset.range m, cohLetters j * V.coeff (N - j) +
        ∑ j ∈ Finset.Icc m N, cohLetters j * V.coeff (N - j) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Finset.sum_range_add_sum_Ico _ (show m ≤ N + 1 by omega)]
    have : Finset.Ico m (N + 1) = Finset.Icc m N := by ext; simp
    rw [this]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>
      simp [letterSeries, seriesOf, Polynomial.coeff_coe]
  have hind := tail_letters_independent m N (fun j => V.coeff (N - j))
    (∑ j ∈ Finset.range m, cohLetters j * V.coeff (N - j)) (fun j => hVm _)
    (Subfield.sum_mem _ fun j hj => Subfield.mul_mem _
      (cohLetters_mem_letterField (Finset.mem_range.1 hj)) (hVm _))
    (by rw [← hsum]; exact hO2)
  have hVz : ∀ t, t + m ≤ N → V.coeff t = 0 := by
    intro t ht
    have := hind.2 (N - t) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    simpa [show N - (N - t) = t by omega] using this
  have hunit : IsUnit (leftCoframe K : PowerSeries CohField) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : PowerSeries.constantCoeff (leftCoframe K : PowerSeries CohField) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        leftCoframe_coeff_zero]
    rw [this]; exact isUnit_one
  have hdvd : (PowerSeries.X : PowerSeries CohField) ^ (N - m + 1) ∣ (Q : PowerSeries CohField) := by
    have h1 : (PowerSeries.X : PowerSeries CohField) ^ (N - m + 1) ∣ (V : PowerSeries CohField) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro t ht
      rw [Polynomial.coeff_coe]
      exact hVz t (by omega)
    rw [hV, Polynomial.coe_mul] at h1
    exact (hunit.dvd_mul_left).1 h1
  rw [PowerSeries.X_pow_dvd_iff] at hdvd
  have := hdvd i (by omega)
  rwa [Polynomial.coeff_coe] at this

end SkewCoframeRigidity.FixedCap
