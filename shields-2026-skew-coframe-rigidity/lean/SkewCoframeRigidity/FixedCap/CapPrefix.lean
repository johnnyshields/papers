/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.CapBuild
import SkewCoframeRigidity.FixedCap.StageOne

/-!
# The left coframe of the recursive cap kills the prefix

Formalizes the cancellation of the prefix in the descent of `sc:fixed-cap` of
`shields-2026-skew-coframe-rigidity.tex`.  If a diagram `D` has the cap `K` as its prefix (up to
the translation `t`), then `[z^c] H C_K U = 0` for every series `U` supported on the prefix
columns of `D`, where `C_K` is the complete left coframe of `K`.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The general coefficient of `H · U` for a series `U` on the column positions. -/
theorem coeff_H_mul_supp (D : BetaDiagram (n + 1)) {U : PowerSeries CohField}
    (hU : SuppCols D (fun _ => True) U) (k : ℕ) :
    PowerSeries.coeff k (letterSeries * U) =
      ∑ j, PowerSeries.coeff (colPos D j) U * letterOf cohLetters ((k : ℤ) - colPos D j) := by
  have h := coeff_series_mul_uniPoly cohLetters (fun j => PowerSeries.coeff (colPos D j) U)
    (colPos D) k
  rw [uniPoly_colVec_eq D hU, mul_add, mul_one, map_add] at h
  have e : PowerSeries.coeff k (PowerSeries.mk cohLetters) = cohLetters k := by
    rw [PowerSeries.coeff_mk]
  rw [e] at h
  exact add_left_cancel h

/-- A sum over `Fin n` of a function supported on the first `q` indices. -/
theorem sum_fin_lead {F : Type*} [AddCommMonoid F] {q : ℕ} (hq : q ≤ n) (f : Fin n → F)
    (hf : ∀ j : Fin n, q ≤ j.val → f j = 0) :
    ∑ j : Fin n, f j = ∑ j : Fin q, f (Fin.castLE hq j) := by
  have : ∑ j : Fin q, f (Fin.castLE hq j) = ∑ x ∈ (Finset.univ : Finset (Fin q)).map
      (Fin.castLEEmb hq), f x := by
    rw [Finset.sum_map]; rfl
  rw [this]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hf x ?_).symm
  by_contra hlt
  push Not at hlt
  exact hx (Finset.mem_map.2 ⟨⟨x.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/-- `D` carries the cap `K` as its prefix, translated by `t`. -/
def CapMatches {q : ℕ} (D : BetaDiagram (n + 1)) (hq : q ≤ n) (t : ℤ) (K : BetaDiagram (q + 1)) :
    Prop :=
  (∀ i : Fin (q + 1), D.row (Fin.castLE (by omega) i) - t = K.row i) ∧
    ∀ j : Fin q, D.col (Fin.castLE (by omega) j.castSucc) - t = K.col j.castSucc

section Matches

variable {q : ℕ} {hq : q ≤ n} {t : ℤ} {K : BetaDiagram (q + 1)} {D : BetaDiagram (n + 1)}
  (hD : IsNorm D) (hm : CapMatches D hq t K)

include hD hm

theorem capMatches_leftExp (i : Fin q) :
    leftExp K i + rowPos D ⟨i.val, by omega⟩ = span D := by
  have h1 := hm.1 0
  have h2 := hm.1 i.succ
  have h3 : D.row (Fin.castLE (by omega : q + 1 ≤ n + 1) i.succ) =
      D.row (⟨i.val, by omega⟩ : Fin n).succ := rfl
  have h4 := rowPos_cast D ⟨i.val, by omega⟩
  have h5 := span_cast D
  have h6 := row_zero_eq D hD
  have h7 := rowPos_lt_span D ⟨i.val, by omega⟩
  have h8 : D.row (Fin.castLE (by omega : q + 1 ≤ n + 1) 0) = D.row 0 := rfl
  unfold leftExp
  have : D.col (Fin.last n) = 0 := hD
  omega

theorem capMatches_topRow (j : Fin q) :
    topRowOf cohLetters K j = letterOf cohLetters ((span D : ℤ) - colPos D ⟨j.val, by omega⟩) := by
  have h1 := hm.1 0
  have h2 := hm.2 j
  have h3 : D.col (Fin.castLE (by omega : q + 1 ≤ n + 1) j.castSucc) =
      D.col (⟨j.val, by omega⟩ : Fin n).castSucc := rfl
  have h4 := col_castSucc_eq D hD ⟨j.val, by omega⟩
  have h5 := row_zero_eq D hD
  have h8 : D.row (Fin.castLE (by omega : q + 1 ≤ n + 1) 0) = D.row 0 := rfl
  unfold topRowOf
  congr 1
  omega

theorem capMatches_properMatrix (i j : Fin q) :
    properMatrixOf cohLetters K i j =
      properMatrixOf cohLetters D ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ := by
  have h1 := hm.1 i.succ
  have h2 := hm.2 j
  have h3 : D.row (Fin.castLE (by omega : q + 1 ≤ n + 1) i.succ) =
      D.row (⟨i.val, by omega⟩ : Fin n).succ := rfl
  have h4 : D.col (Fin.castLE (by omega : q + 1 ≤ n + 1) j.castSucc) =
      D.col (⟨j.val, by omega⟩ : Fin n).castSucc := rfl
  simp only [properMatrixOf, Matrix.of_apply]
  congr 1
  omega

end Matches

/-- Expansion of the left coframe of the recursive cap: `[z^c] H C_K U` is `[z^c] H U` plus the
coefficients `[z^{x_i}] H U` at the prefix rows, weighted by the left coframe vector. -/
theorem coeff_cap_expand {q : ℕ} {hq : q ≤ n} {t : ℤ} {K : BetaDiagram (q + 1)}
    {D : BetaDiagram (n + 1)} (hD : IsNorm D) (hm : CapMatches D hq t K)
    (U : PowerSeries CohField) :
    PowerSeries.coeff (span D) (letterSeries *
      ((leftCoframe K : CohField[X]) : PowerSeries CohField) * U) =
      PowerSeries.coeff (span D) (letterSeries * U) +
        ∑ i : Fin q, leftVecOf cohLetters K i *
          PowerSeries.coeff (rowPos D ⟨i.val, by omega⟩) (letterSeries * U) := by
  classical
  set lv := leftVecOf cohLetters K with hlv
  have hC : ((leftCoframe K : CohField[X]) : PowerSeries CohField) =
      1 + ∑ i, ((Polynomial.C (lv i) * Polynomial.X ^ leftExp K i : CohField[X]) :
        PowerSeries CohField) := by
    unfold leftCoframe leftCoframeOf capPoly
    rw [Polynomial.coe_add, Polynomial.coe_one]
    congr 1
    exact map_sum (Polynomial.coeToPowerSeries.ringHom (R := CohField)) _ _
  have hexpand : letterSeries * ((leftCoframe K : CohField[X]) : PowerSeries CohField) * U =
      (1 + ∑ i, ((Polynomial.C (lv i) * Polynomial.X ^ leftExp K i : CohField[X]) :
        PowerSeries CohField)) * (letterSeries * U) := by
    rw [hC]; ring
  rw [hexpand, add_mul, one_mul, map_add, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := capMatches_leftExp hD hm i
  rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
  rw [show span D - leftExp K i = rowPos D ⟨i.val, by omega⟩ by omega]

/-- **The left coframe of the recursive cap kills the prefix.**  If `D` carries the cap `K` as its
prefix, then `[z^c] H C_K U = 0` for every series `U` on the prefix columns. -/
theorem coeff_cap_prefix {q : ℕ} {hq : q ≤ n} {t : ℤ} {K : BetaDiagram (q + 1)}
    (hKc : K.Connected) {D : BetaDiagram (n + 1)} (hD : IsNorm D) (hm : CapMatches D hq t K)
    {U : PowerSeries CohField} (hU : SuppCols D (fun j => j.val < q) U) :
    PowerSeries.coeff (span D) (letterSeries *
      ((leftCoframe K : CohField[X]) : PowerSeries CohField) * U) = 0 := by
  classical
  have hU' : SuppCols D (fun _ => True) U := hU.mono (fun _ _ => trivial)
  set lv := leftVecOf cohLetters K with hlv
  have hlvP : lv ᵥ* properMatrixOf cohLetters K = -topRowOf cohLetters K :=
    leftVecOf_vecMul cohLetters K (isUnit_iff_ne_zero.2 (properDet_cohLetters_ne_zero hKc))
  rw [coeff_cap_expand hD hm]
  rw [coeff_H_mul_supp D hU' (span D)]
  have hu : ∀ j : Fin n, q ≤ j.val → PowerSeries.coeff (colPos D j) U = 0 := fun j hj =>
    hU.apply_not (by omega)
  rw [sum_fin_lead hq _ (fun j hj => by rw [hu j hj, zero_mul])]
  have hrow : ∀ i : Fin q, PowerSeries.coeff (rowPos D ⟨i.val, by omega⟩) (letterSeries * U) =
      ∑ j : Fin q, properMatrixOf cohLetters K i j *
        PowerSeries.coeff (colPos D ⟨j.val, by omega⟩) U := by
    intro i
    rw [coeff_rowPos_supp D hU']
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_fin_lead hq _ (fun j hj => by rw [hu j hj, mul_zero])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [capMatches_properMatrix hD hm i j]
    rfl
  simp only [hrow, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := congrFun hlvP j
  simp only [Matrix.vecMul, dotProduct, Pi.neg_apply] at hj
  rw [capMatches_topRow hD hm j] at hj
  have e : Fin.castLE hq j = (⟨j.val, by omega⟩ : Fin n) := rfl
  rw [e]
  simp only [← mul_assoc, ← Finset.sum_mul]
  rw [← hlv, hj]
  ring

end SkewCoframeRigidity.FixedCap
