/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Defs

/-!
# Algebra of the coframe equations

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:coframe-definition` and the Schur
complement in `sc:atlas`.  For generic letters in a commutative ring and an arbitrary vector
`g` of coefficients solving the proper linear system, the numerator coefficients at the
positions `I_A` vanish and the Jacobi–Trudi determinant equals the signed proper corner times
the degree-`M` coefficient of `HG`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The polynomial `1 + ∑ g_j z^{s_j}` with an arbitrary coefficient vector. -/
noncomputable def uniPoly (g : Fin n → R) (s : Fin n → ℕ) : R[X] :=
  1 + ∑ j, C (g j) * X ^ s j

omit [CommRing R] in
theorem letterOf_of_neg [Zero R] (h : ℕ → R) {k : ℤ} (hk : k < 0) : letterOf h k = 0 := by
  simp [letterOf, hk]

omit [CommRing R] in
theorem letterOf_of_nonneg [Zero R] (h : ℕ → R) {k : ℤ} (hk : 0 ≤ k) :
    letterOf h k = h k.toNat := by
  simp [letterOf, not_lt.mpr hk]

omit [CommRing R] in
theorem letterOf_natCast [Zero R] (h : ℕ → R) (k : ℕ) : letterOf h (k : ℤ) = h k := by
  simp [letterOf_of_nonneg h (Int.natCast_nonneg k)]

theorem coeff_series_mul_uniPoly (h : ℕ → R) (g : Fin n → R) (s : Fin n → ℕ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk h * (uniPoly g s : PowerSeries R)) =
      h k + ∑ j, g j * letterOf h ((k : ℤ) - s j) := by
  unfold uniPoly
  have hsum : ((∑ j, C (g j) * X ^ s j : R[X]) : PowerSeries R) =
      ∑ j, ((C (g j) * X ^ s j : R[X]) : PowerSeries R) :=
    map_sum (Polynomial.coeToPowerSeries.ringHom (R := R)) _ _
  rw [Polynomial.coe_add, Polynomial.coe_one, mul_add, mul_one, map_add, PowerSeries.coeff_mk]
  congr 1
  rw [hsum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
    mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  by_cases hs : s j ≤ k
  · have e : ((k : ℤ) - s j).toNat = k - s j := by omega
    rw [letterOf_of_nonneg h (by omega), e, PowerSeries.coeff_mk]
    simp [hs]
  · rw [letterOf_of_neg h (by omega)]
    simp [hs]


section Positions

variable (D : BetaDiagram (n + 1))

theorem col_last_le (j : Fin (n + 1)) : D.col (Fin.last n) ≤ D.col j :=
  D.col_strictAnti.antitone (Fin.le_last j)

theorem colPos_cast (j : Fin n) : (colPos D j : ℤ) = D.col j.castSucc - D.col (Fin.last n) := by
  have := col_last_le D j.castSucc
  unfold colPos
  omega

theorem rowPos_cast (i : Fin n) : (rowPos D i : ℤ) = D.row i.succ - D.col (Fin.last n) := by
  have := col_last_le D i.succ
  have := D.row_nonempty i.succ
  unfold rowPos
  omega

theorem span_cast : (span D : ℤ) = D.largestLabel := by
  have := D.largestLabel_pos
  unfold span
  omega

theorem span_pos : 0 < span D := by
  have := D.largestLabel_pos
  have := span_cast D
  omega

theorem colPos_pos (j : Fin n) : 0 < colPos D j := by
  have h1 := D.col_strictAnti (show j.castSucc < Fin.last n from Fin.castSucc_lt_last j)
  have := colPos_cast D j
  omega

theorem colPos_lt_span (j : Fin n) : colPos D j < span D := by
  have h1 : D.row 0 ≤ D.row 0 := le_rfl
  have h2 := D.row_nonempty j.castSucc
  have h3 : D.row j.castSucc ≤ D.row 0 := D.row_strictAnti.antitone (Fin.zero_le _)
  have := colPos_cast D j
  have := span_cast D
  unfold BetaDiagram.largestLabel at this
  omega

theorem rowPos_pos (i : Fin n) : 0 < rowPos D i := by
  have h1 := col_last_le D i.succ
  have h2 := D.row_nonempty i.succ
  have := rowPos_cast D i
  omega

theorem rowPos_lt_span (i : Fin n) : rowPos D i < span D := by
  have h1 : D.row i.succ < D.row 0 := D.row_strictAnti (Fin.succ_pos i)
  have := rowPos_cast D i
  have := span_cast D
  unfold BetaDiagram.largestLabel at this
  omega

theorem colPos_injective : Function.Injective (colPos D) := by
  intro i j hij
  have h := colPos_cast D i
  rw [hij, colPos_cast D j] at h
  have : D.col i.castSucc = D.col j.castSucc := by omega
  exact Fin.castSucc_injective _ (D.col_strictAnti.injective this)

theorem rowPos_injective : Function.Injective (rowPos D) := by
  intro i j hij
  have h := rowPos_cast D i
  rw [hij, rowPos_cast D j] at h
  have : D.row i.succ = D.row j.succ := by omega
  exact Fin.succ_injective _ (D.row_strictAnti.injective this)

theorem card_colSet : (colSet D).card = n := by
  unfold colSet
  rw [Finset.card_image_of_injective _ (colPos_injective D)]
  simp

theorem card_rowSet : (rowSet D).card = n := by
  unfold rowSet
  rw [Finset.card_image_of_injective _ (rowPos_injective D)]
  simp

theorem rowPos_sub_colPos (i j : Fin n) :
    (rowPos D i : ℤ) - colPos D j = D.row i.succ - D.col j.castSucc := by
  rw [rowPos_cast D, colPos_cast D]
  ring

theorem span_sub_colPos (j : Fin n) :
    (span D : ℤ) - colPos D j = D.row 0 - D.col j.castSucc := by
  rw [span_cast D, colPos_cast D]
  unfold BetaDiagram.largestLabel
  ring

end Positions

section Equations

variable (h : ℕ → R) (D : BetaDiagram (n + 1)) (g : Fin n → R)

theorem coeff_rowPos (i : Fin n) :
    PowerSeries.coeff (rowPos D i) (PowerSeries.mk h * (uniPoly g (colPos D) : PowerSeries R)) =
      topVecOf h D i + (properMatrixOf h D *ᵥ g) i := by
  rw [coeff_series_mul_uniPoly]
  congr 1
  · unfold topVecOf
    rw [← letterOf_natCast h (rowPos D i), rowPos_cast D]
  · simp only [Matrix.mulVec, dotProduct, properMatrixOf, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rowPos_sub_colPos D, mul_comm]

theorem coeff_span :
    PowerSeries.coeff (span D) (PowerSeries.mk h * (uniPoly g (colPos D) : PowerSeries R)) =
      letterOf h D.largestLabel + ∑ j, g j * letterOf h (D.row 0 - D.col j.castSucc) := by
  rw [coeff_series_mul_uniPoly, ← letterOf_natCast h (span D), span_cast D]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e := span_sub_colPos D j
  rw [span_cast D] at e
  rw [e]

/-- If the coefficient vector solves the proper system, the numerator vanishes on `I_A`. -/
theorem coeff_rowPos_eq_zero (hg : properMatrixOf h D *ᵥ g = -topVecOf h D) (i : Fin n) :
    PowerSeries.coeff (rowPos D i) (PowerSeries.mk h * (uniPoly g (colPos D) : PowerSeries R))
      = 0 := by
  rw [coeff_rowPos, hg]
  simp

/-- The Schur complement identity `s_A = κ_A [HG]_M`. -/
theorem schurOf_eq_corner_mul (hg : properMatrixOf h D *ᵥ g = -topVecOf h D) :
    schurOf h D = cornerOf h D *
      PowerSeries.coeff (span D) (PowerSeries.mk h * (uniPoly g (colPos D) : PowerSeries R)) := by
  classical
  set N := fullMatrixOf h D with hN
  let c : Fin (n + 1) → R := Fin.snoc (α := fun _ => R) g 1
  have hdet := Matrix.det_updateCol_sum N (Fin.last n) c
  have hc : c (Fin.last n) = 1 := by simp [c]
  rw [hc, one_smul] at hdet
  have hcol : ∀ k, (∑ i, c i • N k i) = N k (Fin.last n) + ∑ j : Fin n, g j * N k j.castSucc := by
    intro k
    rw [Fin.sum_univ_castSucc]
    simp only [c, Fin.snoc_castSucc, Fin.snoc_last, smul_eq_mul, one_mul]
    rw [add_comm]
  set N' := N.updateCol (Fin.last n) fun k => ∑ i, c i • N k i with hN'
  have hsc : schurOf h D = N'.det := by
    rw [hN', hdet]; rfl
  have hcol' : ∀ k, N' k (Fin.last n) = N k (Fin.last n) + ∑ j : Fin n, g j * N k j.castSucc := by
    intro k
    rw [hN', Matrix.updateCol_self]
    exact hcol k
  have hrest : ∀ i : Fin n, N' i.succ (Fin.last n) = 0 := by
    intro i
    rw [hcol']
    have := congrFun hg i
    simp only [Matrix.mulVec, dotProduct, properMatrixOf, Pi.neg_apply, topVecOf,
      Matrix.of_apply] at this
    have e : N i.succ (Fin.last n) = letterOf h (D.row i.succ - D.col (Fin.last n)) := rfl
    have e2 : ∀ j : Fin n, N i.succ j.castSucc = letterOf h (D.row i.succ - D.col j.castSucc) :=
      fun j => rfl
    simp only [e, e2]
    rw [show ∑ j, g j * letterOf h (D.row i.succ - D.col j.castSucc) =
      ∑ j, letterOf h (D.row i.succ - D.col j.castSucc) * g j from
        Finset.sum_congr rfl fun j _ => mul_comm _ _, this]
    ring
  have h0 : N' 0 (Fin.last n) =
      letterOf h D.largestLabel + ∑ j, g j * letterOf h (D.row 0 - D.col j.castSucc) := by
    rw [hcol']; rfl
  have hsub : N'.submatrix (Fin.succAbove 0) (Fin.last n).succAbove = properMatrixOf h D := by
    ext i j
    simp [hN', Fin.succAbove_last, properMatrixOf, hN, fullMatrixOf,
      (Fin.castSucc_lt_last j).ne]
  rw [hsc, Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_succ]
  simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [h0, hsub, coeff_span, cornerOf]
  simp
  ring

end Equations

section UniPoly

variable (g : Fin n → R) (s : Fin n → ℕ)

theorem uniPoly_coeff (k : ℕ) :
    (uniPoly g s).coeff k = (if k = 0 then 1 else 0) + ∑ j, if s j = k then g j else 0 := by
  unfold uniPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_one, finsetSum_coeff]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : s j = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem uniPoly_coeff_apply (hs : Function.Injective s) (hpos : ∀ j, 0 < s j) (j : Fin n) :
    (uniPoly g s).coeff (s j) = g j := by
  rw [uniPoly_coeff, ite_eq_right (hpos j).ne', zero_add,
    Finset.sum_eq_single j (fun i _ hi => ite_eq_right (fun h => hi (hs h))) (by simp)]
  simp

theorem uniPoly_coeff_of_ne (k : ℕ) (hk : 0 < k) (hne : ∀ j, s j ≠ k) :
    (uniPoly g s).coeff k = 0 := by
  rw [uniPoly_coeff, ite_eq_right hk.ne']
  simp [hne]

theorem uniPoly_coeff_zero : (uniPoly g s).coeff 0 = 1 + ∑ j, if s j = 0 then g j else 0 := by
  rw [uniPoly_coeff]; simp

end UniPoly

section FieldEquations

variable {K : Type*} [Field K] (h : ℕ → K) (D : BetaDiagram (n + 1))

theorem coframeOf_eq_uniPoly : coframeOf h D = uniPoly (coframeVecOf h D) (colPos D) := rfl

theorem properMatrix_mulVec_coframeVecOf (hT : (properMatrixOf h D).det ≠ 0) :
    properMatrixOf h D *ᵥ coframeVecOf h D = -topVecOf h D := by
  unfold coframeVecOf
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT), Matrix.one_mulVec]

theorem numeratorOf_coeff (k : ℕ) :
    (numeratorOf h D).coeff k =
      if k < span D then
        PowerSeries.coeff k (seriesOf h * (coframeOf h D : PowerSeries K)) else 0 :=
  PowerSeries.coeff_trunc _ _ _

theorem numeratorOf_coeff_rowPos (hT : (properMatrixOf h D).det ≠ 0) (i : Fin n) :
    (numeratorOf h D).coeff (rowPos D i) = 0 := by
  rw [numeratorOf_coeff, ite_eq_left (rowPos_lt_span D i)]
  exact coeff_rowPos_eq_zero h D _ (properMatrix_mulVec_coframeVecOf h D hT) i

theorem numeratorOf_coeff_zero : (numeratorOf h D).coeff 0 = h 0 := by
  rw [numeratorOf_coeff, ite_eq_left (span_pos D)]
  rw [coframeOf_eq_uniPoly]
  unfold seriesOf
  rw [coeff_series_mul_uniPoly]
  have : ∀ j : Fin n, letterOf h (((0 : ℕ) : ℤ) - colPos D j) = 0 := fun j =>
    letterOf_of_neg h (by have := colPos_pos D j; omega)
  rw [Finset.sum_eq_zero (fun j _ => by rw [this j, mul_zero]), add_zero]

theorem schurOf_eq_cornerOf_mul_topQuotientOf (hT : (properMatrixOf h D).det ≠ 0) :
    schurOf h D = cornerOf h D * topQuotientOf h D :=
  schurOf_eq_corner_mul h D _ (properMatrix_mulVec_coframeVecOf h D hT)

end FieldEquations

section SeriesLemmas

theorem uniPoly_coeff_zero_of_pos (g : Fin n → R) (s : Fin n → ℕ) (hpos : ∀ j, 0 < s j) :
    (uniPoly g s).coeff 0 = 1 := by
  rw [uniPoly_coeff_zero, Finset.sum_eq_zero fun j _ => by simp [(hpos j).ne'], add_zero]

theorem constantCoeff_uniPoly (g : Fin n → R) (s : Fin n → ℕ) (hpos : ∀ j, 0 < s j) :
    PowerSeries.constantCoeff (uniPoly g s : PowerSeries R) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    uniPoly_coeff_zero_of_pos g s hpos]

/-- The coefficient of a product up to degree `i` depends only on the factors up to degree `i`. -/
theorem coeff_mul_congr (A A' B : PowerSeries R) (i : ℕ)
    (h : ∀ k ≤ i, PowerSeries.coeff k A = PowerSeries.coeff k A') :
    PowerSeries.coeff i (A * B) = PowerSeries.coeff i (A' * B) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have : p.1 ≤ i := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega
  rw [h p.1 this]

end SeriesLemmas

section FieldSeries

variable {K : Type*} [Field K] (h : ℕ → K) (D : BetaDiagram (n + 1))

theorem constantCoeff_coframeOf :
    PowerSeries.constantCoeff (coframeOf h D : PowerSeries K) = 1 :=
  constantCoeff_uniPoly _ _ (colPos_pos D)

theorem coeff_numeratorOf_mul_inv {j : ℕ} (hj : j < span D) :
    PowerSeries.coeff j ((numeratorOf h D : PowerSeries K) *
      (coframeOf h D : PowerSeries K)⁻¹) = h j := by
  have hc : PowerSeries.constantCoeff (coframeOf h D : PowerSeries K) ≠ 0 := by
    rw [constantCoeff_coframeOf]; exact one_ne_zero
  have h1 : PowerSeries.coeff j ((numeratorOf h D : PowerSeries K) *
      (coframeOf h D : PowerSeries K)⁻¹) =
      PowerSeries.coeff j ((seriesOf h * (coframeOf h D : PowerSeries K)) *
        (coframeOf h D : PowerSeries K)⁻¹) := by
    apply coeff_mul_congr
    intro k hk
    rw [Polynomial.coeff_coe, numeratorOf, PowerSeries.coeff_trunc, ite_eq_left (by omega)]
  rw [h1, mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]
  simp [seriesOf]

end FieldSeries

end SkewCoframeRigidity.Coframe
