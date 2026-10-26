/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.Injectivity
import SkewCoframeRigidity.Coframe.Coprime

/-!
# Finite injectivity for the complete coframe

Formalizes `sc:finite-injectivity` of `shields-2026-skew-coframe-rigidity.tex`, «The complete unit
expansion and finite injectivity», for the first statement (the letter series `H`).  For a
connected diagram with complete coframe `g` and span `M`, a polynomial `δ` with `δ₀ = 0` and
`[Hδ]_i = 0` at every original proper row `i` is determined by the vanishing of
`𝒯_{g,δ}(z^a H)`, `0 ≤ a ≤ M - 1`.  The coprimality of `g` with the shifted clipped numerator
is the hypothesis `hcop`; for `a = 0` it is discharged from the coframe's irreducibility.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence SkewCoframeRigidity Polynomial PowerSeries

variable {n : ℕ}

theorem colPos_cast_aux (D : BetaDiagram (n + 1)) (j : Fin n) :
    (colPos D j : ℤ) = D.col j.castSucc - D.col (Fin.last n) := by
  have := D.col_strictAnti.antitone (Fin.le_last j.castSucc)
  unfold colPos
  omega

theorem span_cast_aux (D : BetaDiagram (n + 1)) : (span D : ℤ) = D.largestLabel := by
  have := D.largestLabel_pos
  unfold span
  omega

theorem colPos_pos_aux (D : BetaDiagram (n + 1)) (j : Fin n) : 0 < colPos D j := by
  have h1 := D.col_strictAnti (show j.castSucc < Fin.last n from Fin.castSucc_lt_last j)
  have := colPos_cast_aux D j
  omega

theorem colPos_lt_span_aux (D : BetaDiagram (n + 1)) (j : Fin n) : colPos D j < span D := by
  have h2 := D.row_nonempty j.castSucc
  have h3 : D.row j.castSucc ≤ D.row 0 := D.row_strictAnti.antitone (Fin.zero_le _)
  have := colPos_cast_aux D j
  have := span_cast_aux D
  unfold BetaDiagram.largestLabel at this
  omega

theorem span_pos_aux (D : BetaDiagram (n + 1)) : 0 < span D := by
  have := D.largestLabel_pos
  have := span_cast_aux D
  omega

/-- Shifting through the clipping: `[z^a W f]_{<M} = z^a [W f]_{<M-a}`. -/
theorem trunc_shift_eq {F : Type*} [CommRing F] (M a : ℕ) (ha : a ≤ M) (W f : F⟦X⟧) :
    trunc M (PowerSeries.X ^ a * W * f) = Polynomial.X ^ a * trunc (M - a) (W * f) := by
  ext k
  rw [coeff_trunc, mul_assoc, PowerSeries.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul',
    coeff_trunc]
  by_cases h1 : a ≤ k
  · by_cases h2 : k < M
    · simp [h1, h2, show k - a < M - a by omega]
    · simp [h1, h2, show ¬ k - a < M - a by omega]
  · simp [h1]

theorem cohLetters_zero_ne : cohLetters 0 ≠ 0 := by
  unfold cohLetters
  rw [map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)]
  exact MvPolynomial.X_ne_zero 0

/-- The coefficient at zero of `H g` is the coherent unit `ϑ`. -/
theorem coeff_zero_letterSeries_mul (D : BetaDiagram (n + 1)) :
    PowerSeries.coeff 0 (letterSeries * (coframe D : PowerSeries CohField)) = cohLetters 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
  simp [letterSeries, seriesOf, coframe_coeff_zero]

/-- For a nonconstant coframe the shifted clipped numerator at `a = 0` is coprime to it. -/
theorem coframe_isCoprime_numerator {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    IsCoprime (coframe D) (numerator D) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : coframe D = 1 := by simp [coframe, coframeOf]
    rw [this]; exact isCoprime_one_left
  · exact (Irreducible.coprime_iff_not_dvd (coframe_irreducible hD hn)).mpr
      (coframe_not_dvd_numerator hD hn)

/-- **Finite injectivity** (`sc:finite-injectivity`, first statement). -/
theorem eq_zero_of_clippedOp_letterSeries {D : BetaDiagram (n + 1)} (hD : D.Connected) (a : ℕ)
    (ha : a < span D) (δ : CohField[X]) (hδ0 : δ.coeff 0 = 0)
    (hrows : ∀ i ∈ rowSet D,
      PowerSeries.coeff i (letterSeries * (δ : PowerSeries CohField)) = 0)
    (hcop : IsCoprime (coframe D)
      (trunc (span D - a) (letterSeries * (coframe D : PowerSeries CohField))))
    (hT : clippedOp (span D) (coframe D) δ (PowerSeries.X ^ a * letterSeries) = 0) : δ = 0 := by
  refine eq_zero_of_clippedOp_eq_zero (span D) a (coframe D) δ letterSeries
    (coframe_coeff_zero D) hδ0 ?_ ⟨0, by omega, by
      rw [coeff_zero_letterSeries_mul]; exact cohLetters_zero_ne⟩ ?_ hT
  · rw [trunc_shift_eq _ _ ha.le]
    refine IsCoprime.mul_right ?_ hcop
    refine IsCoprime.pow_right ?_
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := coframe D)
    refine ⟨1, -q, ?_⟩
    rw [coframe_coeff_zero D, map_one] at hq
    linear_combination hq
  · intro i hi hia hP
    refine hrows i ?_
    have hiM : i < span D := by omega
    have hnum : (numerator D).coeff i = 0 := by
      unfold numerator numeratorOf
      rw [coeff_trunc]; simp only [hiM, ite_true]
      exact hP
    exact (numerator_coeff_eq_zero_iff hD hi hiM).mp hnum

/-- The first statement of `sc:finite-injectivity` at `a = 0`, with no coprimality hypothesis. -/
theorem eq_zero_of_clippedOp_letterSeries_zero {D : BetaDiagram (n + 1)} (hD : D.Connected)
    (δ : CohField[X]) (hδ0 : δ.coeff 0 = 0)
    (hrows : ∀ i ∈ rowSet D,
      PowerSeries.coeff i (letterSeries * (δ : PowerSeries CohField)) = 0)
    (hT : clippedOp (span D) (coframe D) δ letterSeries = 0) : δ = 0 := by
  refine eq_zero_of_clippedOp_letterSeries hD 0 (span_pos_aux D) δ hδ0 hrows ?_ (by simpa using hT)
  rw [Nat.sub_zero]; exact coframe_isCoprime_numerator hD

/-- The complete coframe has degree below the span. -/
theorem natDegree_coframe_lt (D : BetaDiagram (n + 1)) : (coframe D).natDegree < span D := by
  have hM := span_pos_aux D
  refine lt_of_le_of_lt (b := span D - 1) (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_)
    (by omega)
  intro k hk
  unfold coframe coframeOf
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_one,
    if_neg (by omega), zero_add]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := colPos_lt_span_aux D j
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

/-- Vanishing modulo `z^{2M-1}` suffices (`sc:finite-injectivity`): for `deg δ < M` the operator
is a polynomial of degree at most `2M - 2`. -/
theorem clippedOp_eq_zero_of_coeff_eq_zero {D : BetaDiagram (n + 1)} (δ : CohField[X])
    (hδ : δ.natDegree < span D) (u : PowerSeries CohField)
    (h : ∀ k < 2 * span D - 1, (clippedOp (span D) (coframe D) δ u).coeff k = 0) :
    clippedOp (span D) (coframe D) δ u = 0 := by
  have hM := span_pos_aux D
  have hg := natDegree_coframe_lt D
  have htr : ∀ f : PowerSeries CohField, (trunc (span D) f).natDegree ≤ span D - 1 := by
    intro f
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [coeff_trunc]; simp only [show ¬ k < span D by omega, ite_false]
  by_contra hne
  have hle : (clippedOp (span D) (coframe D) δ u).natDegree ≤ 2 * span D - 2 := by
    unfold clippedOp
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · have := htr (u * (δ : PowerSeries CohField))
      exact (Polynomial.natDegree_mul_le).trans (by omega)
    · have := htr (u * (coframe D : PowerSeries CohField))
      exact (Polynomial.natDegree_mul_le).trans (by omega)
  apply hne
  ext k
  by_cases hk : k < 2 * span D - 1
  · exact h k hk
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp

end SkewCoframeRigidity.Coframe
