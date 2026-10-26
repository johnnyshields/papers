/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.TopColumn
import SkewCoframeRigidity.Stationary.DerivSeries
import SkewCoframeRigidity.Stationary.TopGeometry

/-!
# The derivative of the coframe series

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:component-column`.  For a connected
diagram whose first proper row sits at `M - 1`, the derivative of the complete coframe series in
the letter `H_{M-1}` is `-k⁻¹ z^a g`, where `a` is the least column of the highest strict
component, `g` its own right coframe (`1` for a unit) and `k = [Hg]_L` its top quotient, with
`L = M - 1 - a` its span.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The derivative of the coframe series is the polynomial with the derivatives of the native
coefficients. -/
theorem dS_coframe (D : BetaDiagram (n + 1)) :
    dS (span D - 1) (coframe D : PowerSeries CohField) =
      ((∑ j : Fin n, Polynomial.C (dRaw (span D - 1) (coframeVecOf cohLetters D j)) *
        Polynomial.X ^ colPos D j : CohField[X]) : PowerSeries CohField) := by
  ext s
  rw [coeff_dS, Polynomial.coeff_coe, Polynomial.coeff_coe]
  unfold coframe coframeOf
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, dRaw_add,
    dRaw_sum]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  have : dRaw (span D - 1) (if s = 0 then (1 : CohField) else 0) = 0 := by
    split_ifs
    · exact dRaw_one _
    · exact dRaw_zero _
  rw [this, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, dRaw_zero]


theorem rowPos_zero_eq {D : BetaDiagram (n + 1)} (hn : 0 < n) :
    (rowPos D ⟨0, hn⟩ : ℤ) = D.row (⟨0, hn⟩ : Fin n).succ - D.col (Fin.last n) := by
  rw [rowPos_cast]

/-- `sc:component-column`. -/
theorem top_data {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n) (htop : TopRow D hn) :
    ∃ (a L : ℕ) (g : CohField[X]) (k : CohField), k ≠ 0 ∧ 1 ≤ a ∧ a + L = span D - 1 ∧
      g.coeff 0 = 1 ∧
      dS (span D - 1) (coframe D : PowerSeries CohField) =
        ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X]) : PowerSeries CohField) ∧
      PowerSeries.coeff L (PowerSeries.mk cohLetters * (g : PowerSeries CohField)) = k ∧
      ((L = 0 ∧ g = 1 ∧ k = cohLetters 0) ∨
        (1 ≤ L ∧ ∃ (n' : ℕ) (E : BetaDiagram (n' + 1)), E.Connected ∧ span E = L ∧
          coframe E = g ∧ topQuotient E = k)) ∧ TopFlags D a L g := by
  obtain ⟨t, ht, W, k, hWs, hk, hW, hblk, hcase⟩ := top_component_solution hD hn
  have hdvec := dvec_eq_of_solution hD hn htop hk hW
  have hcol := colPos_pos D ⟨t, by omega⟩
  have hrp := rowPos_zero_eq (D := D) hn
  have htopZ : (rowPos D ⟨0, hn⟩ : ℤ) = span D - 1 := by
    unfold TopRow at htop; have := span_pos D; omega
  -- the series identity from the polynomial one
  have hser : ∀ (g : CohField[X]) (a : ℕ),
      (∑ j : Fin n, Polynomial.C (dRaw (span D - 1) (coframeVecOf cohLetters D j)) *
        Polynomial.X ^ colPos D j : CohField[X]) = -(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) →
      dS (span D - 1) (coframe D : PowerSeries CohField) =
        ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X]) : PowerSeries CohField) :=
    fun g a h => by rw [dS_coframe, h]
  have hcoef : ∀ j : Fin n, dRaw (span D - 1) (coframeVecOf cohLetters D j) = -(k⁻¹ * W j) :=
    fun j => congrFun hdvec j
  rcases hcase with ⟨ht0, hu, hkϑ, hWe⟩ | ⟨hpos, hconn, hkE, hWE⟩
  · subst ht0
    have hu0 := hu ⟨0, hn⟩ rfl
    unfold IsUnit' at hu0
    have hcp := colPos_cast D ⟨0, by omega⟩
    have haeq : (colPos D ⟨0, by omega⟩ : ℤ) = span D - 1 := by
      omega
    refine ⟨colPos D ⟨0, by omega⟩, 0, 1, k, hk, by omega, by omega, by simp, ?_, ?_,
      Or.inl ⟨rfl, rfl, hkϑ⟩, flags_unit D hn hblk hu0⟩
    · apply hser
      rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
      · rw [hcoef, hWe]
        simp only [Pi.single_eq_same, mul_one, Polynomial.C_neg, one_mul, pow_zero]
        ring
      · intro j _ hj
        rw [hcoef, hWe, Pi.single_eq_of_ne hj]; simp
      · simp
    · simp [hkϑ]
  · set E := firstBlock D t ht hpos with hE
    have hEcol : ∀ j : Fin (t + 1), E.col j = D.col (blockEmb 0 (t + 1) (by omega) j).castSucc :=
      fun j => rfl
    have hErow : ∀ j : Fin (t + 1), E.row j = D.row (blockEmb 0 (t + 1) (by omega) j).succ :=
      fun j => rfl
    set a := colPos D ⟨t, by omega⟩ with ha
    have hcpos : ∀ j' : Fin t, colPos D (blockEmb 0 (t + 1) (by omega) j'.castSucc) =
        a + colPos E j' := by
      intro j'
      have h1 := colPos_cast D (blockEmb 0 (t + 1) (by omega) j'.castSucc)
      have h2 := colPos_cast E j'
      have h3 := colPos_cast D ⟨t, by omega⟩
      have e1 := hEcol j'.castSucc
      have e2 := hEcol (Fin.last t)
      have e3 : (blockEmb (n := n) 0 (t + 1) (by omega) (Fin.last t)) = (⟨t, by omega⟩ : Fin n) :=
        Fin.ext (by simp [blockEmb])
      rw [e3] at e2
      apply Nat.cast_injective (R := ℤ)
      push_cast
      omega
    have hspanE : (span E : ℤ) = (span D : ℤ) - 1 - a := by
      have h1 := span_cast E
      have h3 := colPos_cast D ⟨t, by omega⟩
      have h4 := rowPos_zero_eq (D := D) hn
      have e2 := hEcol (Fin.last t)
      have e3 : (blockEmb (n := n) 0 (t + 1) (by omega) (Fin.last t)) = (⟨t, by omega⟩ : Fin n) :=
        Fin.ext (by simp [blockEmb])
      rw [e3] at e2
      unfold BetaDiagram.largestLabel at h1
      have e0 : E.row 0 = D.row (⟨0, hn⟩ : Fin n).succ := rfl
      omega
    have hapos : 0 < a := colPos_pos D _
    have hLpos : 0 < span E := span_pos E
    refine ⟨a, span E, coframe E, topQuotient E, ?_, hapos, by omega, ?_, ?_, rfl,
      Or.inr ⟨hLpos, t, E, hconn, rfl, rfl, rfl⟩, flags_big ht hpos hn hblk hconn⟩
    · rw [← hkE]; exact hk
    · exact coeff_zero_coframe E
    · rw [← hkE]
      refine hser (coframe E) a ?_
      have hW' : ∀ j : Fin n, W j = if h : j.val < t + 1 then
          (Fin.snoc (α := fun _ => CohField) (coframeVecOf cohLetters E) 1 :
            Fin (t + 1) → CohField) ⟨j.val, h⟩ else 0 := by
        intro j
        by_cases h : j.val < t + 1
        · rw [dif_pos h]; exact hWE j h
        · rw [dif_neg h]; by_contra hne; exact h (by have := hWs j hne; omega)
      have hsum := sum_fin_of_supp (n := n) (t := t) ht
        (fun j : Fin n => (Polynomial.C (dRaw (span D - 1) (coframeVecOf cohLetters D j)) *
          Polynomial.X ^ colPos D j : CohField[X])) (fun j hj => by
          rw [hcoef, hW' j, dif_neg (by omega)]; simp)
      rw [hsum, Fin.sum_univ_castSucc]
      have hlast : blockEmb (n := n) 0 (t + 1) (by omega) (Fin.last t) = (⟨t, by omega⟩ : Fin n) :=
        Fin.ext (by simp [blockEmb])
      simp only [hlast]
      have hWl : W ⟨t, by omega⟩ = 1 := by rw [hW' ⟨t, by omega⟩, dif_pos (by simp)]; exact Fin.snoc_last _ _
      rw [hcoef, hWl]
      have hg : coframe E = 1 + ∑ j' : Fin t, Polynomial.C (coframeVecOf cohLetters E j') *
          Polynomial.X ^ colPos E j' := rfl
      have hsumpart : ∑ j' : Fin t, Polynomial.C (-(k⁻¹ * W (blockEmb (n := n) 0 (t + 1)
            (by omega) j'.castSucc))) * Polynomial.X ^ colPos D (blockEmb (n := n) 0 (t + 1)
            (by omega) j'.castSucc) =
          -(Polynomial.C k⁻¹ * Polynomial.X ^ a * ∑ j' : Fin t, Polynomial.C
            (coframeVecOf cohLetters E j') * Polynomial.X ^ colPos E j') := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [hcpos j', hW' _, dif_pos (by simp [blockEmb])]
        have : (Fin.snoc (α := fun _ => CohField) (coframeVecOf cohLetters E) 1 :
            Fin (t + 1) → CohField) ⟨(blockEmb (n := n) 0 (t + 1) (by omega) j'.castSucc).val,
              by simp [blockEmb]⟩ = coframeVecOf cohLetters E j' := by
          have : (⟨(blockEmb (n := n) 0 (t + 1) (by omega) j'.castSucc).val, by simp [blockEmb]⟩ :
              Fin (t + 1)) = j'.castSucc := Fin.ext (by simp [blockEmb])
          rw [this, Fin.snoc_castSucc]
        rw [this, pow_add]
        simp only [Polynomial.C_neg, Polynomial.C_mul]
        ring
      simp only [hcoef] at hsumpart ⊢
      have hq : colPos D (⟨t, by omega⟩ : Fin n) = a := rfl
      rw [hsumpart, hg, hq, Polynomial.C_neg]
      ring

end SkewCoframeRigidity.Coframe
