/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.UniversalOmega

/-!
# Universal omega on independent finite alphabets

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The full polynomial involution specializes to elementary coefficients at every
index, including indices beyond the alphabet size. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- Complete series of an independent finite alphabet. -/
noncomputable def independentCompleteSeries (a : ℕ) :
    PowerSeries (MvPolynomial (Fin a) ℚ) :=
  PowerSeries.mk fun n => hsymm (Fin a) ℚ n

/-- Elementary series of the same independent finite alphabet. -/
noncomputable def independentElementarySeries (a : ℕ) :
    PowerSeries (MvPolynomial (Fin a) ℚ) :=
  PowerSeries.mk fun n => esymm (Fin a) ℚ n

/-- Complete specialization transports the entire generator series. -/
theorem evalComplete_map_universal_series (a : ℕ) :
    PowerSeries.map (evalComplete a (varAlphabet a)).toRingHom universalCompleteSeries =
      independentCompleteSeries a := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map]
  simp only [independentCompleteSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, universal_complete_constant,
      map_one, hsymm_zero]
  · let k : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
    change evalComplete a (varAlphabet a)
      (PowerSeries.coeff (k : ℕ) universalCompleteSeries) = hsymm (Fin a) ℚ k
    rw [universal_complete_coeff]
    exact (aeval_X _ _).trans (completeHom_varAlphabet a k)

/-- The signed elementary series is the complete series' exact inverse. -/
theorem independent_negative_elementary_product (a : ℕ) :
    PowerSeries.rescale (-1 : MvPolynomial (Fin a) ℚ) (independentElementarySeries a) *
      independentCompleteSeries a = 1 := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i
      (PowerSeries.rescale (-1 : MvPolynomial (Fin a) ℚ)
        (independentElementarySeries a)) *
      PowerSeries.coeff j (independentCompleteSeries a))]
  simp only [PowerSeries.coeff_rescale, independentElementarySeries,
    independentCompleteSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.sub_self,
      esymm_zero, hsymm_zero, mul_one, PowerSeries.coeff_one, ite_true]
  · rw [PowerSeries.coeff_one, ite_eq_right hn]
    exact AlgebraicCombinatorics.SymmetricPolynomials.newtonGirard_eh n
      (Nat.pos_of_ne_zero hn)

/-- The unsigned elementary series inverts the negative complete series. -/
theorem independent_elementary_negative_product (a : ℕ) :
    independentElementarySeries a *
      PowerSeries.rescale (-1 : MvPolynomial (Fin a) ℚ) (independentCompleteSeries a) = 1 := by
  have h := congrArg (PowerSeries.rescale (-1 : MvPolynomial (Fin a) ℚ))
    (independent_negative_elementary_product a)
  simpa only [map_mul, map_one, PowerSeries.rescale_rescale, neg_mul_neg,
    one_mul, PowerSeries.rescale_one, RingHom.id_apply] using h

/-- Full universal elementary coefficients specialize to the full elementary
series, rather than to a finite-generator surrogate. -/
theorem evalComplete_map_universal_elementary (a : ℕ) :
    PowerSeries.map (evalComplete a (varAlphabet a)).toRingHom universalElementarySeries =
      independentElementarySeries a := by
  let φ := (evalComplete a (varAlphabet a)).toRingHom
  have h := congrArg (PowerSeries.map φ) universal_elementary_complete_product
  have hneg : PowerSeries.map φ (PowerSeries.rescale (-1 : Lambda) universalCompleteSeries) =
      PowerSeries.rescale (-1 : MvPolynomial (Fin a) ℚ) (independentCompleteSeries a) := by
    have hm := PowerSeries.rescale_map φ (-1 : Lambda) universalCompleteSeries
    dsimp only [φ] at hm
    simpa only [map_neg, map_one, evalComplete_map_universal_series] using hm.symm
  rw [map_mul, map_one, hneg] at h
  have hi := independent_elementary_negative_product a
  calc
    PowerSeries.map φ universalElementarySeries =
        PowerSeries.map φ universalElementarySeries * 1 := (mul_one _).symm
    _ = PowerSeries.map φ universalElementarySeries *
        (PowerSeries.rescale (-1 : MvPolynomial (Fin a) ℚ)
          (independentCompleteSeries a) * independentElementarySeries a) := by
      rw [mul_comm _ (independentElementarySeries a), hi]
    _ = independentElementarySeries a := by rw [← mul_assoc, h, one_mul]

/-- Universal omega followed by complete specialization is elementary
specialization at every generator index. -/
theorem evalComplete_comp_schurInvolution (a : ℕ) :
    (evalComplete a (varAlphabet a)).comp schurInvolution =
      aeval (fun n : ℕ+ => esymm (Fin a) ℚ n) := by
  apply MvPolynomial.algHom_ext
  intro n
  change evalComplete a (varAlphabet a) (schurInvolution (X n)) =
    aeval (fun k : ℕ+ => esymm (Fin a) ℚ k) (X n)
  rw [schurInvolution_X, aeval_X, ← universal_elementary_coeff]
  have h := congrArg (PowerSeries.coeff (n : ℕ))
    (evalComplete_map_universal_elementary a)
  rw [PowerSeries.coeff_map, independentElementarySeries, PowerSeries.coeff_mk] at h
  change evalComplete a (varAlphabet a)
    (PowerSeries.coeff (n : ℕ) universalElementarySeries) = esymm (Fin a) ℚ n at h
  exact h

end SkewCornerDescent
