/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergOneShyIndexing
import SkewCornerDescent.Matrix.NormalInverseProductJets

/-!
# Complete marked period-activity jets

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A produced constant period gradient retains every reciprocal diagonal jet.
The disjoint-pair residue keeps its complete pair response and both cost-two marks.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- A common full period gradient supplies both lower interval jets and the
complete disjoint-pair residue. The gradient premise must be produced from
actual source geometry before applying this algebraic reduction. -/
theorem normal_marked_period_jets {N m : ℕ} (hm : 2 ≤ m) {F : Type*} [Field F]
    (A G : Matrix (Fin N) (Fin N) (PowerSeries F)) (γ : F)
    (hunit : ∀ i, PowerSeries.constantCoeff (A i i) ≠ 0)
    (hgradient : ∀ i j, j.val + 1 = i.val + m → G i j = PowerSeries.C γ) :
    let w := fun j => (A j j)⁻¹
    let w₀ := fun j => (PowerSeries.constantCoeff (A j j))⁻¹
    let ν := fun j => PowerSeries.coeff 1 (A j j) * w₀ j
    let lower := ∑ i : Fin N, ∑ j : Fin N,
      if i.val ≤ j.val ∧ j.val - i.val = m - 1 then
        G i j * ∏ k ∈ Finset.Icc i j, w k else 0
    let pair := ∑ p : OneShyIntervalPair N m,
      (G p.longStart p.longEnd * ∏ k ∈ Finset.Icc p.longStart p.longEnd, w k) *
        (A p.pairStart p.pairEnd * ∏ k ∈ Finset.Icc p.pairStart p.pairEnd, w k)
    PowerSeries.constantCoeff lower = γ *
      (∑ i : Fin N, ∑ j : Fin N, if j.val - i.val = m - 1 then
        ∏ k ∈ Finset.Icc i j, w₀ k else 0) ∧
    PowerSeries.coeff 1 lower = -γ *
      (∑ i : Fin N, ∑ j : Fin N, if j.val - i.val = m - 1 then
        (∏ k ∈ Finset.Icc i j, w₀ k) * ∑ k ∈ Finset.Icc i j, ν k else 0) ∧
    PowerSeries.constantCoeff pair = γ *
      (∑ p : OneShyIntervalPair N m,
        (∏ k ∈ Finset.Icc p.longStart p.longEnd, w₀ k) *
          (PowerSeries.constantCoeff (A p.pairStart p.pairEnd) *
            ∏ k ∈ Finset.Icc p.pairStart p.pairEnd, w₀ k)) := by
  classical
  dsimp only
  constructor
  · rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hlen : j.val - i.val = m - 1
    · have hiup : i.val ≤ j.val := by omega
      have hcond : i.val ≤ j.val ∧ j.val - i.val = m - 1 := ⟨hiup, hlen⟩
      rw [ite_eq_left hcond, ite_eq_left hlen, hgradient i j (by omega),
        map_mul, PowerSeries.constantCoeff_C, map_prod]
      simp only [PowerSeries.constantCoeff_inv]
    · have hcond : ¬ (i.val ≤ j.val ∧ j.val - i.val = m - 1) := fun h => hlen h.2
      rw [ite_eq_right hcond, ite_eq_right hlen, map_zero, mul_zero]
  constructor
  · rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hlen : j.val - i.val = m - 1
    · have hiup : i.val ≤ j.val := by omega
      have hcond : i.val ≤ j.val ∧ j.val - i.val = m - 1 := ⟨hiup, hlen⟩
      rw [ite_eq_left hcond, ite_eq_left hlen, hgradient i j (by omega),
        PowerSeries.coeff_C_mul,
        normal_inverse_product_coeff_one (Finset.Icc i j) (fun k => A k k)
          (fun k _ => hunit k)]
      ring
    · have hcond : ¬ (i.val ≤ j.val ∧ j.val - i.val = m - 1) := fun h => hlen h.2
      rw [ite_eq_right hcond, ite_eq_right hlen, map_zero, mul_zero]
  · rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    have hlen := p.longLength
    rw [hgradient p.longStart p.longEnd (by omega)]
    simp only [map_mul, map_prod, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv]
    ring

end SkewCornerDescent.Matrix
