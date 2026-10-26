/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalMarkedPeriodJets
import SkewCornerDescent.Matrix.HessenbergDisjointPairCancellation

/-!
# Complete marked logarithmic contributions after disjoint cancellation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both period jets and the actual first partition coefficient retain complete
inverse diagonals. Exact selected-cost signs leave only overlapping pair charges.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The exact three marked logarithmic contributions reduce to the full long
residue, the weighted vertex slope, and the negative overlapping-pair charge.
The common period gradient and first partition formula are DERIVED premises;
actual source producers must supply both at the point of application. -/
theorem normal_marked_log_overlap {N m : ℕ} (hm : 2 ≤ m) {F : Type*} [Field F]
    (A G : Matrix (Fin N) (Fin N) (PowerSeries F)) (b γ : F)
    (hunit : ∀ i, PowerSeries.constantCoeff (A i i) ≠ 0)
    (hgradient : ∀ i j, j.val + 1 = i.val + m → G i j = PowerSeries.C γ)
    (hfirst : let w₀ := fun i => (PowerSeries.constantCoeff (A i i))⁻¹
      PowerSeries.coeff 1 (A.det * ∏ i, (A i i)⁻¹) =
        -b * (∑ k : Fin N, ∑ l : Fin N, if l.val = k.val + 1 then
          PowerSeries.constantCoeff (A k l) * ∏ i ∈ Finset.Icc k l, w₀ i else 0)) :
    let w := fun i => (A i i)⁻¹
    let w₀ := fun i => (PowerSeries.constantCoeff (A i i))⁻¹
    let ν := fun i => PowerSeries.coeff 1 (A i i) * w₀ i
    let interval := fun L => ∑ i : Fin N, ∑ j : Fin N,
      if i.val ≤ j.val ∧ j.val - i.val = L then
        G i j * ∏ k ∈ Finset.Icc i j, w k else 0
    let pair := ∑ p : OneShyIntervalPair N m,
      (G p.longStart p.longEnd * ∏ k ∈ Finset.Icc p.longStart p.longEnd, w k) *
        (A p.pairStart p.pairEnd * ∏ k ∈ Finset.Icc p.pairStart p.pairEnd, w k)
    (-1 : F) ^ m * b ^ m * PowerSeries.constantCoeff (interval m + pair) +
      (-1 : F) ^ (m - 1) * b ^ (m - 1) *
        (PowerSeries.coeff 1 (interval (m - 1)) -
          PowerSeries.coeff 1 (A.det * ∏ j, w j) *
            PowerSeries.constantCoeff (interval (m - 1))) =
    (-1 : F) ^ m * b ^ m * PowerSeries.constantCoeff (interval m) -
      (-1 : F) ^ (m - 1) * b ^ (m - 1) * γ *
        (∑ i : Fin N, ∑ j : Fin N, if j.val - i.val = m - 1 then
          (∏ k ∈ Finset.Icc i j, w₀ k) * ∑ k ∈ Finset.Icc i j, ν k else 0) -
      (-1 : F) ^ m * b ^ m * γ *
        (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
          if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
            ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
              (∏ s ∈ Finset.Icc i j, w₀ s) *
                (PowerSeries.constantCoeff (A k l) * ∏ s ∈ Finset.Icc k l, w₀ s) else 0) := by
  let w₀ := fun i => (PowerSeries.constantCoeff (A i i))⁻¹
  let L := fun i j : Fin N => ∏ s ∈ Finset.Icc i j, w₀ s
  let Q := fun i j : Fin N => PowerSeries.constantCoeff (A i j) * L i j
  have h := normal_marked_period_jets hm A G γ hunit hgradient
  have hc := signed_disjoint_pair_log_cancellation (N := N) (m := m) (by omega) b γ L Q
  dsimp only at h hfirst ⊢
  rw [map_add, h.1, h.2.1, h.2.2, hfirst]
  dsimp only [L, Q, w₀] at hc
  linear_combination hc

end SkewCornerDescent.Matrix
