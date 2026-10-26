/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.MatrixIntervalCharges
import SkewCornerDescent.Matrix.MatrixOverlapCharges
import SkewCornerDescent.Matrix.AdjacentPairIndexing
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Full finite-window expansion of the normal open overlap charge

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
This is the explicit long, vertex, and overlapping-pair expression, not a
definition of a logarithmic coefficient. The actual logarithmic derivative is
identified with this expression by the original marked-frontier assembly.
All full normal entries and both exterior pair charges remain present.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The complete three-term open overlap expression, retaining genuine normal
entry gradients and full onsite inverse jets before taking constant terms. -/
noncomputable def normalOpenOverlapCharge {N : ℕ} {F : Type*} [Field F]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (δ : PowerSeries F → PowerSeries F) (b γ : F) (m : ℕ) : F :=
  let w := fun i => (PowerSeries.constantCoeff (M i i))⁻¹
  let ν := fun i => PowerSeries.coeff 1 (M i i) * w i
  let long := ∑ i : Fin N, ∑ j,
    if i.val ≤ j.val ∧ j.val - i.val = m then
      δ (M i j) * ∏ k ∈ Finset.Icc i j, (M k k)⁻¹ else 0
  (-1 : F) ^ m * b ^ m * PowerSeries.constantCoeff long -
    (-1 : F) ^ (m - 1) * b ^ (m - 1) * γ *
      (∑ i : Fin N, ∑ j, if j.val - i.val = m - 1 then
        (∏ k ∈ Finset.Icc i j, w k) * ∑ k ∈ Finset.Icc i j, ν k else 0) -
    (-1 : F) ^ m * b ^ m * γ *
      (∑ i : Fin N, ∑ j, ∑ k, ∑ l,
        if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
          ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
          (∏ s ∈ Finset.Icc i j, w s) *
            (PowerSeries.constantCoeff (M k l) * ∏ s ∈ Finset.Icc k l, w s) else 0)

/-- The actual open overlap expression is the sum of five complete local
matrix-window functionals. The exterior terms have the larger window size. -/
theorem normalOpenOverlapCharge_windows {N d : ℕ} (hd : 0 < d) {F : Type*} [Field F]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (δ : PowerSeries F → PowerSeries F) (b γ : F) :
    let w := fun p : PowerSeries F => (PowerSeries.constantCoeff p)⁻¹
    let ν := fun p : PowerSeries F => PowerSeries.coeff 1 p * w p
    let longF := fun V : Matrix (Fin (d + 2)) (Fin (d + 2)) (PowerSeries F) =>
      PowerSeries.constantCoeff (δ (V 0 (Fin.last (d + 1)))) * ∏ k, w (V k k)
    let vertexF := fun V : Matrix (Fin (d + 1)) (Fin (d + 1)) (PowerSeries F) =>
      (∏ k, w (V k k)) * ∑ k, ν (V k k)
    let innerF := fun V : Matrix (Fin (d + 1)) (Fin (d + 1)) (PowerSeries F) =>
      (∏ k, w (V k k)) * ∑ t : Fin d,
        PowerSeries.constantCoeff (V t.castSucc t.succ) * w (V t.castSucc t.castSucc) *
          w (V t.succ t.succ)
    let leftF := fun V : Matrix (Fin (d + 2)) (Fin (d + 2)) (PowerSeries F) =>
      (∏ k : Fin (d + 1), w (V k.succ k.succ)) *
        (PowerSeries.constantCoeff (V 0 1) * w (V 0 0) * w (V 1 1))
    let rightF := fun V : Matrix (Fin (d + 2)) (Fin (d + 2)) (PowerSeries F) =>
      (∏ k : Fin (d + 1), w (V k.castSucc k.castSucc)) *
        (PowerSeries.constantCoeff (V (Fin.last d).castSucc (Fin.last (d + 1))) *
          w (V (Fin.last d).castSucc (Fin.last d).castSucc) *
          w (V (Fin.last (d + 1)) (Fin.last (d + 1))))
    normalOpenOverlapCharge M δ b γ (d + 1) =
      (-1 : F) ^ (d + 1) * b ^ (d + 1) *
        (∑ s : Fin (N - (d + 1)),
          longF (contiguousMatrixWindow M (d + 2) ⟨s.val, by have := s.isLt; omega⟩)) -
      (-1 : F) ^ d * b ^ d * γ *
        (∑ s : Fin (N - d),
          vertexF (contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩)) -
      (-1 : F) ^ (d + 1) * b ^ (d + 1) * γ *
        ((∑ s : Fin (N - d),
            innerF (contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩)) +
          (∑ s : Fin (N - d - 1),
            leftF (contiguousMatrixWindow M (d + 2) ⟨s.val, by have := s.isLt; omega⟩)) +
          (∑ s : Fin (N - d - 1),
            rightF (contiguousMatrixWindow M (d + 2) ⟨s.val, by have := s.isLt; omega⟩))) := by
  let w := fun p : PowerSeries F => (PowerSeries.constantCoeff p)⁻¹
  let ν := fun p : PowerSeries F => PowerSeries.coeff 1 p * w p
  have hl := matrix_interval_charge_windows (d + 1) M
    (fun p => PowerSeries.constantCoeff (δ p)) w
  have hv := matrix_vertex_charge_windows d M w ν
  have ho := matrix_overlap_charge_windows hd M w (fun p => PowerSeries.constantCoeff p)
  have hp (i j : Fin N) : j.val - i.val = d ↔ i.val ≤ j.val ∧ j.val - i.val = d := by omega
  have hover : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
      if j.val - i.val = d ∧ l.val = k.val + 1 ∧
        ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
        (∏ s ∈ Finset.Icc i j, w (M s s)) *
          (PowerSeries.constantCoeff (M k l) * ∏ s ∈ Finset.Icc k l, w (M s s)) else 0) =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
      if j.val - i.val = d ∧ l.val = k.val + 1 ∧
        ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
        (∏ s ∈ Finset.Icc i j, w (M s s)) *
          (PowerSeries.constantCoeff (M k l) * w (M k k) * w (M l l)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : l.val = k.val + 1
    · rw [adjacent_pair_interval_product (fun s => w (M s s)) k l h]
      simp only [mul_assoc]
    · simp only [h, false_and, and_false, ite_false]
  have hcc_ite (p : Prop) [Decidable p] (x y : PowerSeries F) :
      PowerSeries.constantCoeff (if p then x else y) =
        if p then PowerSeries.constantCoeff x else PowerSeries.constantCoeff y := by
    split_ifs <;> rfl
  dsimp only
  unfold normalOpenOverlapCharge
  simp only [Nat.add_sub_cancel, map_sum, hcc_ite, map_mul, map_prod, map_zero,
    PowerSeries.constantCoeff_inv]
  rw [hover, ho]
  simp only [← hp] at hv
  rw [hv, hl]

end SkewCornerDescent.Matrix
