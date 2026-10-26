/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularChambers

/-!
# Simultaneous sign control at anchor roots

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Higher triangular responses can be assigned a common sign at every one of finitely many
anchor roots simultaneously. All coordinates through the anchor remain fixed, and root
functions depend only on earlier coordinates, never on the coordinates being chosen.

Sorry-free.
-/

namespace SkewCornerDescent

/-- Evaluate at a specified root of the anchor coordinate, keeping all other coordinates literal. -/
def anchorAssignment {α : Type*} (K : ℕ) (root : α → (ℕ → ℝ) → ℝ)
    (a : α) (x : ℕ → ℝ) : ℕ → ℝ := Function.update x K (root a x)

/-- Root substitution preserves the triangular dependence of every strictly higher response. -/
theorem anchor_correction_locality {ι α : Type*} (K : ℕ)
    (top : ι → ℕ) (htop : ∀ i, K < top i)
    (correction : ι → (ℕ → ℝ) → ℝ)
    (hcorrection : ∀ i x y, (∀ j, j < top i → x j = y j) → correction i x = correction i y)
    (root : α → (ℕ → ℝ) → ℝ)
    (hroot : ∀ a x y, (∀ j, j < K → x j = y j) → root a x = root a y)
    (i : ι) (a : α) (x y : ℕ → ℝ) (hxy : ∀ j, j < top i → x j = y j) :
    correction i (anchorAssignment K root a x) = correction i (anchorAssignment K root a y) := by
  apply hcorrection
  intro j hj
  by_cases he : j = K
  · subst j
    simp only [anchorAssignment, Function.update_self]
    apply hroot
    intro j hj
    exact hxy j (lt_trans hj (htop i))
  · simp only [anchorAssignment, Function.update_of_ne he]
    exact hxy j hj

/-- Choose higher coordinates to give every higher response the chosen sign at every root. -/
theorem exists_signed_above_anchor {ι α : Type*} [Finite ι] [Finite α]
    (K : ℕ) (top : ι → ℕ) (htop : ∀ i, K < top i)
    (correction : ι → (ℕ → ℝ) → ℝ)
    (hcorrection : ∀ i x y, (∀ j, j < top i → x j = y j) → correction i x = correction i y)
    (root : α → (ℕ → ℝ) → ℝ)
    (hroot : ∀ a x y, (∀ j, j < K → x j = y j) → root a x = root a y)
    (base : ℕ → ℝ) (positive : Bool) :
    ∃ x : ℕ → ℝ, (∀ j, j ≤ K → x j = base j) ∧
      ∀ i a, responseSign positive
        (anchorAssignment K root a x (top i) + correction i (anchorAssignment K root a x)) := by
  obtain ⟨x, hx, hs⟩ := exists_signed_triangular_assignment
    (fun ia : ι × α => top ia.1)
    (fun ia x => correction ia.1 (anchorAssignment K root ia.2 x))
    (K + 1) (fun ia => htop ia.1)
    (fun ia x y hxy => anchor_correction_locality K top htop correction hcorrection
      root hroot ia.1 ia.2 x y hxy) base positive
  refine ⟨x, fun j hj => hx j (by omega), ?_⟩
  intro i a
  simpa only [anchorAssignment, Function.update_of_ne (Nat.ne_of_gt (htop i))] using hs (i, a)

/-- The root functions themselves are unchanged by that choice of higher coordinates. -/
theorem anchor_roots_eq_of_agree_through {α : Type*} (K : ℕ)
    (root : α → (ℕ → ℝ) → ℝ)
    (hroot : ∀ a x y, (∀ j, j < K → x j = y j) → root a x = root a y)
    (x y : ℕ → ℝ) (hxy : ∀ j, j ≤ K → x j = y j) (a : α) :
    root a x = root a y :=
  hroot a x y (fun j hj => hxy j hj.le)

/-- A response below the anchor cannot see either root substitution or higher-coordinate choices. -/
theorem response_below_anchor_preserved {α : Type*} (K J : ℕ) (hJ : J < K)
    (correction : (ℕ → ℝ) → ℝ)
    (hcorrection : ∀ x y, (∀ j, j < J → x j = y j) → correction x = correction y)
    (root : α → (ℕ → ℝ) → ℝ) (a : α)
    (x base : ℕ → ℝ) (hxy : ∀ j, j ≤ K → x j = base j) :
    anchorAssignment K root a x J + correction (anchorAssignment K root a x) =
      base J + correction base := by
  have hc : correction (anchorAssignment K root a x) = correction base := by
    apply hcorrection
    intro j hj
    simp only [anchorAssignment, Function.update_of_ne (by omega : j ≠ K)]
    exact hxy j (by omega)
  rw [hc]
  simp only [anchorAssignment, Function.update_of_ne (Nat.ne_of_lt hJ), hxy J hJ.le]

/-- Distinct finite real labels have a unique least exposed label. -/
theorem exists_least_anchor_label {α : Type*} [Finite α] [Nonempty α]
    (label : α → ℝ) (hinj : Function.Injective label) :
    ∃ a, ∀ b, b ≠ a → label a < label b := by
  classical
  let _ := Fintype.ofFinite α
  let S := Finset.univ.image label
  have hS : S.Nonempty := Finset.univ_nonempty.image label
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  refine ⟨a, fun b hba => ?_⟩
  have hb : label b ∈ S := Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
  have hl : label a ≤ label b := ha.trans_le (Finset.min'_le S _ hb)
  exact lt_of_le_of_ne hl (fun he => hba (hinj he.symm))

/-- Distinct finite real labels have a unique greatest exposed label. -/
theorem exists_greatest_anchor_label {α : Type*} [Finite α] [Nonempty α]
    (label : α → ℝ) (hinj : Function.Injective label) :
    ∃ a, ∀ b, b ≠ a → label b < label a := by
  classical
  let _ := Fintype.ofFinite α
  let S := Finset.univ.image label
  have hS : S.Nonempty := Finset.univ_nonempty.image label
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.max'_mem S hS)
  refine ⟨a, fun b hba => ?_⟩
  have hb : label b ∈ S := Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
  have hl : label b ≤ label a := (Finset.le_max' S _ hb).trans ha.symm.le
  exact lt_of_le_of_ne hl (fun he => hba (hinj he))

/-- At the least label other same-anchor responses are negative for a positive cap product. -/
theorem least_anchor_response_negative {α : Type*} (label : α → ℝ) (a : α)
    (hleast : ∀ b, b ≠ a → label a < label b) {F A : ℝ} (hF : 0 < F)
    (b : α) (hba : b ≠ a) :
    (F * label a - A) + A - F * label b < 0 := by
  have h := mul_pos hF (sub_pos.mpr (hleast b hba))
  nlinarith

/-- At the greatest label every other same-anchor response is positive on the same assignment. -/
theorem greatest_anchor_response_positive {α : Type*} (label : α → ℝ) (a : α)
    (hgreatest : ∀ b, b ≠ a → label b < label a) {F A : ℝ} (hF : 0 < F)
    (b : α) (hba : b ≠ a) :
    0 < (F * label a - A) + A - F * label b := by
  have h := mul_pos hF (sub_pos.mpr (hgreatest b hba))
  nlinarith

end SkewCornerDescent
