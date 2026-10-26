/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalBlockRankBounds
import Mathlib.Order.Interval.Finset.Fin

/-!
# Complete actual interval cardinality

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original complementary row bijection partitions an entire component
interval into its retained selected pivots and every removed row. This
recovers physical source-rank information from complete interval sizes.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Removed interval rows plus the actual selected pivots count the entire
source interval, including both complete endpoint components. -/
theorem original_interval_card_balance {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P) :
    Fintype.card (OriginalResponseInterval (hD := hD) P (some a) (some b)) +
      Fintype.card {s : OriginalSelectedBlocks (hD := hD) P //
        interiorBlock P a.val.val ≤ interiorBlock P s.val.val ∧
        interiorBlock P s.val.val ≤ interiorBlock P b.val.val} =
      (interiorBlockLast P b.val.val).val + 1 - a.val.val.val := by
  classical
  let label : OriginalSelectedBlocks (hD := hD) P ⊕ OriginalRemainingIndices (hD := hD) P → ℕ
    | .inl s => interiorBlock P s.val.val
    | .inr r => interiorBlock P r.1.val
  let between := fun k : ℕ => interiorBlock P a.val.val ≤ k ∧ k ≤ interiorBlock P b.val.val
  have hlabel (x) : interiorBlock P (complementaryRowEquiv (hD := hD) P x) = label x := by
    change interiorBlock P (originalBlockIndex P (complementaryRowPartition P x)) = label x
    rw [originalBlockIndex_label]
    cases x <;> rfl
  let e := (complementaryRowEquiv (hD := hD) P).subtypeEquiv
    (p := fun x => between (label x))
    (q := fun j => a.val.val ≤ j ∧ j ≤ interiorBlockLast P b.val.val)
    (fun x => by
      dsimp only [between]
      rw [← hlabel, interiorBlock_label_le_iff_first_le,
        interiorBlock_label_le_iff_le_last, a.val.property])
  have hcard := Fintype.card_congr e
  have hsplit := Fintype.card_congr
    (Equiv.subtypeSum (p := fun x => between (label x)))
  rw [Fintype.card_sum] at hsplit
  let eR : {r : OriginalRemainingIndices (hD := hD) P // between (label (.inr r))} ≃
      OriginalResponseInterval (hD := hD) P (some a) (some b) :=
    { toFun := fun r => ⟨⟨r.val, by
        change (interiorBlock P r.val.1.val : ℤ) <
          (interiorBlock P b.val.val : ℤ) + 1
        have := r.property.2
        dsimp only [between, label] at this
        omega⟩, by
        change (interiorBlock P a.val.val : ℤ) - 1 <
          (interiorBlock P r.val.1.val : ℤ)
        have := r.property.1
        dsimp only [between, label] at this
        omega⟩
      invFun := fun r => ⟨r.val.val, by
        have hupper := r.val.property
        have hlower := r.property
        change (interiorBlock P r.val.val.1.val : ℤ) <
          (interiorBlock P b.val.val : ℤ) + 1 at hupper
        change (interiorBlock P a.val.val : ℤ) - 1 <
          (interiorBlock P r.val.val.1.val : ℤ) at hlower
        dsimp only [between, label]
        constructor <;> omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hrem := Fintype.card_congr eR
  have hrows : Fintype.card {j : Fin n // a.val.val ≤ j ∧ j ≤ interiorBlockLast P b.val.val} =
      (interiorBlockLast P b.val.val).val + 1 - a.val.val.val := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter fun j : Fin n =>
        a.val.val ≤ j ∧ j ≤ interiorBlockLast P b.val.val) =
        Finset.Icc a.val.val (interiorBlockLast P b.val.val) := by
      ext j
      simp
    rw [heq]
    exact Fin.card_Icc _ _
  dsimp only [between, label] at hsplit hcard hrem
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
