/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FiveExceptionalFamilies

/-!
# Negative partition need not be a Schur invariant

The actual thirteen-cell pair of `ex:negative-shape-change` in
`shields-2026-skew-jacobi-negative.tex`, including its common-beta boundary.
-/

namespace SkewJacobiNegative.NegativePartitionExample

/-- The common-beta boundary parameters of the first exceptional five-row family. -/
def parameters : FiveExceptional.Parameters where
  q := 1
  b := 1
  g := 2
  q_pos := by decide
  q_le_b := by decide
  b_lt_g := by decide

def first : BetaDiagram 5 := FiveExceptional.F parameters false

def second : BetaDiagram 5 := FiveExceptional.H parameters false

/-- Both functions are equal by the uniform family identity, not a finite census. -/
theorem schur_eq : first.schur = second.schur := FiveExceptional.F_schur_eq_H parameters false

@[simp] theorem first_partition : negativePartition first = [3, 1, 1] := by decide

@[simp] theorem second_partition : negativePartition second = [3, 2] := by decide

@[simp] theorem first_area : first.area = 13 := by decide

@[simp] theorem second_area : second.area = 13 := by decide

/-- The exact two partitions differ. -/
theorem partition_ne : negativePartition first ≠ negativePartition second := by
  rw [first_partition, second_partition]
  decide

/-- They are not conjugate in the first direction. -/
theorem not_conjugate : ¬ PartitionsConjugate (negativePartition first)
    (negativePartition second) := by
  intro h
  have h0 := h 0
  norm_num [first_partition, second_partition] at h0

/-- They are not conjugate in the reverse direction either. -/
theorem not_conjugate_reverse : ¬ PartitionsConjugate (negativePartition second)
    (negativePartition first) := by
  intro h
  have h1 := h 1
  norm_num [first_partition, second_partition] at h1

/-- The displayed pair witnesses failure even after identifying conjugate partitions. -/
theorem negative_partition_not_invariant :
    ∃ D E : BetaDiagram 5, D.Connected ∧ E.Connected ∧ D.schur = E.schur ∧
      D.area = 13 ∧ E.area = 13 ∧ negativePartition D ≠ negativePartition E ∧
      ¬ PartitionsConjugate (negativePartition D) (negativePartition E) ∧
      ¬ PartitionsConjugate (negativePartition E) (negativePartition D) :=
  ⟨first, second, FiveExceptional.F_connected parameters false,
    FiveExceptional.H_connected parameters false,
    schur_eq, first_area, second_area, partition_ne, not_conjugate, not_conjugate_reverse⟩

end SkewJacobiNegative.NegativePartitionExample
