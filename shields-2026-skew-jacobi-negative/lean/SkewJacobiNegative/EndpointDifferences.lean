/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.SmallRowRigidity
import SkewJacobiNegative.BorderCoefficients

/-!
# Endpoint differences

Actual Laplace expansions and cofactor label bounds in `eq:levels` and
`lem:endpoint-top` of `shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative.BetaDiagram

open scoped BigOperators
variable {n : ℕ}

/-- Difference of the two actual positive endpoint extensions. -/
noncomputable def endpointDifference (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) : CompleteRing :=
  (D.extendTop t ht).schur - (D.extendBottom t ht).schur

/-- The unsigned minor at an actual board site. -/
noncomputable def unsignedMinor (D : BetaDiagram (n + 1))
    (i j : Fin (n + 1)) : CompleteRing :=
  (D.matrix.submatrix i.succAbove j.succAbove).det

set_option backward.isDefEq.respectTransparency false in
/-- A top-row minor is unchanged by a top endpoint extension. -/
theorem extendTop_unsignedMinor (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) (j : Fin (n + 1)) :
    (D.extendTop t ht).unsignedMinor 0 j = D.unsignedMinor 0 j := by
  unfold unsignedMinor
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  simp [matrix, extendTop, Fin.zero_succAbove, Fin.succ_ne_zero]

set_option backward.isDefEq.respectTransparency false in
/-- A last-column minor is unchanged by a bottom endpoint extension. -/
theorem extendBottom_unsignedMinor (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) (i : Fin (n + 1)) :
    (D.extendBottom t ht).unsignedMinor i (Fin.last n) =
      D.unsignedMinor i (Fin.last n) := by
  unfold unsignedMinor
  congr 1
  ext a b
  simp [matrix, extendBottom, Fin.succAbove_last, Fin.castSucc_ne_last]

set_option backward.isDefEq.respectTransparency false in
/-- `eq:levels`: the common moving corner cancels, with every other term retained. -/
theorem endpointDifference_levels (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht =
      (∑ j ∈ Finset.univ.erase (Fin.last n),
        complete (D.row 0 - D.col j + t) * D.cofactor 0 j) -
      ∑ i ∈ Finset.univ.erase 0,
        complete (D.row i - D.col (Fin.last n) + t) * D.cofactor i (Fin.last n) := by
  classical
  have htop : (D.extendTop t ht).schur =
      ∑ j : Fin (n + 1), complete (D.row 0 - D.col j + t) * D.cofactor 0 j := by
    unfold schur
    rw [Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    have hm := D.extendTop_unsignedMinor t ht j
    change (-1) ^ j.val * complete ((D.row 0 + t) - D.col j) *
      (D.extendTop t ht).unsignedMinor 0 j = _
    rw [hm]
    simp only [cofactor, unsignedMinor, Fin.val_zero, zero_add]
    rw [show D.row 0 + t - D.col j = D.row 0 - D.col j + t by ring]
    ring
  have hbottom : (D.extendBottom t ht).schur =
      ∑ i : Fin (n + 1), complete (D.row i - D.col (Fin.last n) + t) *
        D.cofactor i (Fin.last n) := by
    unfold schur
    rw [Matrix.det_succ_column _ (Fin.last n)]
    apply Finset.sum_congr rfl
    intro i _
    have he : (D.extendBottom t ht).matrix i (Fin.last n) =
        complete (D.row i - D.col (Fin.last n) + t) := by
      simp only [matrix, Matrix.of_apply, extendBottom, ite_true]
      congr 1
      ring
    rw [he]
    have hm : ((D.extendBottom t ht).matrix.submatrix
        i.succAbove (Fin.last n).succAbove).det =
        (D.matrix.submatrix i.succAbove (Fin.last n).succAbove).det :=
      D.extendBottom_unsignedMinor t ht i
    rw [hm]
    simp only [cofactor, Fin.val_last]
    ring
  unfold endpointDifference
  rw [htop, hbottom,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (Fin.last n)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
  ring

/-- Every actual first-row cofactor label is bounded by the second-row offset. -/
theorem first_row_minor_labels (D : BetaDiagram (n + 2))
    (j : Fin (n + 2)) (v : ℕ+) (hv : v ∈ (D.unsignedMinor 0 j).vars) :
    (v.val : ℤ) ≤ D.row (0 : Fin (n + 1)).succ - D.col (Fin.last (n + 1)) := by
  by_contra h
  apply (not_mem_vars_det _ v ?_) hv
  intro a b
  change v ∉ (complete (D.row ((0 : Fin (n + 2)).succAbove a) -
    D.col (j.succAbove b))).vars
  rw [Fin.zero_succAbove, mem_vars_complete_iff]
  have hr := D.row_strictAnti.antitone
    (show (0 : Fin (n + 1)).succ ≤ a.succ by simp [Fin.le_def])
  have hc := D.col_strictAnti.antitone (Fin.le_last (j.succAbove b))
  omega

/-- Every actual last-column cofactor label is bounded by the penultimate-column offset. -/
theorem last_column_minor_labels (D : BetaDiagram (n + 2))
    (i : Fin (n + 2)) (v : ℕ+)
    (hv : v ∈ (D.unsignedMinor i (Fin.last (n + 1))).vars) :
    (v.val : ℤ) ≤ D.row 0 - D.col (Fin.last n).castSucc := by
  by_contra h
  apply (not_mem_vars_det _ v ?_) hv
  intro a b
  change v ∉ (complete (D.row (i.succAbove a) -
    D.col ((Fin.last (n + 1)).succAbove b))).vars
  rw [Fin.succAbove_last, mem_vars_complete_iff]
  have hr := D.row_strictAnti.antitone (Fin.zero_le (i.succAbove a))
  have hc := D.col_strictAnti.antitone
    (show b.castSucc ≤ (Fin.last n).castSucc from
      Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last b))
  omega

/-- Signed cofactors cannot acquire a generator from their constant sign. -/
theorem cofactor_vars_subset (D : BetaDiagram (n + 1)) (i j : Fin (n + 1)) :
    (D.cofactor i j).vars ⊆ (D.unsignedMinor i j).vars := by
  intro v hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with h | h
  · have hh := MvPolynomial.vars_pow (-1 : CompleteRing) (i.val + j.val) h
    simpa using hh
  · exact h

/-- Literal symmetry identifies the two endpoint extensions by a half-turn. -/
theorem extendTop_rotation_extendBottom_of_symmetric (D : BetaDiagram (n + 1))
    (hD : D.Symmetric) (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).RotationEquivalent (D.extendBottom t ht) := by
  obtain ⟨c, hr, hc⟩ := hD
  refine ⟨c, ?_, ?_⟩
  · intro i
    have hi : i.rev = Fin.last n ↔ i = 0 := by
      rw [Fin.rev_eq_iff, Fin.rev_last]
    simp only [extendTop, extendBottom]
    rw [hr i]
    by_cases h : i = 0 <;> simp [h, hi] <;> omega
  · exact hc

/-- Symmetric diagrams have identically zero endpoint difference, for every shift. -/
theorem endpointDifference_eq_zero_of_symmetric (D : BetaDiagram (n + 1))
    (hD : D.Symmetric) (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht = 0 := by
  apply sub_eq_zero.mpr
  have h := (D.extendTop t ht).translation_rotate_iff_rotation (D.extendBottom t ht)
  exact (h.mpr (D.extendTop_rotation_extendBottom_of_symmetric hD t ht)).schur_eq.trans
    (D.extendBottom t ht).rotate_schur

/-- Nonnegative endpoint rigidity gives an actual nonzero difference, not a minor certificate. -/
theorem endpointDifference_ne_zero_nonnegative (D : BetaDiagram (n + 2))
    (hC : D.Connected) (hN : D.Nonnegative) (hS : ¬ D.Symmetric)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  intro hz
  have he := sub_eq_zero.mp hz
  rcases (D.extendTop t ht).nonnegative_rigidity_same_order (D.extendBottom t ht)
    (D.extendTop_connected hC t ht) (D.extendBottom_connected hC t ht)
    (D.extendTop_nonnegative hN t ht) he with htr | hrot
  · exact D.extendTop_not_translation_extendBottom t ht htr
  · exact hS (D.symmetric_of_extendTop_rotation_extendBottom t ht hrot)

/-- The same implication uses the actual small-row theorem, with no index sign premise. -/
theorem endpointDifference_ne_zero_small_rows (D : BetaDiagram (n + 2))
    (hC : D.Connected) (hn : n + 2 ≤ 3) (hS : ¬ D.Symmetric)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  intro hz
  have he := sub_eq_zero.mp hz
  rcases (D.extendTop t ht).small_rows_rigidity_same_order (D.extendBottom t ht)
    (D.extendTop_connected hC t ht) (D.extendBottom_connected hC t ht) hn he
    with htr | hrot
  · exact D.extendTop_not_translation_extendBottom t ht htr
  · exact hS (D.symmetric_of_extendTop_rotation_extendBottom t ht hrot)

end SkewJacobiNegative.BetaDiagram
