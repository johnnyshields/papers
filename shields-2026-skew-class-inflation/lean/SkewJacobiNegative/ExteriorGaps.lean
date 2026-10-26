/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/ExteriorGaps.lean

import SkewJacobiNegative.ConnectedIrreducibility
import SkewJacobiNegative.PrivateEntries

/-!
# Exterior beta margins

Actual geometric restrictions and extensions for `lem:exterior-gaps` and
`thm:nonnegative-rigidity`.  The corner restriction enters the positive-row
class only through a proved geometric condition.  Endpoint extensions
retain the nonnegative-index hypothesis and connectedness.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

variable {n : ℕ}

/-- Literal half-turn of strict beta lists, using reflection constant zero. -/
def rotate (D : BetaDiagram n) : BetaDiagram n where
  row i := -D.col i.rev
  col i := -D.row i.rev
  row_strictAnti := by
    intro i j hij
    have ht := D.col_strictAnti (Fin.rev_lt_rev.mpr hij)
    dsimp
    omega
  col_strictAnti := by
    intro i j hij
    have ht := D.row_strictAnti (Fin.rev_lt_rev.mpr hij)
    dsimp
    omega
  row_nonempty i := by have := D.row_nonempty i.rev; omega

set_option backward.isDefEq.respectTransparency false in
/-- Reversing both determinant axes after transposing produces the actual half-turn. -/
theorem rotate_schur (D : BetaDiagram n) : D.rotate.schur = D.schur := by
  have hm : D.rotate.matrix = D.matrix.transpose.submatrix Fin.revPerm Fin.revPerm := by
    apply Matrix.ext
    intro i j
    simp only [matrix, rotate, Matrix.of_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, Fin.revPerm_apply]
    congr 1
    ring
  unfold schur
  rw [hm, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

/-- Nonnegative indices are unchanged by the transposed reversed board. -/
theorem rotate_nonnegative (D : BetaDiagram n) (hN : D.Nonnegative) :
    D.rotate.Nonnegative := by
  intro i j
  have ht := hN j.rev i.rev
  change -D.row j.rev ≤ -D.col i.rev
  omega

/-- The literal half-turn preserves every adjacent overlap. -/
theorem rotate_connected (D : BetaDiagram n) (hD : D.Connected) :
    D.rotate.Connected := by
  refine ⟨hD.1, ?_⟩
  intro i hi
  let j : Fin n := (⟨i.val + 1, hi⟩ : Fin n).rev
  have hj : j.val + 1 < n := by
    dsimp [j, Fin.rev]
    omega
  have he : (⟨j.val + 1, hj⟩ : Fin n) = i.rev := by
    apply Fin.ext
    dsimp [j, Fin.rev]
    omega
  have ht := hD.2 j hj
  rw [he] at ht
  change -D.row i.rev ≤ -D.col (⟨i.val + 1, hi⟩ : Fin n).rev
  dsimp [j] at ht
  omega

/-- The private largest label does not change under a half-turn. -/
theorem rotate_largestLabel (D : BetaDiagram (n + 1)) :
    D.rotate.largestLabel = D.largestLabel := by
  simp [largestLabel, rotate, Fin.rev_zero, Fin.rev_last]
  ring

/-- Strict positive corner diagonal is the exact hypothesis for nonempty corner rows. -/
def PositiveCorner (D : BetaDiagram (n + 1)) : Prop :=
  ∀ i : Fin n, D.col i.castSucc < D.row i.succ

/-- The maximal corner interpreted as an actual diagram, when its rows are nonempty. -/
def cornerDiagram (D : BetaDiagram (n + 1)) (h : D.PositiveCorner) : BetaDiagram n where
  row i := D.row i.succ
  col i := D.col i.castSucc
  row_strictAnti := D.row_strictAnti.comp_strictMono Fin.strictMono_succ
  col_strictAnti := D.col_strictAnti.comp_strictMono Fin.strictMono_castSucc
  row_nonempty := h

/-- Nonnegative-index diagrams of at least three rows have strictly positive corner rows. -/
theorem positiveCorner_of_nonnegative (D : BetaDiagram (n + 3)) (hD : D.Nonnegative) :
    D.PositiveCorner := by
  intro i
  by_cases hi : i = 0
  · subst i
    have hr := D.row_strictAnti
      (show (0 : Fin (n + 2)).succ < Fin.last (n + 2) by
        simp only [Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_last]
        omega)
    have hn := hD (Fin.last (n + 2)) 0
    change D.col 0 < D.row (0 : Fin (n + 2)).succ
    omega
  · have hc := D.col_strictAnti
      (show (0 : Fin (n + 3)) < i.castSucc by
        simpa only [Fin.lt_def, Fin.val_zero, Fin.val_castSucc] using
          (Fin.pos_iff_ne_zero.mpr hi))
    have hn := hD i.succ 0
    omega

/-- The restriction is exactly the unsigned polynomial recovered by differentiation. -/
theorem cornerDiagram_schur (D : BetaDiagram (n + 1)) (h : D.PositiveCorner) :
    (D.cornerDiagram h).schur = D.cornerPolynomial := rfl

/-- The core retains all nonnegative entries, not merely its diagonal overlaps. -/
theorem cornerDiagram_nonnegative (D : BetaDiagram (n + 1))
    (hN : D.Nonnegative) (h : D.PositiveCorner) :
    (D.cornerDiagram h).Nonnegative := fun i j => hN i.succ j.castSucc

/-- A nonempty nonnegative corner core is connected by its actual entries. -/
theorem cornerDiagram_connected (D : BetaDiagram (n + 1))
    (hN : D.Nonnegative) (h : D.PositiveCorner) (hn : 0 < n) :
    (D.cornerDiagram h).Connected := by
  refine ⟨hn, ?_⟩
  intro i hi
  exact hN (⟨i.val + 1, hi⟩ : Fin n).succ i.castSucc

/-- Increase the largest row beta by a positive exterior gap. -/
def extendTop (T : BetaDiagram (n + 1)) (d : ℤ) (hd : 0 < d) : BetaDiagram (n + 1) where
  row i := if i = 0 then T.row i + d else T.row i
  col := T.col
  row_strictAnti := by
    intro i j hij
    have ht := T.row_strictAnti hij
    have hj : j ≠ 0 := by intro h; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij
    by_cases hi : i = 0
    · subst i
      simp only [ite_true, hj, ite_false]
      omega
    · simpa only [hi, hj, ite_false] using ht
  col_strictAnti := T.col_strictAnti
  row_nonempty i := by
    have ht := T.row_nonempty i
    by_cases hi : i = 0
    · subst i
      simp only [ite_true]
      omega
    · simpa only [hi, ite_false] using ht

/-- Decrease the smallest column beta by a positive exterior gap. -/
def extendBottom (T : BetaDiagram (n + 1)) (d : ℤ) (hd : 0 < d) : BetaDiagram (n + 1) where
  row := T.row
  col i := if i = Fin.last n then T.col i - d else T.col i
  row_strictAnti := T.row_strictAnti
  col_strictAnti := by
    intro i j hij
    have ht := T.col_strictAnti hij
    have hi : i ≠ Fin.last n := by
      intro h
      subst i
      exact (not_lt_of_ge (Fin.le_last j)) hij
    by_cases hj : j = Fin.last n
    · subst j
      simp only [hi, ite_false, ite_true]
      omega
    · simpa only [hi, hj, ite_false] using ht
  row_nonempty i := by
    have ht := T.row_nonempty i
    by_cases hi : i = Fin.last n
    · subst i
      simp only [ite_true]
      omega
    · simpa only [hi, ite_false] using ht

/-- An endpoint row extension preserves all nonnegative Jacobi--Trudi indices. -/
theorem extendTop_nonnegative (T : BetaDiagram (n + 1)) (hT : T.Nonnegative)
    (d : ℤ) (hd : 0 < d) : (T.extendTop d hd).Nonnegative := by
  intro i j
  have ht := hT i j
  change T.col j ≤ if i = 0 then T.row i + d else T.row i
  split_ifs <;> omega

/-- The other endpoint extension preserves the same class. -/
theorem extendBottom_nonnegative (T : BetaDiagram (n + 1)) (hT : T.Nonnegative)
    (d : ℤ) (hd : 0 < d) : (T.extendBottom d hd).Nonnegative := by
  intro i j
  have ht := hT i j
  change (if j = Fin.last n then T.col j - d else T.col j) ≤ T.row i
  split_ifs <;> omega

/-- Neither endpoint extension destroys adjacent overlaps. -/
theorem extendTop_connected (T : BetaDiagram (n + 1)) (hT : T.Connected)
    (d : ℤ) (hd : 0 < d) : (T.extendTop d hd).Connected := by
  refine ⟨hT.1, ?_⟩
  intro i hi
  have ht := hT.2 i hi
  change T.col i ≤ if (⟨i.val + 1, hi⟩ : Fin (n + 1)) = 0 then
    T.row ⟨i.val + 1, hi⟩ + d else T.row ⟨i.val + 1, hi⟩
  have hn : (⟨i.val + 1, hi⟩ : Fin (n + 1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    omega
  simpa only [hn, ite_false] using ht

/-- The last column beta is never an adjacent overlap's upper row index. -/
theorem extendBottom_connected (T : BetaDiagram (n + 1)) (hT : T.Connected)
    (d : ℤ) (hd : 0 < d) : (T.extendBottom d hd).Connected := by
  refine ⟨hT.1, ?_⟩
  intro i hi
  have ht := hT.2 i hi
  change (if i = Fin.last n then T.col i - d else T.col i) ≤ T.row ⟨i.val + 1, hi⟩
  split_ifs <;> omega

/-- The two different endpoint extensions cannot be translates. -/
theorem extendTop_not_translation_extendBottom (T : BetaDiagram (n + 2))
    (d : ℤ) (hd : 0 < d) :
    ¬ (T.extendTop d hd).TranslationEquivalent (T.extendBottom d hd) := by
  rintro ⟨c, hr, hc⟩
  have h₀ := hc 0
  have hn : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]
  change T.col 0 = (if (0 : Fin (n + 2)) = Fin.last (n + 1) then
    T.col 0 - d else T.col 0) + c at h₀
  simp only [hn, ite_false] at h₀
  have h₁ := hr 0
  change (if (0 : Fin (n + 2)) = 0 then T.row 0 + d else T.row 0) = T.row 0 + c at h₁
  simp only [ite_true] at h₁
  omega

/-- A rotation between the endpoint extensions forces symmetry of the unextended core. -/
theorem symmetric_of_extendTop_rotation_extendBottom (T : BetaDiagram (n + 1))
    (d : ℤ) (hd : 0 < d)
    (h : (T.extendTop d hd).RotationEquivalent (T.extendBottom d hd)) : T.Symmetric := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    have hi := hr i
    change (if i = 0 then T.row i + d else T.row i) =
      c - (if i.rev = Fin.last n then T.col i.rev - d else T.col i.rev) at hi
    have he : i.rev = Fin.last n ↔ i = 0 := by
      rw [Fin.rev_eq_iff, Fin.rev_last]
    by_cases hz : i = 0
    · rw [ite_eq_left hz, ite_eq_left (he.mpr hz)] at hi
      omega
    · rw [ite_eq_right hz, ite_eq_right (he.not.mpr hz)] at hi
      exact hi
  · intro i
    have hi := hc i
    change T.col i = c - T.row i.rev at hi
    exact hi

/-- The reflection constant of that rotation is read off the unchanged core endpoints. -/
theorem extend_rotation_constant (T : BetaDiagram (n + 1)) (d : ℤ) (hd : 0 < d)
    (c : ℤ)
    (hr : ∀ i, (T.extendTop d hd).row i = c - (T.extendBottom d hd).col i.rev) :
    c = T.row 0 + T.col (Fin.last n) := by
  have h := hr 0
  simp only [extendTop, extendBottom, Fin.rev_zero, ite_true] at h
  omega

/-- Literal exterior row margin of an actual parent. -/
def topMargin (D : BetaDiagram (n + 2)) : ℤ := D.row 0 - D.row (0 : Fin (n + 1)).succ

/-- Literal exterior column margin of the same parent. -/
def bottomMargin (D : BetaDiagram (n + 2)) : ℤ :=
  D.col (Fin.last n).castSucc - D.col (Fin.last (n + 1))

/-- Strict full beta lists make both exterior margins positive. -/
theorem topMargin_pos (D : BetaDiagram (n + 2)) : 0 < D.topMargin := by
  exact sub_pos.mpr (D.row_strictAnti (by simp))

/-- The last two column betas give the second positive margin. -/
theorem bottomMargin_pos (D : BetaDiagram (n + 2)) : 0 < D.bottomMargin := by
  apply sub_pos.mpr
  apply D.col_strictAnti
  simp [Fin.lt_def]

/-- A half-turn interchanges the literal exterior margins. -/
theorem rotate_topMargin (D : BetaDiagram (n + 2)) :
    D.rotate.topMargin = D.bottomMargin := by
  change -D.col (0 : Fin (n + 2)).rev -
      (-D.col ((0 : Fin (n + 1)).succ).rev) =
    D.col (Fin.last n).castSucc - D.col (Fin.last (n + 1))
  rw [Fin.rev_zero, Fin.rev_succ, Fin.rev_zero]
  ring

/-- The other margin transforms in the opposite direction. -/
theorem rotate_bottomMargin (D : BetaDiagram (n + 2)) :
    D.rotate.bottomMargin = D.topMargin := by
  simp [rotate, topMargin, bottomMargin, Fin.rev_last, Fin.rev_castSucc]
  ring

/-- The two next-largest candidate labels are read from the actual exterior sites. -/
theorem exterior_candidate_labels (D : BetaDiagram (n + 2)) :
    D.row (0 : Fin (n + 1)).succ - D.col (Fin.last (n + 1)) =
      D.largestLabel - D.topMargin ∧
    D.row 0 - D.col (Fin.last n).castSucc =
      D.largestLabel - D.bottomMargin := by
  constructor <;> dsimp [largestLabel, topMargin, bottomMargin] <;> ring

/-- Strictly unequal margins isolate the larger remaining label at the second row. -/
theorem topMargin_private (D : BetaDiagram (n + 2))
    (h : D.topMargin < D.bottomMargin) (i j : Fin (n + 2))
    (hcorner : i ≠ 0 ∨ j ≠ Fin.last (n + 1))
    (hsite : i ≠ (0 : Fin (n + 1)).succ ∨ j ≠ Fin.last (n + 1)) :
    D.row i - D.col j < D.largestLabel - D.topMargin := by
  have hr0 := D.row_strictAnti.antitone (Fin.zero_le i)
  have hcLast := D.col_strictAnti.antitone (Fin.le_last j)
  by_cases hi0 : i = 0
  · subst i
    have hj : j ≠ Fin.last (n + 1) := by simpa using hcorner
    have hjle : j ≤ (Fin.last n).castSucc := by
      have hn := Fin.lt_last_iff_ne_last.mpr hj
      have hv : j.val < n + 1 := by simpa only [Fin.lt_def, Fin.val_last] using hn
      change j.val ≤ n
      omega
    have hc := D.col_strictAnti.antitone hjle
    dsimp only [largestLabel, topMargin, bottomMargin] at *
    simp only [Fin.succ_zero_eq_one] at *
    omega
  · have hir : (0 : Fin (n + 1)).succ ≤ i := by
      have hp := Fin.pos_iff_ne_zero.mpr hi0
      simp only [Fin.le_def, Fin.val_succ, Fin.val_zero]
      have hv : 0 < i.val := by simpa only [Fin.lt_def, Fin.val_zero] using hp
      omega
    have hr := D.row_strictAnti.antitone hir
    rcases hsite with hi | hj
    · have hh : (0 : Fin (n + 1)).succ < i := lt_of_le_of_ne hir (Ne.symm hi)
      have hs := D.row_strictAnti hh
      dsimp [largestLabel, topMargin]
      simp only [Fin.succ_zero_eq_one] at *
      omega
    · have hh : j < Fin.last (n + 1) := lt_of_le_of_ne (Fin.le_last j) hj
      have hs := D.col_strictAnti hh
      dsimp [largestLabel, topMargin]
      simp only [Fin.succ_zero_eq_one] at *
      omega

/-- The second-row exterior label is positive even without a density hypothesis. -/
theorem exterior_top_label_pos (D : BetaDiagram (n + 2)) :
    0 < D.largestLabel - D.topMargin := by
  rw [← D.exterior_candidate_labels.1]
  have hr := D.row_nonempty (0 : Fin (n + 1)).succ
  have hc := D.col_strictAnti.antitone (Fin.le_last (0 : Fin (n + 1)).succ)
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Deleting the private second label realizes the top extension of the actual corner. -/
theorem exterior_top_minor (D : BetaDiagram (n + 3)) (hN : D.Nonnegative) :
    D.matrix.submatrix (0 : Fin (n + 2)).succ.succAbove
        (Fin.last (n + 2)).succAbove =
      ((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendTop
        D.topMargin D.topMargin_pos).matrix := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases with
  | zero =>
      simp only [Matrix.submatrix_apply, matrix, Matrix.of_apply,
        Fin.succ_succAbove_zero, Fin.succAbove_last,
        extendTop, cornerDiagram, ite_true]
      congr 1
      unfold topMargin
      ring
  | succ i =>
      simp only [Matrix.submatrix_apply, matrix, Matrix.of_apply,
        Fin.succ_succAbove_succ, Fin.zero_succAbove, Fin.succAbove_last,
        extendTop, cornerDiagram, Fin.succ_ne_zero, ite_false]

set_option backward.isDefEq.respectTransparency false in
/-- Actual polynomial coefficient at the private next-largest top exterior label. -/
theorem exterior_top_coefficient (D : BetaDiagram (n + 3)) (hN : D.Nonnegative)
    (hgap : D.topMargin < D.bottomMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendTop
          D.topMargin D.topMargin_pos).schur := by
  classical
  dsimp only
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
    by have := D.exterior_top_label_pos; omega⟩
  let A := D.matrix.map (eraseGenerator N)
  have hMN : M ≠ N := by
    intro h
    have he := congrArg Subtype.val h
    have := D.topMargin_pos
    have := D.exterior_top_label_pos
    have := D.largestLabel_pos
    dsimp [M, N] at he
    omega
  have hentry : A (0 : Fin (n + 2)).succ (Fin.last (n + 2)) =
      MvPolynomial.X M := by
    change eraseGenerator N
      (complete (D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2)))) = _
    rw [D.exterior_candidate_labels.1, complete_of_pos D.exterior_top_label_pos]
    simp [eraseGenerator, M, hMN]
  have hprivate : ∀ a b, a ≠ (0 : Fin (n + 2)).succ ∨
      b ≠ Fin.last (n + 2) → MvPolynomial.pderiv M (A a b) = 0 := by
    intro a b hab
    by_cases hcorner : a = 0 ∧ b = Fin.last (n + 2)
    · obtain ⟨rfl, rfl⟩ := hcorner
      change MvPolynomial.pderiv M (eraseGenerator N (complete D.largestLabel)) = 0
      rw [complete_of_pos D.largestLabel_pos]
      simp [eraseGenerator, N]
    · have hlt := D.topMargin_private hgap a b (by tauto) hab
      have havoid : M ∉ (D.matrix a b).vars := by
        change M ∉ (complete (D.row a - D.col b)).vars
        rw [mem_vars_complete_iff]
        change ¬ (((D.largestLabel - D.topMargin).toNat : ℕ) : ℤ) = D.row a - D.col b
        have := D.exterior_top_label_pos
        omega
      change MvPolynomial.pderiv M
        (eraseGenerator N (complete (D.row a - D.col b))) = 0
      rw [eraseGenerator_complete]
      split_ifs
      · simp
      · exact MvPolynomial.pderiv_eq_zero_of_notMem_vars havoid
  have hm : A.submatrix (0 : Fin (n + 2)).succ.succAbove
      (Fin.last (n + 2)).succAbove =
      D.matrix.submatrix (0 : Fin (n + 2)).succ.succAbove
        (Fin.last (n + 2)).succAbove := by
    apply Matrix.ext
    intro i j
    change eraseGenerator N
      (complete (D.row ((0 : Fin (n + 2)).succ.succAbove i) -
        D.col ((Fin.last (n + 2)).succAbove j))) =
      complete (D.row ((0 : Fin (n + 2)).succ.succAbove i) -
        D.col ((Fin.last (n + 2)).succAbove j))
    apply eraseGenerator_eq_self
    rw [mem_vars_complete_iff]
    change ¬ ((D.largestLabel.toNat : ℕ) : ℤ) =
      D.row ((0 : Fin (n + 2)).succ.succAbove i) -
        D.col ((Fin.last (n + 2)).succAbove j)
    have hb : (Fin.last (n + 2)).succAbove j ≠ Fin.last (n + 2) :=
      Fin.succAbove_ne _ _
    have hlt := D.index_lt_largestLabel
      ((0 : Fin (n + 2)).succ.succAbove i) ((Fin.last (n + 2)).succAbove j)
      (Or.inr hb)
    have := D.largestLabel_pos
    omega
  change MvPolynomial.pderiv M (eraseGenerator N D.matrix.det) =
    (-1) ^ (n + 3) *
      ((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendTop
        D.topMargin D.topMargin_pos).schur
  rw [eraseGenerator_det, pderiv_det_private_of_derivative_zero A M
    (0 : Fin (n + 2)).succ (Fin.last (n + 2)) hentry hprivate,
    hm, D.exterior_top_minor hN]
  simp only [Fin.val_succ, Fin.val_zero, Fin.val_last, schur]
  rw [show 0 + 1 + (n + 2) = n + 3 by omega]

set_option backward.isDefEq.respectTransparency false in
/-- The private exterior coefficient is nonzero because its actual diagram has nonempty rows. -/
theorem exterior_top_coefficient_ne_zero (D : BetaDiagram (n + 3))
    (hN : D.Nonnegative) (hgap : D.topMargin < D.bottomMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0 := by
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
    by have := D.exterior_top_label_pos; omega⟩
  change MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0
  have hc : MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendTop
          D.topMargin D.topMargin_pos).schur := D.exterior_top_coefficient hN hgap
  rw [hc]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendTop
      D.topMargin D.topMargin_pos).schur_ne_zero)

/-- In the tied-margin case the only remaining sites of that label are the two exterior sites. -/
theorem tied_margin_private (D : BetaDiagram (n + 2))
    (hgap : D.topMargin = D.bottomMargin) (i j : Fin (n + 2))
    (hcorner : i ≠ 0 ∨ j ≠ Fin.last (n + 1))
    (ht : i ≠ 0 ∨ j ≠ (Fin.last n).castSucc)
    (hb : i ≠ (0 : Fin (n + 1)).succ ∨ j ≠ Fin.last (n + 1)) :
    D.row i - D.col j < D.largestLabel - D.topMargin := by
  have hr0 := D.row_strictAnti.antitone (Fin.zero_le i)
  have hcLast := D.col_strictAnti.antitone (Fin.le_last j)
  by_cases hi0 : i = 0
  · subst i
    have hjl : j ≠ Fin.last (n + 1) := by simpa using hcorner
    have hjp : j ≠ (Fin.last n).castSucc := by simpa using ht
    have hjlt : j < (Fin.last n).castSucc := by
      have hvl : j.val < n + 1 := by
        simpa only [Fin.lt_def, Fin.val_last] using Fin.lt_last_iff_ne_last.mpr hjl
      have hvp : j.val ≠ n := by
        intro he
        apply hjp
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_last] using he
      change j.val < n
      omega
    have hc := D.col_strictAnti hjlt
    dsimp only [largestLabel, topMargin, bottomMargin] at *
    simp only [Fin.succ_zero_eq_one] at *
    omega
  · have hir : (0 : Fin (n + 1)).succ ≤ i := by
      have hp := Fin.pos_iff_ne_zero.mpr hi0
      have hv : 0 < i.val := by simpa only [Fin.lt_def, Fin.val_zero] using hp
      change 1 ≤ i.val
      omega
    have hr := D.row_strictAnti.antitone hir
    rcases hb with hi | hj
    · have hs := D.row_strictAnti (lt_of_le_of_ne hir (Ne.symm hi))
      dsimp [largestLabel, topMargin]
      simp only [Fin.succ_zero_eq_one] at *
      omega
    · have hs := D.col_strictAnti (lt_of_le_of_ne (Fin.le_last j) hj)
      dsimp [largestLabel, topMargin]
      simp only [Fin.succ_zero_eq_one] at *
      omega

set_option backward.isDefEq.respectTransparency false in
/-- Actual tied-label quadratic coefficient, expressed without dividing by factorials. -/
theorem exterior_tied_second_derivative (D : BetaDiagram (n + 3))
    (hgap : D.topMargin = D.bottomMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    MvPolynomial.pderiv M (MvPolynomial.pderiv M (eraseGenerator N D.schur)) =
      2 * (D.matrix.submatrix (fun i : Fin (n + 1) => i.succ.succ)
        (fun j : Fin (n + 1) => j.castSucc.castSucc)).det := by
  classical
  dsimp only
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
    by have := D.exterior_top_label_pos; omega⟩
  let A := D.matrix.map (eraseGenerator N)
  have hMN : M ≠ N := by
    intro h
    have he := congrArg Subtype.val h
    have := D.topMargin_pos
    have := D.exterior_top_label_pos
    have := D.largestLabel_pos
    dsimp [M, N] at he
    omega
  have hb : A (0 : Fin (n + 2)).succ (Fin.last (n + 2)) = MvPolynomial.X M := by
    change eraseGenerator N
      (complete (D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2)))) = _
    rw [D.exterior_candidate_labels.1, complete_of_pos D.exterior_top_label_pos]
    simp [eraseGenerator, M, hMN]
  have ht : A 0 (Fin.last (n + 1)).castSucc = MvPolynomial.X M := by
    change eraseGenerator N
      (complete (D.row 0 - D.col (Fin.last (n + 1)).castSucc)) = _
    rw [D.exterior_candidate_labels.2, ← hgap, complete_of_pos D.exterior_top_label_pos]
    simp [eraseGenerator, M, hMN]
  have hprivate : ∀ a b,
      (a ≠ 0 ∨ b ≠ (Fin.last (n + 1)).castSucc) →
      (a ≠ (0 : Fin (n + 2)).succ ∨ b ≠ Fin.last (n + 2)) →
      MvPolynomial.pderiv M (A a b) = 0 := by
    intro a b hab hba
    by_cases hcorner : a = 0 ∧ b = Fin.last (n + 2)
    · obtain ⟨rfl, rfl⟩ := hcorner
      change MvPolynomial.pderiv M (eraseGenerator N (complete D.largestLabel)) = 0
      rw [complete_of_pos D.largestLabel_pos]
      simp [eraseGenerator, N]
    · have hlt := D.tied_margin_private hgap a b (by tauto) hab hba
      have havoid : M ∉ (D.matrix a b).vars := by
        change M ∉ (complete (D.row a - D.col b)).vars
        rw [mem_vars_complete_iff]
        change ¬ (((D.largestLabel - D.topMargin).toNat : ℕ) : ℤ) = D.row a - D.col b
        have := D.exterior_top_label_pos
        omega
      change MvPolynomial.pderiv M
        (eraseGenerator N (complete (D.row a - D.col b))) = 0
      rw [eraseGenerator_complete]
      split_ifs
      · simp
      · exact MvPolynomial.pderiv_eq_zero_of_notMem_vars havoid
  have hm : A.submatrix (fun i : Fin (n + 1) => i.succ.succ)
      (fun j : Fin (n + 1) => j.castSucc.castSucc) =
      D.matrix.submatrix (fun i : Fin (n + 1) => i.succ.succ)
        (fun j : Fin (n + 1) => j.castSucc.castSucc) := by
    apply Matrix.ext
    intro i j
    change eraseGenerator N (complete (D.row i.succ.succ - D.col j.castSucc.castSucc)) =
      complete (D.row i.succ.succ - D.col j.castSucc.castSucc)
    apply eraseGenerator_eq_self
    rw [mem_vars_complete_iff]
    change ¬ ((D.largestLabel.toNat : ℕ) : ℤ) = D.row i.succ.succ - D.col j.castSucc.castSucc
    have hlt := D.index_lt_largestLabel i.succ.succ j.castSucc.castSucc
      (Or.inl (Fin.succ_ne_zero i.succ))
    have := D.largestLabel_pos
    omega
  change MvPolynomial.pderiv M (MvPolynomial.pderiv M (eraseGenerator N D.matrix.det)) =
    2 * (D.matrix.submatrix (fun i : Fin (n + 1) => i.succ.succ)
      (fun j : Fin (n + 1) => j.castSucc.castSucc)).det
  rw [eraseGenerator_det, pderiv_twice_det_exterior_pair A M ht hb hprivate, hm]

set_option backward.isDefEq.respectTransparency false in
/-- The tied coefficient survives even if its complementary diagonal contains zeros. -/
theorem exterior_tied_second_derivative_ne_zero (D : BetaDiagram (n + 3))
    (hN : D.Nonnegative) (hgap : D.topMargin = D.bottomMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    MvPolynomial.pderiv M (MvPolynomial.pderiv M (eraseGenerator N D.schur)) ≠ 0 := by
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
    by have := D.exterior_top_label_pos; omega⟩
  change MvPolynomial.pderiv M (MvPolynomial.pderiv M (eraseGenerator N D.schur)) ≠ 0
  have hc : MvPolynomial.pderiv M (MvPolynomial.pderiv M (eraseGenerator N D.schur)) =
      2 * (D.matrix.submatrix (fun i : Fin (n + 1) => i.succ.succ)
        (fun j : Fin (n + 1) => j.castSucc.castSucc)).det :=
    D.exterior_tied_second_derivative hgap
  rw [hc]
  apply mul_ne_zero (by norm_num)
  apply betaBoard_det_ne_zero
  · exact D.row_strictAnti.comp_strictMono (Fin.strictMono_succ.comp Fin.strictMono_succ)
  · exact D.col_strictAnti.comp_strictMono (Fin.strictMono_castSucc.comp Fin.strictMono_castSucc)
  · intro i
    exact hN i.succ.succ i.castSucc.castSucc

set_option backward.isDefEq.respectTransparency false in
/-- Rotation identifies the literal bottom extension with the top extension of the rotated core. -/
theorem rotate_corner_extension_schur (D : BetaDiagram (n + 3))
    (hN : D.Nonnegative) (d : ℤ) (hd : 0 < d) :
    ((D.rotate.cornerDiagram
      (D.rotate.positiveCorner_of_nonnegative (D.rotate_nonnegative hN))).extendTop d hd).schur =
    ((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendBottom d hd).schur := by
  let R := (D.rotate.cornerDiagram
    (D.rotate.positiveCorner_of_nonnegative (D.rotate_nonnegative hN))).extendTop d hd
  let T := (D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendBottom d hd
  have hm : R.rotate.matrix = T.matrix := by
    apply Matrix.ext
    intro i j
    have hj : j.rev = 0 ↔ j = Fin.last (n + 1) := by
      rw [Fin.rev_eq_iff, Fin.rev_zero]
    simp only [R, T, matrix, Matrix.of_apply, rotate, extendTop, extendBottom,
      cornerDiagram, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev]
    by_cases hz : j = Fin.last (n + 1)
    · have hrev := hj.mpr hz
      rw [ite_eq_left hrev, ite_eq_left hz]
      congr 1
      ring
    · have hrev := hj.not.mpr hz
      rw [ite_eq_right hrev, ite_eq_right hz]
      congr 1
      ring
  change R.schur = T.schur
  rw [← R.rotate_schur]
  exact congrArg Matrix.det hm

set_option backward.isDefEq.respectTransparency false in
/-- The actual private bottom coefficient follows by rotating the full board,
not a mate assumption. -/
theorem exterior_bottom_coefficient (D : BetaDiagram (n + 3)) (hN : D.Nonnegative)
    (hgap : D.bottomMargin < D.topMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat,
      by have hp := D.rotate.exterior_top_label_pos
         rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
         omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendBottom
          D.bottomMargin D.bottomMargin_pos).schur := by
  have hr := D.rotate.exterior_top_coefficient (D.rotate_nonnegative hN)
    (by simpa only [D.rotate_topMargin, D.rotate_bottomMargin] using hgap)
  dsimp only at hr ⊢
  have hl := D.rotate_largestLabel
  have hm := D.rotate_topMargin
  simpa only [hl, hm, D.rotate_schur, D.rotate_corner_extension_schur hN] using hr

set_option backward.isDefEq.respectTransparency false in
/-- The second private bottom coefficient cannot disappear under erasure of the largest label. -/
theorem exterior_bottom_coefficient_ne_zero (D : BetaDiagram (n + 3))
    (hN : D.Nonnegative) (hgap : D.bottomMargin < D.topMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat,
      by have hp := D.rotate.exterior_top_label_pos
         rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
         omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0 := by
  have hp : 0 < D.largestLabel - D.bottomMargin := by
    have hp := D.rotate.exterior_top_label_pos
    rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
    exact hp
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat, by omega⟩
  change MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0
  have hc : MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendBottom
          D.bottomMargin D.bottomMargin_pos).schur := D.exterior_bottom_coefficient hN hgap
  rw [hc]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (((D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).extendBottom
      D.bottomMargin D.bottomMargin_pos).schur_ne_zero)

/-- Largest label remaining after the maximal corner variable is set to zero. -/
def secondLabel (D : BetaDiagram (n + 2)) : ℤ :=
  D.largestLabel - min D.topMargin D.bottomMargin

/-- The literal next-label expression is positive. -/
theorem secondLabel_pos (D : BetaDiagram (n + 2)) : 0 < D.secondLabel := by
  have ht := D.exterior_top_label_pos
  have hb := D.rotate.exterior_top_label_pos
  rw [D.rotate_largestLabel, D.rotate_topMargin] at hb
  unfold secondLabel
  rcases le_total D.topMargin D.bottomMargin with h | h
  · rw [min_eq_left h]
    exact ht
  · rw [min_eq_right h]
    exact hb

/-- Every noncorner entry is bounded by the larger of the two exterior labels. -/
theorem index_le_secondLabel (D : BetaDiagram (n + 2)) (i j : Fin (n + 2))
    (hcorner : i ≠ 0 ∨ j ≠ Fin.last (n + 1)) :
    D.row i - D.col j ≤ D.secondLabel := by
  have hminT := min_le_left D.topMargin D.bottomMargin
  have hminB := min_le_right D.topMargin D.bottomMargin
  by_cases hi : i = 0
  · subst i
    have hj : j ≠ Fin.last (n + 1) := by simpa using hcorner
    have hc := D.col_strictAnti.antitone
      (show j ≤ (Fin.last n).castSucc by
        have hvl : j.val < n + 1 := by
          simpa only [Fin.lt_def, Fin.val_last] using Fin.lt_last_iff_ne_last.mpr hj
        change j.val ≤ n
        omega)
    dsimp only [secondLabel, largestLabel, bottomMargin] at *
    omega
  · have hr := D.row_strictAnti.antitone
      (show (0 : Fin (n + 1)).succ ≤ i by
        have hp := Fin.pos_iff_ne_zero.mpr hi
        have hv : 0 < i.val := by simpa only [Fin.lt_def, Fin.val_zero] using hp
        change 1 ≤ i.val
        omega)
    have hc := D.col_strictAnti.antitone (Fin.le_last j)
    dsimp only [secondLabel, largestLabel, topMargin] at *
    simp only [Fin.succ_zero_eq_one] at *
    omega

set_option backward.isDefEq.respectTransparency false in
/-- The second label really occurs after erasing the largest generator, including tied margins. -/
theorem secondLabel_mem_vars (D : BetaDiagram (n + 3)) (hN : D.Nonnegative) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨D.secondLabel.toNat, by have := D.secondLabel_pos; omega⟩
    M ∈ (eraseGenerator N D.schur).vars := by
  classical
  dsimp only
  by_contra h
  have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars h
  rcases lt_trichotomy D.topMargin D.bottomMargin with ht | he | hb
  · have hn := D.exterior_top_coefficient_ne_zero hN ht
    dsimp only at hn
    simp only [secondLabel, min_eq_left ht.le] at hz
    exact hn hz
  · have hn := D.exterior_tied_second_derivative_ne_zero hN he
    dsimp only at hn
    simp only [secondLabel, min_eq_left (le_of_eq he)] at hz
    apply hn
    rw [hz]
    exact map_zero _
  · have hn := D.exterior_bottom_coefficient_ne_zero hN hb
    dsimp only at hn
    simp only [secondLabel, min_eq_right hb.le] at hz
    exact hn hz

set_option backward.isDefEq.respectTransparency false in
/-- Erasure cannot introduce a generator above the actual second label. -/
theorem vars_le_secondLabel (D : BetaDiagram (n + 2)) (v : ℕ+)
    (hv : v ∈ (eraseGenerator
      (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) D.schur).vars) :
    (v.val : ℤ) ≤ D.secondLabel := by
  classical
  by_contra h
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  have hNv : (N.val : ℤ) = D.largestLabel := by
    change (D.largestLabel.toNat : ℤ) = D.largestLabel
    have := D.largestLabel_pos
    omega
  change v ∈ (eraseGenerator N D.matrix.det).vars at hv
  rw [eraseGenerator_det] at hv
  apply (not_mem_vars_det _ v ?_) hv
  intro i j
  change v ∉ (eraseGenerator N (complete (D.row i - D.col j))).vars
  rw [eraseGenerator_complete]
  split_ifs with hk
  · simp
  · rw [mem_vars_complete_iff]
    have hc : i ≠ 0 ∨ j ≠ Fin.last (n + 1) := by
      by_contra hc
      push Not at hc
      obtain ⟨rfl, rfl⟩ := hc
      apply hk
      change D.largestLabel = (N.val : ℤ)
      exact hNv.symm
    have hb := D.index_le_secondLabel i j hc
    omega

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the full polynomials recovers the smaller exterior gap
once both boards are nonnegative. -/
theorem minMargin_eq_of_schur_eq (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hND : D.Nonnegative)
    (hNE : E.Nonnegative) (he : D.schur = E.schur) :
    min D.topMargin D.bottomMargin = min E.topMargin E.bottomMargin := by
  have hl := D.largestLabel_eq_of_schur_eq E hD hE he
  have hd := D.secondLabel_mem_vars hND
  have hf := E.secondLabel_mem_vars hNE
  dsimp only at hd hf
  have hv : (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) =
      ⟨E.largestLabel.toNat, by have := E.largestLabel_pos; omega⟩ := by
    apply Subtype.ext
    exact congrArg Int.toNat hl
  rw [he, hv] at hd
  rw [← he, ← hv] at hf
  have hb₁ := E.vars_le_secondLabel _ hd
  have hb₂ := D.vars_le_secondLabel _ hf
  have := D.secondLabel_pos
  have := E.secondLabel_pos
  dsimp [secondLabel] at *
  omega

end BetaDiagram
end SkewJacobiNegative
