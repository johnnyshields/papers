/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/BetaDiagrams.lean

import SkewJacobiNegative.CompleteAlgebra

/-!
# Strict beta lists and their actual determinants

Formalizes «Beta lists and polynomial readings» (`sec:boundary`, `eq:profile`)
of `shields-2026-skew-cofactor-independence.tex`.  Rows and columns retain the
same decreasing order as in the manuscript.  Every cofactor is an actual
signed complementary determinant.  Sorry-free.
-/

namespace SkewJacobiNegative

/-- Strict full beta lists with nonempty diagonal rows. -/
structure BetaDiagram (n : ℕ) where
  /-- Row beta entries, in decreasing order. -/
  row : Fin n → ℤ
  /-- Column beta entries, in decreasing order. -/
  col : Fin n → ℤ
  row_strictAnti : StrictAnti row
  col_strictAnti : StrictAnti col
  row_nonempty : ∀ i, col i < row i

namespace BetaDiagram

variable {n : ℕ}

/-- The actual Jacobi--Trudi matrix, including the genuine units at index zero. -/
noncomputable def matrix (D : BetaDiagram n) : Matrix (Fin n) (Fin n) CompleteRing :=
  Matrix.of fun i j => complete (D.row i - D.col j)

/-- The skew Schur polynomial read from the full beta lists. -/
noncomputable def schur (D : BetaDiagram n) : CompleteRing := D.matrix.det

/-- Adjacent rows overlap, in addition to the diagram being nonempty. -/
def Connected (D : BetaDiagram n) : Prop :=
  0 < n ∧ ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    D.col i ≤ D.row ⟨i.val + 1, hi⟩

/-- Every matrix index is strictly positive. -/
def Dense (D : BetaDiagram n) : Prop := ∀ i j, D.col j < D.row i

/-- Every matrix index is nonnegative. -/
def Nonnegative (D : BetaDiagram n) : Prop := ∀ i j, D.col j ≤ D.row i

/-- The common translation is fixed by setting the last column beta to zero. -/
def Normalized (D : BetaDiagram n) : Prop :=
  ∀ hn : 0 < n, D.col ⟨n - 1, by omega⟩ = 0

/-- Ordered row lengths, rather than a sorted multiset. -/
def rowLength (D : BetaDiagram n) (i : Fin n) : ℤ := D.row i - D.col i

/-- Adjacent overlap minus one, with signed subtraction. -/
def overlap (D : BetaDiagram n) (i : Fin n) (hi : i.val + 1 < n) : ℤ :=
  D.row ⟨i.val + 1, hi⟩ - D.col i

/-- The square complementary determinant at the specified matrix site. -/
noncomputable def cofactor (D : BetaDiagram (n + 1)) (i j : Fin (n + 1)) : CompleteRing :=
  (-1) ^ (i.val + j.val) * (D.matrix.submatrix i.succAbove j.succAbove).det

/-- Equality of the actual beta lists up to one common translation. -/
def TranslationEquivalent (D E : BetaDiagram n) : Prop :=
  ∃ c : ℤ, (∀ i, D.row i = E.row i + c) ∧ (∀ i, D.col i = E.col i + c)

/-- Reflection of both beta lists reverses their roles and their index orders. -/
def RotationEquivalent (D E : BetaDiagram n) : Prop :=
  ∃ c : ℤ, (∀ i, D.row i = c - E.col i.rev) ∧ (∀ i, D.col i = c - E.row i.rev)

/-- Rotation fixes the translation class of the diagram. -/
def Symmetric (D : BetaDiagram n) : Prop := D.RotationEquivalent D

/-- Strictly positive entries imply the nonnegative-index condition. -/
theorem Dense.nonnegative {D : BetaDiagram n} (h : D.Dense) : D.Nonnegative :=
  fun i j => (h i j).le

/-- Dense nonempty diagrams are connected. -/
theorem Dense.connected {D : BetaDiagram n} (h : D.Dense) (hn : 0 < n) :
    D.Connected := ⟨hn, fun i hi => (h ⟨i.val + 1, hi⟩ i).le⟩

/-- The strict diagonal condition really supplies positive row lengths. -/
theorem rowLength_pos (D : BetaDiagram n) (i : Fin n) : 0 < D.rowLength i :=
  sub_pos.mpr (D.row_nonempty i)

/-- A common translation leaves every matrix entry unchanged. -/
theorem TranslationEquivalent.matrix_eq {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : D.matrix = E.matrix := by
  obtain ⟨c, hr, hc⟩ := h
  ext i j
  simp only [matrix, Matrix.of_apply, hr i, hc j]
  congr 1
  ring_nf

/-- Translation preserves the actual determinant. -/
theorem TranslationEquivalent.schur_eq {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : D.schur = E.schur :=
  congrArg Matrix.det h.matrix_eq

end BetaDiagram
end SkewJacobiNegative
