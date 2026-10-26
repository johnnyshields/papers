/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/BetaBridge.lean;
-- adapted to the copied skew-boundary-reconstruction boundary-inverse namespace.

import SkewJacobiNegative.BetaDiagrams
import SkewSchurReconstruction.BoundaryReconstruction
import Mathlib.Order.Fin.Basic

/-!
# Faithful passage to the proved boundary inverse

Formalizes the representation seam for `eq:boundary-reconstruction-input`
in `shields-2026-skew-class-inflation.tex`.  Arbitrary full beta lists
are realized by genuine partition boundaries after a common translation.
The actual rational and integral Schur observations are related by an
injective coefficient extension.  Sorry-free.
-/

namespace SkewJacobiNegative

/-- Strict integral decrease compensates for adding the finite row index. -/
theorem strictAnti_add_index_antitone {n : ℕ} {a : Fin n → ℤ}
    (ha : StrictAnti a) : Antitone (fun i => a i + (i.val : ℤ)) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have h := ha i.castSucc_lt_succ
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    omega

namespace BetaDiagram

variable {n : ℕ}

/-- The strict beta lists associated with the copied partition-boundary diagram. -/
def ofDiagram (X : SkewSchurReconstruction.Diagram n) : BetaDiagram n where
  row i := (X.outer i : ℤ) - i.val
  col i := (X.inner i : ℤ) - i.val
  row_strictAnti := by
    intro i j hij
    have h := X.outer_antitone hij.le
    have hi : i.val < j.val := hij
    dsimp
    omega
  col_strictAnti := by
    intro i j hij
    have h := X.inner_antitone hij.le
    have hi : i.val < j.val := hij
    dsimp
    omega
  row_nonempty := by
    intro i
    have h := X.row_nonempty i
    omega

/-- The least column beta, used solely to make the partition boundaries nonnegative. -/
def bottomCol (D : BetaDiagram n) (hn : 0 < n) : ℤ := D.col ⟨n - 1, by omega⟩

/-- Every column lies above the last column in the strict beta order. -/
theorem bottomCol_le (D : BetaDiagram n) (hn : 0 < n) (i : Fin n) :
    D.bottomCol hn ≤ D.col i := by
  apply D.col_strictAnti.antitone
  change i.val ≤ n - 1
  omega

/-- The common beta translation makes every inner boundary nonnegative. -/
theorem translated_col_nonneg (D : BetaDiagram n) (hn : 0 < n) (i : Fin n) :
    0 ≤ D.col i - D.bottomCol hn + i.val := by
  have h := D.bottomCol_le hn i
  omega

/-- Every valid nonempty beta diagram has a partition-boundary realization. -/
def toDiagram (D : BetaDiagram n) (hn : 0 < n) : SkewSchurReconstruction.Diagram n where
  outer i := (D.row i - D.bottomCol hn + i.val).toNat
  inner i := (D.col i - D.bottomCol hn + i.val).toNat
  outer_antitone := by
    intro i j hij
    have h := strictAnti_add_index_antitone D.row_strictAnti hij
    dsimp only at h ⊢
    omega
  inner_antitone := by
    intro i j hij
    have h := strictAnti_add_index_antitone D.col_strictAnti hij
    dsimp only at h ⊢
    omega
  row_nonempty := by
    intro i
    have h := D.row_nonempty i
    have hc := D.translated_col_nonneg hn i
    omega

/-- Recovering beta lists from their realization changes only one common translation. -/
theorem ofDiagram_toDiagram_translation (D : BetaDiagram n) (hn : 0 < n) :
    (ofDiagram (D.toDiagram hn)).TranslationEquivalent D := by
  refine ⟨-D.bottomCol hn, ?_, ?_⟩
  · intro i
    have h := D.row_nonempty i
    have hc := D.translated_col_nonneg hn i
    change ((D.row i - D.bottomCol hn + i.val).toNat : ℤ) - i.val =
      D.row i + -D.bottomCol hn
    omega
  · intro i
    have hc := D.translated_col_nonneg hn i
    change ((D.col i - D.bottomCol hn + i.val).toNat : ℤ) - i.val =
      D.col i + -D.bottomCol hn
    omega

/-- Connectedness agrees across the two representations, including the nonempty condition. -/
theorem ofDiagram_connected_iff (X : SkewSchurReconstruction.Diagram n) :
    (ofDiagram X).Connected ↔ X.Connected := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro i hi
    have hc := h i hi
    change (X.inner i : ℤ) - i.val ≤
      (X.outer ⟨i.val + 1, hi⟩ : ℤ) - (i.val + 1 : ℕ) at hc
    omega
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro i hi
    have hc := h i hi
    change (X.inner i : ℤ) - i.val ≤
      (X.outer ⟨i.val + 1, hi⟩ : ℤ) - (i.val + 1 : ℕ)
    omega

/-- The beta matrix is the rational image of the copied Jacobi--Trudi matrix. -/
theorem ofDiagram_matrix (X : SkewSchurReconstruction.Diagram n) :
    (ofDiagram X).matrix = X.jacobiTrudiMatrix.map integerLift := by
  apply Matrix.ext
  intro i j
  change complete (((X.outer i : ℤ) - i.val) - ((X.inner j : ℤ) - j.val)) =
    integerLift (SkewSchurReconstruction.complete ((X.outer i : ℤ) - X.inner j - i.val + j.val))
  unfold complete
  congr 2
  ring

/-- The copied integral Schur polynomial and the rational beta determinant are the same object. -/
theorem ofDiagram_schur (X : SkewSchurReconstruction.Diagram n) :
    (ofDiagram X).schur = integerLift X.schurFunction := by
  rw [schur, ofDiagram_matrix, ← integerLift_det,
    ← SkewSchurReconstruction.Diagram.schurFunction_eq_jacobiTrudiDet]

/-- Every nonempty beta determinant is the rational image of its actual Young diagram. -/
theorem toDiagram_schur (D : BetaDiagram n) (hn : 0 < n) :
    integerLift (D.toDiagram hn).schurFunction = D.schur := by
  rw [← ofDiagram_schur]
  exact (D.ofDiagram_toDiagram_translation hn).schur_eq

end BetaDiagram
end SkewJacobiNegative
