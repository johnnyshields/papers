/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.IntegralCommonCore
import SkewCornerDescent.Matrix.OriginalProfileFrame

/-!
# Complete Jacobi--Trudi endpoint extensions

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
The complete row and column endpoint lists define every original entry. Strict
negative-index rectangles give zeros; boundary index zero retains its unit.
No selected-prime or equal-extension hypothesis is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

variable {α β γ : Type*}

/-- Complete row endpoints, including the unmatched upper row and all lower rows. -/
def endpointBorderRows (upper : α ⊕ Unit → ℤ) (core : Unit ⊕ β → ℤ)
    (lower : γ → ℤ) : ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) → ℤ :=
  Sum.elim upper (Sum.elim core lower)

/-- Complete column endpoints in the compatible square frame. -/
def endpointBorderCols (upper : α → ℤ) (core : Unit ⊕ β → ℤ)
    (lower : Unit ⊕ γ → ℤ) : ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) → ℤ :=
  (Sum.elim upper (Sum.elim core lower)) ∘ (commonCoreColumnEquiv α β γ).symm

/-- The complete original Jacobi--Trudi matrix of the six endpoint lists. -/
noncomputable def endpointCoreFrame (upperRows : α ⊕ Unit → ℤ)
    (coreRows : Unit ⊕ β → ℤ) (lowerRows : γ → ℤ)
    (upperCols : α → ℤ) (coreCols : Unit ⊕ β → ℤ)
    (lowerCols : Unit ⊕ γ → ℤ) :
    Matrix ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ))
      ((α ⊕ Unit) ⊕ ((Unit ⊕ β) ⊕ γ)) Lambda :=
  Matrix.of fun i j => hh (endpointBorderRows upperRows coreRows lowerRows i -
    endpointBorderCols upperCols coreCols lowerCols j)

/-- Matching complete original endpoint lists after one common content shift
identifies the entire matrix, not merely its determinant or central submatrix. -/
theorem endpointCoreFrame_eq_originalProfileFrame {a b c n : ℕ}
    (P : Profile n) (hsize : n + 1 = a + 1 + (b + 1 + c)) (shift : ℤ)
    (upperRows : Fin a ⊕ Unit → ℤ) (coreRows : Unit ⊕ Fin b → ℤ)
    (lowerRows : Fin c → ℤ) (upperCols : Fin a → ℤ)
    (coreCols : Unit ⊕ Fin b → ℤ) (lowerCols : Unit ⊕ Fin c → ℤ)
    (hrows : ∀ i, P.xi (((commonCoreFiniteRows a b c).trans
      (finCongr hsize.symm)) i) + shift = endpointBorderRows upperRows coreRows lowerRows i)
    (hcols : ∀ j, P.zeta (((commonCoreFiniteCols a b c).trans
      (finCongr hsize.symm)) j) + shift = endpointBorderCols upperCols coreCols lowerCols j) :
    endpointCoreFrame upperRows coreRows lowerRows upperCols coreCols lowerCols =
      originalProfileFrame P a b c hsize := by
  apply Matrix.ext
  intro i j
  change hh (endpointBorderRows upperRows coreRows lowerRows i -
      endpointBorderCols upperCols coreCols lowerCols j) =
    hh (P.xi (((commonCoreFiniteRows a b c).trans (finCongr hsize.symm)) i) -
      P.zeta (((commonCoreFiniteCols a b c).trans (finCongr hsize.symm)) j))
  rw [← hrows, ← hcols]
  exact congrArg hh (by omega)

/-- The three strictly negative rectangles identify the literal full matrix
with compatible borders. No zero-index boundary entry is discarded. -/
theorem endpointCoreFrame_eq_bordered
    (upperRows : α ⊕ Unit → ℤ) (coreRows : Unit ⊕ β → ℤ) (lowerRows : γ → ℤ)
    (upperCols : α → ℤ) (coreCols : Unit ⊕ β → ℤ) (lowerCols : Unit ⊕ γ → ℤ)
    (hCL : ∀ i j, coreRows i < upperCols j)
    (hBL : ∀ i j, lowerRows i < upperCols j)
    (hBC : ∀ i j, lowerRows i < coreCols j) :
    endpointCoreFrame upperRows coreRows lowerRows upperCols coreCols lowerCols =
      borderedCoreMatrix (Matrix.of fun i j => hh (upperRows i - upperCols j))
        (Matrix.of fun i j => hh (upperRows i - coreCols j))
        (Matrix.of fun i j => hh (upperRows i - lowerCols j))
        (Matrix.of fun i j => hh (coreRows i - coreCols j))
        (Matrix.of fun i j => hh (coreRows i - lowerCols j))
        (Matrix.of fun i j => hh (lowerRows i - lowerCols j)) := by
  apply Matrix.ext
  intro i j
  obtain ⟨j, rfl⟩ := (commonCoreColumnEquiv α β γ).surjective j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [endpointCoreFrame, endpointBorderRows, endpointBorderCols,
      Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, borderedCoreMatrix]
  · exact hh_of_neg (sub_neg.mpr (hCL i j))
  · exact hh_of_neg (sub_neg.mpr (hBL i j))
  · exact hh_of_neg (sub_neg.mpr (hBC i j))

variable [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Arbitrary opposite endpoint extensions of the complete original lists have
a cross difference divisible by their whole unchanged corner core. Upper and
lower extensions need not be equal or translated copies. -/
theorem endpointCore_cross_difference_dvd
    (upperRows : α ⊕ Unit → ℤ) (coreRows : Unit ⊕ β → ℤ) (lowerRows : γ → ℤ)
    (upperCols : α → ℤ) (coreCols : Unit ⊕ β → ℤ) (lowerCols : Unit ⊕ γ → ℤ)
    (x y : ℤ) (hCL : ∀ i j, coreRows i < upperCols j)
    (hBL : ∀ i j, lowerRows i < upperCols j)
    (hBC : ∀ i j, lowerRows i < coreCols j) :
    (Matrix.of fun i j => hh (coreRows i - coreCols j)).det ∣
      (endpointCoreFrame upperRows coreRows lowerRows upperCols coreCols lowerCols).det *
        (endpointCoreFrame (fun (_ : Fin 0 ⊕ Unit) => x) coreRows
          (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
          coreCols (fun (_ : Unit ⊕ Fin 0) => y)).det -
      (endpointCoreFrame upperRows coreRows (fun i : Fin 0 => i.elim0)
          upperCols coreCols (fun (_ : Unit ⊕ Fin 0) => y)).det *
        (endpointCoreFrame (fun (_ : Fin 0 ⊕ Unit) => x) coreRows lowerRows
          (fun i : Fin 0 => i.elim0) coreCols lowerCols).det := by
  rw [endpointCoreFrame_eq_bordered upperRows coreRows lowerRows upperCols coreCols lowerCols
      hCL hBL hBC,
    endpointCoreFrame_eq_bordered (fun (_ : Fin 0 ⊕ Unit) => x) coreRows
      (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) coreCols
      (fun (_ : Unit ⊕ Fin 0) => y) (fun _ j => j.elim0)
      (fun i _ => i.elim0) (fun i _ => i.elim0),
    endpointCoreFrame_eq_bordered upperRows coreRows (fun i : Fin 0 => i.elim0)
      upperCols coreCols (fun (_ : Unit ⊕ Fin 0) => y)
      hCL (fun i _ => i.elim0) (fun i _ => i.elim0),
    endpointCoreFrame_eq_bordered (fun (_ : Fin 0 ⊕ Unit) => x) coreRows lowerRows
      (fun i : Fin 0 => i.elim0) coreCols lowerCols
      (fun _ j => j.elim0) (fun _ j => j.elim0) hBC]
  have hA0 : (Matrix.of fun (_ : Fin 0 ⊕ Unit) (j : Fin 0) => hh (x - j.elim0)) = 0 := by
    apply Matrix.ext
    intro _ j
    exact j.elim0
  have hB0 : (Matrix.of fun (i : Fin 0) (_ : Unit ⊕ Fin 0) => hh (i.elim0 - y)) = 0 := by
    apply Matrix.ext
    intro i _
    exact i.elim0
  rw [hA0, hB0]
  exact commonCoreDifference_dvd
    (Matrix.of fun i j => hh (upperRows i - upperCols j))
    (Matrix.of fun i j => hh (upperRows i - coreCols j))
    (Matrix.of fun i j => hh (upperRows i - lowerCols j))
    (Matrix.of fun i j => hh (coreRows i - coreCols j))
    (Matrix.of fun i j => hh (coreRows i - lowerCols j))
    (Matrix.of fun i j => hh (lowerRows i - lowerCols j))
    (fun j => hh (x - coreCols j)) (fun i => hh (coreRows i - y))
    (fun i => hh (upperRows i - y)) (fun j => hh (x - lowerCols j)) (hh (x - y))

end SkewCornerDescent.Matrix
