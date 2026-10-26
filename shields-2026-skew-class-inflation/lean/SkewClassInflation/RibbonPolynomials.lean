/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.CompleteAlgebra
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Ribbon polynomials in independent complete generators

The canonical ribbon recurrence and class `R(alpha)` used in
`eq:ribbon-coarsening`, `eq:thin-substitution`, and
`eq:saturation-substitution` of
`shields-2026-skew-class-inflation.tex`.  The actual determinant bridge
is proved in `RibbonDeterminants`.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The ribbon polynomial with first part `a`, defined by cutting or merging the next boundary. -/
noncomputable def ribbonTail (a : ℕ) : List ℕ → CompleteRing
  | [] => complete a
  | b :: l => complete a * ribbonTail b l - ribbonTail (a + b) l

/-- The ribbon polynomial of an ordered composition, including the empty-word unit. -/
noncomputable def ribbonWord : List ℕ → CompleteRing
  | [] => 1
  | a :: l => ribbonTail a l

/-- Ribbon equivalence at a fixed total size in the independent complete generators. -/
noncomputable def ribbonClass {M : ℕ} (α : Composition M) : Set (Composition M) :=
  {β | ribbonWord β.blocks = ribbonWord α.blocks}

end SkewClassInflation
