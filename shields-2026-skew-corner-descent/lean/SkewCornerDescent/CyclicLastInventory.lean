/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicDetectors

/-!
# The literal last-window detector

Formalizes `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`,
`eq:dual-last`). The complete prefix product is the product of the literal word
before its last closure position. The full-cycle identity keeps all starts.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- The paper's last-window expression, using the complete literal prefix product. -/
def lastWindowDefect {α F : Type*} [Fintype α] [Field F] {n : ℕ} [NeZero n]
    (f : ZMod n → F) (S : α → F) (e : α → ℤ) (b B : ℕ) : F :=
  (b : F) * inverseWindowSum f B -
    (B : F) * closureLabelSum e S / (∏ i ∈ Finset.range (B - 1), f (i : ZMod n))

/-- Every full closure-cycle window has the complete word product, with `B` starts. -/
theorem inverseWindowSum_closure_whole {F : Type*} [Field F] {n B : ℕ}
    [NeZero n] [NeZero B] (f : ZMod n → F) (S : F) :
    inverseWindowSum (closureWord f S B) B =
      (B : F) / ((∏ i ∈ Finset.range (B - 1), f (i : ZMod n)) * S) := by
  simp only [inverseWindowSum, zmod_windowProduct_cycle, closureWord_product,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, div_eq_mul_inv]

/-- The whole-word defect is exactly the last-window expression, without regularity
assumptions and without deduplicating equal starts or equal response values. -/
theorem windowDefect_eq_last {α F : Type*} [Fintype α] [Field F] {n B : ℕ}
    [NeZero n] [NeZero B] (f : ZMod n → F) (S : α → F) (e : α → ℤ) (b : ℕ) :
    windowDefect f S e b B B = lastWindowDefect f S e b B := by
  unfold windowDefect lastWindowDefect
  simp_rw [inverseWindowSum_closure_whole]
  congr 1
  rw [closureLabelSum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end SkewCornerDescent.CyclicWindows
