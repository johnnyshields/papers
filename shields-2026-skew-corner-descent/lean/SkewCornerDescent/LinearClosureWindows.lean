/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.LinearCyclicWindows
import SkewCornerDescent.CyclicClosureWindows

/-!
# Linear inventories of the doubled closure word

Formalizes the word-count step of `shields-2026-skew-corner-descent.tex`
(`lem:original-transfer`). The internal word `l S l` is the truncation of two
cycles of `l S` at its final closure position. All linear and cyclic starts,
including repeated response values, are retained. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- Removing the one closure position leaves exactly the literal original prefix. -/
theorem closureWord_linear_prefix {n B : ℕ} [NeZero B] {F : Type*}
    (f : ZMod n → F) (S : F) :
    (fun i : Fin (B - 1) => closureWord f S B (i.val : ZMod B)) =
      (fun i : Fin (B - 1) => f (i.val : ZMod n)) := by
  funext i
  unfold closureWord
  rw [ZMod.val_natCast_of_lt (by have := i.isLt; omega),
    ite_eq_right (by have := i.isLt; omega)]

/-- The doubled linear closure word contributes one original linear inventory and
one full closure-cycle inventory. This is valid up to the entire closure length. -/
theorem linearInverseWindowSum_closure_double {n B : ℕ} [NeZero B]
    {F : Type*} [Field F] (f : ZMod n → F) (S : F) (j : ℕ) (hj : j ≤ B) :
    linearInverseWindowSum
        (fun i : Fin (2 * B - 1) => closureWord f S B (i.val : ZMod B)) j =
      linearInverseWindowSum (fun i : Fin (B - 1) => f (i.val : ZMod n)) j +
        inverseWindowSum (closureWord f S B) j := by
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hlen : B - 1 + B = 2 * B - 1 := by omega
  have h := linearInverseWindowSum_add_period (L := B - 1)
    (closureWord f S B) j (by omega)
  rw [closureWord_linear_prefix] at h
  rw [← hlen]
  exact h

end SkewCornerDescent.CyclicWindows
