/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.LinearClosureWindows

/-!
# Completing an actual finite internal response word

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The cycle appends one closure response to the complete original internal word.
Its doubled truncation is exactly the two original words with that closure
between them, even when response values coincide. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- One actual internal word and its one closure position, with no quotient by equal values. -/
def completeResponseCycle {B : ℕ} {F : Type*} (l : Fin (B - 1) → F)
    (S : F) (i : ZMod B) : F :=
  if hi : i.val < B - 1 then l ⟨i.val, hi⟩ else S

/-- Before the closure position the completed cycle is literally the original word. -/
theorem completeResponseCycle_prefix {B : ℕ} [NeZero B] {F : Type*}
    (l : Fin (B - 1) → F) (S : F) (i : Fin (B - 1)) :
    completeResponseCycle l S (i.val : ZMod B) = l i := by
  unfold completeResponseCycle
  rw [ZMod.val_natCast_of_lt (by have := i.isLt; omega), dite_eq_left i.isLt]

/-- The doubled truncation has the exact two-copy internal word and one central entry. -/
theorem completeResponseCycle_double {B : ℕ} [NeZero B] {F : Type*}
    (l : Fin (B - 1) → F) (S : F) (i : Fin (2 * B - 1)) :
    completeResponseCycle l S (i.val : ZMod B) =
      if hi : i.val < B - 1 then l ⟨i.val, hi⟩
      else if hm : i.val = B - 1 then S
      else l ⟨i.val - B, by
        have := i.isLt
        have := Nat.pos_of_ne_zero (NeZero.ne B)
        omega⟩ := by
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  by_cases hi : i.val < B - 1
  · rw [dite_eq_left hi]
    unfold completeResponseCycle
    rw [ZMod.val_natCast_of_lt (by omega), dite_eq_left hi]
  · rw [dite_eq_right hi]
    by_cases hm : i.val = B - 1
    · rw [dite_eq_left hm]
      unfold completeResponseCycle
      rw [hm, ZMod.val_natCast_of_lt (by omega), dite_eq_right (by omega)]
    · rw [dite_eq_right hm]
      unfold completeResponseCycle
      have hv : ((i.val : ℕ) : ZMod B).val = i.val - B := by
        have he : i.val = (i.val - B) + B := by omega
        calc
          _ = i.val % B := ZMod.val_natCast _ _
          _ = ((i.val - B) + B) % B := congrArg (· % B) he
          _ = i.val - B := by
            rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
              Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      rw [hv, dite_eq_left (by have := i.isLt; omega)]

/-- Every eligible length retains one full closure-cycle inventory, including all full starts. -/
theorem linearInverseWindowSum_complete_double {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S : F)
    (j : ℕ) (hj : j ≤ B) :
    linearInverseWindowSum
      (fun i : Fin (2 * B - 1) => completeResponseCycle l S (i.val : ZMod B)) j =
      linearInverseWindowSum l j + inverseWindowSum (completeResponseCycle l S) j := by
  have hc : closureWord (completeResponseCycle l S) S B = completeResponseCycle l S := by
    funext i
    unfold closureWord
    by_cases hlast : i.val = B - 1
    · rw [ite_eq_left hlast]
      unfold completeResponseCycle
      rw [hlast, dite_eq_right (by omega)]
    · rw [ite_eq_right hlast, ZMod.natCast_zmod_val]
  have he := linearInverseWindowSum_closure_double (completeResponseCycle l S) S j hj
  rw [hc] at he
  have hl : (fun i : Fin (B - 1) => completeResponseCycle l S (i.val : ZMod B)) = l := by
    funext i
    exact completeResponseCycle_prefix l S i
  rw [hl] at he
  exact he

/-- A bound equality reindexes a complete linear word, without deleting any occurrence. -/
theorem linearInverseWindowSum_fin_congr {L M : ℕ} {F : Type*} [Field F]
    (h : L = M) (l : Fin L → F) (q : Fin M → F)
    (hw : ∀ i, l i = q (finCongr h i)) (j : ℕ) :
    linearInverseWindowSum l j = linearInverseWindowSum q j := by
  subst M
  have he : l = q := funext hw
  rw [he]

end SkewCornerDescent.CyclicWindows
