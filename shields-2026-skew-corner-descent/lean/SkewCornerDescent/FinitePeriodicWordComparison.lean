/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FinitePeriodicWords
import Mathlib.Data.Nat.Periodic

/-!
# Full finite words from their actual periodic prefixes

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Agreement on one complete overlap period extends to every original position
without conflating the whole normal word with its residue phase. Sorry-free.
-/

namespace SkewCornerDescent

/-- Agreement of the actual first period extends across the full overlap
word against any independently periodic comparison function. -/
theorem finite_periodic_word_eq_of_prefix {α : Type*} {L T : ℕ} [NeZero T]
    (word : Fin L → α) (hT : T ≤ L)
    (hp : ∀ i j : Fin L, j.val = i.val + T → word i = word j)
    (g : ℕ → α) (hg : Function.Periodic g T)
    (hfirst : ∀ i : Fin T, word ⟨i.val, i.isLt.trans_le hT⟩ = g i.val)
    (i : Fin L) : word i = g i.val := by
  have he := finiteWordCycle_eq word hT hp i
  have hi : i.val % T < T := Nat.mod_lt _ (NeZero.pos T)
  have heq : word i = word ⟨i.val % T, hi.trans_le hT⟩ := by
    simpa only [finiteWordCycle, ZMod.val_natCast] using he
  exact heq.trans ((hfirst ⟨i.val % T, hi⟩).trans (hg.map_mod_nat i.val))

end SkewCornerDescent
