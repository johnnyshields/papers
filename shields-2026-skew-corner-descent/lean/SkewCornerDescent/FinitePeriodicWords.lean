/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.LinearCyclicWindows

/-!
# Completing an overlapping finite word to its actual cycle

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
Equality on overlapping positions identifies every indexed letter with its residue-class
position in the first complete period. Values are never deduplicated. Sorry-free.
-/

namespace SkewCornerDescent

/-- The first full period of a finite word, retaining its indexed positions. -/
def finiteWordCycle {α : Type*} {n L : ℕ} [NeZero n]
    (word : Fin L → α) (hlen : n ≤ L) (z : ZMod n) : α :=
  word ⟨z.val, (ZMod.val_lt z).trans_le hlen⟩

/-- A finite overlap period supplies the entire cyclic truncation, including repeated wraps. -/
theorem finiteWordCycle_eq {α : Type*} {n L : ℕ} [NeZero n]
    (word : Fin L → α) (hlen : n ≤ L)
    (hp : ∀ i j : Fin L, j.val = i.val + n → word i = word j) (i : Fin L) :
    word i = finiteWordCycle word hlen (i.val : ZMod n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmod (k : ℕ) : ∀ hk : k < L,
      word ⟨k, hk⟩ = word ⟨k % n, (Nat.mod_lt k hn).trans_le hlen⟩ := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hkn : k < n
      · congr 1
        apply Fin.ext
        exact (Nat.mod_eq_of_lt hkn).symm
      · have hnk : n ≤ k := by omega
        have hsub : k - n < k := Nat.sub_lt (by omega) hn
        have hsubL : k - n < L := hsub.trans hk
        have he := hp ⟨k - n, hsubL⟩ ⟨k, hk⟩ (by simp only; omega)
        calc
          _ = word ⟨k - n, hsubL⟩ := he.symm
          _ = word ⟨(k - n) % n, (Nat.mod_lt _ hn).trans_le hlen⟩ := ih _ hsub hsubL
          _ = _ := by
            congr 1
            apply Fin.ext
            exact (Nat.mod_eq_sub_mod hnk).symm
  simpa only [finiteWordCycle, ZMod.val_natCast] using hmod i.val i.isLt

end SkewCornerDescent
