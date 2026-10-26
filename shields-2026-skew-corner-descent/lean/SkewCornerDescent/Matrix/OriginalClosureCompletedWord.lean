/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureGaps

/-!
# The complete actual gap word of the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The canonical selected
order gives two complete copies of the original completed gap word, including the central
splice and the closing cap position. Repeated gap values retain their separate positions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every position in the first complete copy has the original actual completed gap. -/
theorem originalHorizontalClosure_completed_gap_upper {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (k : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalCompletedGap Q
      ⟨k.val, by rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩ =
      c.originalCompletedGap P k := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hB : 0 < originalSelectedCount (hD := hD) P := by have hk := k.isLt; omega
  have hn : ¬ k.val + 1 = originalSelectedCount (hD := hD) Q := by omega
  rw [originalCompletedGap, ite_eq_right hn]
  by_cases hk : k.val + 1 = originalSelectedCount (hD := hD) P
  · have he := c.originalHorizontalClosure_central_distance P Q v hQ hB
    have hs : (⟨k.val, by omega⟩ : Fin (originalSelectedCount (hD := hD) Q)).succ =
        ⟨originalSelectedCount (hD := hD) P, by omega⟩ := Fin.ext hk
    rw [hs]
    have hl : k = ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩ := by
      apply Fin.ext
      change k.val = originalSelectedCount (hD := hD) P - 1
      omega
    have hg := congrArg (c.originalCompletedGap P) hl
    dsimp only at he
    omega
  · have hb : k.val + 1 < originalSelectedCount (hD := hD) P := by omega
    have he := originalHorizontalClosure_internal_distance P Q v hQ k
      ⟨k.val + 1, hb⟩ rfl true
    dsimp only at he
    simp only [ite_true, zero_add] at he
    rw [he, originalCompletedGap, ite_eq_right hk]

/-- Every position in the second complete copy has the original actual completed gap,
including the literal closure's final exterior cap splice. -/
theorem originalHorizontalClosure_completed_gap_lower {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (k : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalCompletedGap Q
      ⟨originalSelectedCount (hD := hD) P + k.val, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩ =
      c.originalCompletedGap P k := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hB : 0 < originalSelectedCount (hD := hD) P := by have hk := k.isLt; omega
  by_cases hk : k.val + 1 = originalSelectedCount (hD := hD) P
  · have hq : originalSelectedCount (hD := hD) P + k.val + 1 =
        originalSelectedCount (hD := hD) Q := by omega
    rw [originalCompletedGap, ite_eq_left hq, originalCompletedGap, ite_eq_left hk,
      originalHorizontalClosure_first_cap P Q v hQ hB,
      originalHorizontalClosure_last_cap P Q v hQ hB]
  · have hq : ¬ originalSelectedCount (hD := hD) P + k.val + 1 =
        originalSelectedCount (hD := hD) Q := by omega
    have hb : k.val + 1 < originalSelectedCount (hD := hD) P := by omega
    have he := originalHorizontalClosure_internal_distance P Q v hQ k
      ⟨k.val + 1, hb⟩ rfl false
    dsimp only at he
    simp only [Bool.false_eq_true, ite_false] at he
    rw [originalCompletedGap, ite_eq_right hq, he, originalCompletedGap, ite_eq_right hk]

/-- The entire actual completed closure word is the positional repetition of the source word. -/
theorem originalHorizontalClosure_completed_gap_mod {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (k : Fin (originalSelectedCount (hD := hD) Q)) :
    c.originalCompletedGap Q k = c.originalCompletedGap P
      ⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ := by
  let B := originalSelectedCount (hD := hD) P
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  by_cases hk : k.val < B
  · let i : Fin B := ⟨k.val, hk⟩
    have he := c.originalHorizontalClosure_completed_gap_upper P Q v hQ i
    have hi : k.val % B = k.val := Nat.mod_eq_of_lt hk
    dsimp only [i, B] at he hi
    exact he.trans (congrArg (c.originalCompletedGap P) (Fin.ext hi.symm))
  · have hi : k.val - B < B := by have hlt := k.isLt; dsimp [B] at *; omega
    let i : Fin B := ⟨k.val - B, hi⟩
    have he := c.originalHorizontalClosure_completed_gap_lower P Q v hQ i
    have hki : B + i.val = k.val := by dsimp [i]; omega
    have hm : k.val % B = i.val := by
      rw [← hki]
      simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt i.isLt]
    have heq : (⟨B + i.val, by dsimp [B] at *; omega⟩ :
        Fin (originalSelectedCount (hD := hD) Q)) = k := Fin.ext hki
    dsimp only [B] at heq hm
    rw [heq] at he
    exact he.trans (congrArg (c.originalCompletedGap P) (Fin.ext hm.symm))

end SkewCornerDescent.Matrix.SelectedCoordinate
