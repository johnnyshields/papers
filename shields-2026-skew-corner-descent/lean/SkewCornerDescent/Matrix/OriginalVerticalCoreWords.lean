/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCoreWords
import SkewCornerDescent.Matrix.OriginalVerticalClosureEnumeration

/-!
# Complete proper-core words in the two literal vertical closure copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Whole selected-component translations identify both complete proper-core
polynomials at every canonical selected occurrence of the actual closure.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both complete proper-core entries of each literal closure copy are its
source entries, not merely equal functions of the selected prime. -/
theorem originalVerticalClosure_core_words_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalSelectedCoreLeft Q (originalVerticalClosureSelectedIndex P Q v hQ upper i) =
      c.originalSelectedCoreLeft P i ∧
    c.originalSelectedCoreRight Q (originalVerticalClosureSelectedIndex P Q v hQ upper i) =
      c.originalSelectedCoreRight P i := by
  let b := originalSelectedEnumeration (hD := hD) P i
  let d := originalVerticalClosureSelectedCopy P Q v hQ upper b
  let z := if upper then vH P.cells - eCell else 0
  have he := originalVerticalClosureSelectedCopy_cells P Q v hQ upper b
  have hcells : translate (v - z) (interiorBlockCells Q d.val.val) =
      interiorBlockCells P b.val.val := by
    apply translate_injective z
    rw [translate_translate, show z + (v - z) = v by abel, he]
    cases upper <;> simp only [z, Bool.false_eq_true, ite_false, ite_true, translate_zero]
  have h := c.original_selected_core_polynomials_of_translate Q P d b (v - z) hcells
  have henum : originalSelectedEnumeration Q
      (originalVerticalClosureSelectedIndex P Q v hQ upper i) = d :=
    originalVerticalClosure_enumeration_copy P Q v hQ upper i
  let LQ := fun e : OriginalSelectedBlocks (hD := hD) Q =>
    c.selectedCoreLeftPolynomial
      (interiorBlockProfile Q e.val.val (originalBlockSelected_nonempty Q e.val e.property))
      (originalSelectedProfile_schur Q e).symm
  let RQ := fun e : OriginalSelectedBlocks (hD := hD) Q =>
    c.selectedCoreRightPolynomial
      (interiorBlockProfile Q e.val.val (originalBlockSelected_nonempty Q e.val e.property))
      (originalSelectedProfile_schur Q e).symm
  have hL : c.originalSelectedCoreLeft Q (originalVerticalClosureSelectedIndex P Q v hQ upper i) =
      LQ d := congrArg LQ henum
  have hR : c.originalSelectedCoreRight Q (originalVerticalClosureSelectedIndex P Q v hQ upper i) =
      RQ d := congrArg RQ henum
  exact ⟨hL.trans h.1, hR.trans h.2⟩

/-- The complete actual closure proper-core words are the exact positional
repetition of the complete source words, including both end occurrences. -/
theorem originalVerticalClosure_core_words_mod {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (k : Fin (originalSelectedCount (hD := hD) Q)) :
    c.originalSelectedCoreLeft Q k = c.originalSelectedCoreLeft P
      ⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ ∧
    c.originalSelectedCoreRight Q k = c.originalSelectedCoreRight P
      ⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ := by
  let B := originalSelectedCount (hD := hD) P
  have hc := originalVerticalClosure_profile_selected_count (hD := hD) P Q v hQ
  by_cases hk : k.val < B
  · let i : Fin B := ⟨k.val, hk⟩
    have h := c.originalVerticalClosure_core_words_copy P Q v hQ true i
    have he : originalVerticalClosureSelectedIndex P Q v hQ true i = k := by
      apply Fin.ext
      simp only [originalVerticalClosureSelectedIndex, i, ite_true, zero_add]
    have hm : k.val % originalSelectedCount (hD := hD) P = i.val :=
      Nat.mod_eq_of_lt hk
    have hi : (⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ :
        Fin (originalSelectedCount (hD := hD) P)) = i := Fin.ext hm
    rw [hi]
    simpa only [he] using h
  · have hsmall : k.val - B < B := by have := k.isLt; dsimp only [B] at *; omega
    let i : Fin B := ⟨k.val - B, hsmall⟩
    have h := c.originalVerticalClosure_core_words_copy P Q v hQ false i
    have he : originalVerticalClosureSelectedIndex P Q v hQ false i = k := by
      apply Fin.ext
      change B + (k.val - B) = k.val
      omega
    have hki : B + i.val = k.val := by dsimp only [i]; omega
    have hm : k.val % B = i.val := by
      rw [← hki]
      simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt i.isLt]
    have hi : (⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ :
        Fin (originalSelectedCount (hD := hD) P)) = i := Fin.ext hm
    rw [hi]
    simpa only [he] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
