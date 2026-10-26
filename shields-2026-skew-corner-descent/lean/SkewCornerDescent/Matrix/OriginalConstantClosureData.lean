/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureProfileCycle
import SkewCornerDescent.Matrix.OriginalClosureCoreWords
import SkewCornerDescent.Matrix.OriginalVerticalCoreWords
import SkewCornerDescent.Matrix.OriginalOrdinaryClosureScalars

/-!
# Full constant source data in either actual ordinary closure

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The actual pinned center and both literal source copies give every real
closure residue and height. Full proper-core transport covers both copies
and both selected endpoints of the splice. No cyclic wrapped inverse or
separately supplied closure core equality is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual ordinary center and whole source suppliers produce all
constant data on the entire doubled internal word. -/
theorem originalClosure_constant_internal_data {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (S : OtherField c.top) (K : ℤ)
    (hS : ∀ i, c.originalInternalResidue P i = S)
    (hgap : ∀ i, c.originalCompletedGap P i = K - (c.top : ℤ))
    (hcore : ∀ i : Fin (originalSelectedCount (hD := hD) P),
      c.originalSelectedCoreLeft P i = c.originalSelectedCoreLeft P 0 ∧
        c.originalSelectedCoreRight P i = c.originalSelectedCoreRight P 0)
    (hcenter : c.originalInternalResidue Q
      ⟨originalSelectedCount (hD := hD) P - 1, by
        rw [originalOrdinaryClosure_selected_count P Q z hQ]
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = S) :
    (∀ i : Fin (originalSelectedCount (hD := hD) Q - 1),
      c.originalInternalResidue Q i = S ∧
        originalHessenbergDistance (hD := hD) Q
          (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) = K) ∧
      ∀ i : Fin (originalSelectedCount (hD := hD) Q),
        c.originalSelectedCoreLeft Q i = c.originalSelectedCoreLeft P 0 ∧
          c.originalSelectedCoreRight Q i = c.originalSelectedCoreRight P 0 := by
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  obtain ⟨_, hdata⟩ := c.originalClosure_profile_height_residue_cycle P Q z hQ S
  have hword (x : ZMod (originalSelectedCount (hD := hD) P)) :
      completeResponseCycle (c.originalInternalResidue P) S x = S := by
    unfold completeResponseCycle
    split_ifs
    · exact hS _
    · rfl
  constructor
  · intro i
    have hd := hdata hcenter i
    refine ⟨hd.2.2.trans (hword _), ?_⟩
    rw [hd.2.1, hgap]
    ring
  · intro i
    have hc : c.originalSelectedCoreLeft Q i = c.originalSelectedCoreLeft P
        ⟨i.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ ∧
        c.originalSelectedCoreRight Q i = c.originalSelectedCoreRight P
        ⟨i.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ := by
      rcases hQ with hH | hV
      · exact c.originalHorizontalClosure_core_words_mod P Q z hH hB i
      · exact c.originalVerticalClosure_core_words_mod P Q z hV hB i
    exact ⟨hc.1.trans (hcore _).1, hc.2.trans (hcore _).2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
