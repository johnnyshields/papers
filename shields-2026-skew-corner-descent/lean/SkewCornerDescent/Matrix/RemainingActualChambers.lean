/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualSimultaneousChambers

/-!
# Restriction of actual simultaneous chambers

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
Removing classes restricts the original simultaneous chamber at the same top generator.
Its root assignments and all lower-generator dependencies remain unchanged. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

open Classical in
/-- Every remaining-family chamber condition is inherited from the original chamber at
the same top generator. This supplies the chamber at each finite peeling step. -/
theorem simultaneousActualChamber_restrict {α : Type*}
    (S : Finset α) (N K : ℕ+) (top : α → ℕ+) (p q : α → OtherPolynomial N)
    (positive : Bool) (x : ℕ → ℝ)
    (hx : x ∈ simultaneousActualChamber N K top p q positive) :
    x ∈ simultaneousActualChamber N K (fun a : {a : α // a ∉ S} => top a.val)
      (fun a => p a.val) (fun a => q a.val) positive := by
  refine ⟨fun a => hx.1 ⟨a.val.val, a.property⟩, ?_, ?_⟩
  · intro a b hab
    apply hx.2.1 ⟨a.val.val, a.property⟩ ⟨b.val.val, b.property⟩
    intro he
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {i : α // top i = K} => z.val) he
  · intro a i
    exact hx.2.2 ⟨a.val.val, a.property⟩ ⟨i.val.val, i.property⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
