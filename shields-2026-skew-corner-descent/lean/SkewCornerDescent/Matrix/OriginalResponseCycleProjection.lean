/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassWords
import SkewCornerDescent.FiniteClosureWindows

/-!
# Literal original closure cycles from the actual finite period word

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`). Complete
literal windows supply the entire source period projection. Appending one closure
response then gives exactly the cyclic truncation used by the inventory identities,
with every repeated original position retained. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- Completing an actual projected finite word is its literal periodic truncation
with one final closure position. This statement needs no response unit convention. -/
theorem completeResponseCycle_eq_closureWord {n B : ℕ} [NeZero n] [NeZero B]
    {F : Type*} (l : Fin (B - 1) → F) (f : ZMod n → F) (S : F)
    (hproj : ∀ i, l i = f (i.val : ZMod n)) :
    completeResponseCycle l S = closureWord f S B := by
  funext z
  have hz := ZMod.val_lt z
  unfold completeResponseCycle closureWord
  by_cases hlast : z.val = B - 1
  · rw [ite_eq_left hlast, dite_eq_right (by omega)]
  · have hprefix : z.val < B - 1 := by omega
    rw [ite_eq_right hlast, dite_eq_left hprefix]
    exact hproj ⟨z.val, hprefix⟩

end SkewCornerDescent.CyclicWindows

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual complete source cycle equals its full period truncation with the
same arbitrary closure response. The source projection is produced from literal
windows, not supplied as an abstract finite-word premise. -/
theorem originalWindow_complete_cycle_projection {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) [NeZero j]
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W) :
    ∃ hperiod : j ≤ originalSelectedCount (hD := hD) P - 1,
      ∀ S : OtherField c.top, completeResponseCycle (c.originalInternalResidue P) S =
        closureWord (finiteWordCycle (n := j) (c.originalInternalResidue P) hperiod)
          S (originalSelectedCount (hD := hD) P) := by
  obtain ⟨hperiod, hP, _⟩ := c.originalWindow_responseClass_projection P W q u v hv hW
    hwindow hcutq hcutLq hC j hjlen
  refine ⟨hperiod, fun S => completeResponseCycle_eq_closureWord _ _ S ?_⟩
  intro i
  have hc := congrFun (c.originalResponseClassWord_val P j hperiod) (i.val : ZMod j)
  exact (hP i).trans hc

end SkewCornerDescent.Matrix.SelectedCoordinate
