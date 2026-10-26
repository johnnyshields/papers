/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowEndLogLocality
import SkewCornerDescent.Matrix.OriginalClosureEndLogLocality
import SkewCornerDescent.Matrix.OriginalAmalgamationSpan

/-!
# Complete actual overlap-union endpoint logarithmic jets

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both actual whole end windows preserve complete cap neighborhoods. The original
corner product supplies the union's maximal-component bound. Every original
normal inverse jet remains in the transported cap logarithms. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every full left-cap logarithmic jet of the actual overlap union is its original source
jet below the source selected count. No union units, cap matching or inverse jets are assumed. -/
theorem originalAmalgamation_left_log_coeff {n m w : ℕ}
    (P : Profile n) (W : Profile w) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P) :
    PowerSeries.coeff k (leftCap (c.originalNormalExtension A)
      (originalSelectedCount (hD := hD) A)) =
    PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
      (originalSelectedCount (hD := hD) P)) := by
  have hmaxA := originalAmalgamation_component_span P W A q v u z hv hwindow hW hA _ hmax
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  obtain ⟨_, hright⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  have hupper : P.cells = translate (u - v)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate]
    have he : v + (u - v) = u := by abel
    rw [he]
    exact hright.symm
  exact (c.originalWindow_left_log_coeff A P q (u - v) hupper
    (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2)
    hmaxA hmax k hk).symm

/-- The actual union's entire right-cap logarithmic jet is also its original source jet.
The actual lower end window supplies its suffix offset and every complete inverse match. -/
theorem originalAmalgamation_right_log_coeff {n m w : ℕ}
    (P : Profile n) (W : Profile w) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P) :
    PowerSeries.coeff k (rightCap (c.originalNormalExtension A) 0
      (originalSelectedCount (hD := hD) A)) =
    PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
      (originalSelectedCount (hD := hD) P)) := by
  have hmaxA := originalAmalgamation_component_span P W A q v u z hv hwindow hW hA _ hmax
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  obtain ⟨hleft, _⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  exact (c.originalWindow_right_log_coeff A P q u hleft.symm
    (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1)
    hmaxA hmax k hk).symm

/-- Complete left and right cap logarithms cancel with the actual three-word weights
on the horizontal-closure branch. Literal geometry supplies all four jet matches;
the outer-count balance is the only scalar assumption. -/
theorem originalHorizontalComparison_end_log_balance {n m w h : ℕ}
    (P : Profile n) (W : Profile w) (A : Profile m) (H : Profile h)
    (q : ℤ) (shift u z l : ℤ × ℤ) (hq : 0 ≤ q) (hv : content shift = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate shift (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate shift P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate l H.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (b a d : ℕ) (hd : d + a = b) (k : ℕ)
    (hk : k < originalSelectedCount (hD := hD) P) :
    let left := fun {s : ℕ} (X : Profile s) =>
      PowerSeries.coeff k (leftCap (c.originalNormalExtension X)
        (originalSelectedCount (hD := hD) X))
    let right := fun {s : ℕ} (X : Profile s) =>
      PowerSeries.coeff k (rightCap (c.originalNormalExtension X) 0
        (originalSelectedCount (hD := hD) X))
    (b : OtherField c.top) * left A - (a : OtherField c.top) * left P -
        (d : OtherField c.top) * left H = 0 ∧
      (b : OtherField c.top) * right A - (a : OtherField c.top) * right P -
        (d : OtherField c.top) * right H = 0 := by
  dsimp only
  rw [c.originalAmalgamation_left_log_coeff P W A q shift u z hq hv
      hwindow hW hA hcutq hcutLq hmax k hk,
    c.originalHorizontalClosure_left_log_coeff P H l hH hmax k hk,
    c.originalAmalgamation_right_log_coeff P W A q shift u z hq hv
      hwindow hW hA hcutq hcutLq hmax k hk,
    c.originalHorizontalClosure_right_log_coeff P H l hH hmax k hk]
  have hc : (d : OtherField c.top) + (a : OtherField c.top) = (b : OtherField c.top) := by
    exact_mod_cast hd
  constructor
  · linear_combination
      -(PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
        (originalSelectedCount (hD := hD) P))) * hc
  · linear_combination
      -(PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
        (originalSelectedCount (hD := hD) P))) * hc

end SkewCornerDescent.Matrix.SelectedCoordinate
