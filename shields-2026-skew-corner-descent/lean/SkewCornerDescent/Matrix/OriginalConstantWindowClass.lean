/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassDefects
import SkewCornerDescent.Matrix.OriginalInternalCyclicProfiles

/-!
# Complete original class inventory for a constant internal word

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Complete literal windows transfer the actual constant response to every
internal window position. The full source/window counts then produce
exactly one active class of exponent equal to their outer-count difference.
True cap classes are retained and have zero exponent when distinct.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A constant actual internal word supplies its complete one-active class
inventory, including the window and both true cap classes. -/
theorem originalWindow_constant_internal_class {n m : ℕ} (P : Profile n) (W : Profile m)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcountP : originalSelectedCount (hD := hD) P = b)
    (hcountW : originalSelectedCount (hD := hD) W = a)
    (i₀ : Fin (originalSelectedCount (hD := hD) P - 1))
    (hconstant : ∀ i, c.originalInternalResidue P i = c.originalInternalResidue P i₀) :
    let active := c.originalResponseClassOf P (originalInternalStateIndex P i₀)
    (∀ i, c.originalInternalResidue W i = active.val) ∧
      c.originalResponseClassExponent P W a b active = (b-a : ℕ) ∧
      ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0 := by
  classical
  let active := c.originalResponseClassOf P (originalInternalStateIndex P i₀)
  have hactive : active.val = c.originalInternalResidue P i₀ := rfl
  let d := b-a
  let : NeZero d := ⟨by dsimp only [d]; omega⟩
  have hC : 0 < originalSelectedCount (hD := hD) W := by rw [hcountW]; exact ha
  obtain ⟨hperiod, _, hwordW⟩ := c.originalWindow_responseClass_projection P W q u v hv hW
    hwindow hcutq hcutLq hC d (by rw [hcountP, hcountW])
  have hP (i) : c.originalInternalResidue P i = active.val := (hconstant i).trans hactive.symm
  have hw (i : Fin (originalSelectedCount (hD := hD) W - 1)) :
      c.originalInternalResidue W i = active.val := by
    have he := congrFun (c.originalResponseClassWord_val P d hperiod) (i.val : ZMod d)
    exact (hwordW i).trans (he.trans (hP _))
  refine ⟨hw, ?_, ?_⟩
  · change (a : ℤ)*(Finset.univ.filter fun i => c.originalInternalResidue P i = active.val).card -
      (b : ℤ)*(Finset.univ.filter fun i => c.originalInternalResidue W i = active.val).card = _
    simp only [hP, hw, Finset.filter_true, Finset.card_univ, Fintype.card_fin, hcountP, hcountW]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub hab.le]
    ring
  · intro X hX
    have hx : active.val ≠ X.val := fun he => hX (Subtype.ext he.symm)
    change (a : ℤ)*(Finset.univ.filter fun i => c.originalInternalResidue P i = X.val).card -
      (b : ℤ)*(Finset.univ.filter fun i => c.originalInternalResidue W i = X.val).card = 0
    simp only [hP, hw, hx, Finset.filter_false, Finset.card_empty, Nat.cast_zero,
      mul_zero, sub_self]

end SkewCornerDescent.Matrix.SelectedCoordinate
