/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicPrivatePhase
import SkewCornerDescent.Matrix.OriginalResponseClassWords

/-!
# The actual private boundary represents the omitted active phase

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Whole windows produce the complete original finite response cycle. Periodicity
of the completed response word then identifies every proper period boundary
with its actual omitted class, not an independently assigned label. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every proper period boundary of the full actual source internal word is
its omitted class. The complete finite-word representation is supplied by
literal equal windows, rather than assumed at the chosen index. -/
theorem originalPrivate_boundary_active {n s : ℕ}
    (P : Profile n) (W : Profile s) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (r b a m : ℕ) (hr : 0 < r) (ha : 0 < a)
    (hm : 0 < m) (hmb : m < b)
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hcountW : originalSelectedCount (hD := hD) W = r * a)
    [NeZero (r * b)] [NeZero (r * (b - a))]
    (active : c.OriginalResponseClass P)
    (hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1)
    (hp : Function.Periodic
      (closureWord (finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod)
        active.val (r * b)) (r : ZMod (r * b))) :
    let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨r * m - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left hmb hr
      have hpos := Nat.mul_pos hr hm
      omega⟩
    c.originalInternalResidue P i = active.val := by
  intro i
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hr ha
  have hjlen : r * (b - a) = originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W := by
    rw [hcount, hcountW, Nat.mul_sub_left_distrib]
  obtain ⟨hperiod', hsource, _⟩ := c.originalWindow_responseClass_projection P W q u v hv
    hW hwindow hcutq hcutLq hC (r * (b - a)) hjlen
  have hcycle := congrFun (c.originalResponseClassWord_val P (r * (b - a)) hperiod')
    (i.val : ZMod (r * (b - a)))
  have hs : c.originalInternalResidue P i =
      finiteWordCycle (c.originalInternalResidue P) hperiod (i.val : ZMod (r * (b - a))) :=
    (hsource i).trans hcycle
  have hboundary := closureWord_private_boundary
    (finiteWordCycle (c.originalInternalResidue P) hperiod) active.val r b m hr hm hmb hp
  have hlt := Nat.mul_lt_mul_of_pos_left hmb hr
  have hpos := Nat.mul_pos hr hm
  simp only [closureWord, ZMod.val_natCast_of_lt (show r * m - 1 < r * b by omega),
    ite_eq_right (show r * m - 1 ≠ r * b - 1 by omega)] at hboundary
  exact hs.trans hboundary

end SkewCornerDescent.Matrix.SelectedCoordinate
