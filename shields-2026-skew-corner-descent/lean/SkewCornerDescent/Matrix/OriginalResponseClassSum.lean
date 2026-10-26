/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassDefects
import SkewCornerDescent.Matrix.OriginalPrimitiveClasses

/-!
# Complete actual response exponent sum

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`).
Literal window counts include every actual class and the omitted position, and
produce a nonzero exponent sum before any active class is chosen. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete literal matching supplies the exact actual class-exponent sum. -/
theorem originalWindow_responseClassExponent_sum {n m : ℕ}
    (P : Profile n) (W : Profile m) (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (r b a : ℕ) (hr : 0 < r) (ha : 0 < a) (hab : a < b)
    (hcountP : originalSelectedCount (hD := hD) P = r * b)
    (hcountW : originalSelectedCount (hD := hD) W = r * a) :
    (∑ X : c.OriginalResponseClass P, c.originalResponseClassExponent P W a b X) =
      ((b - a : ℕ) : ℤ) := by
  classical
  let d := b - a
  have hd : 0 < d := by dsimp [d]; omega
  let : NeZero (r * d) := ⟨Nat.ne_of_gt (Nat.mul_pos hr hd)⟩
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hr ha
  obtain ⟨k, s, hk, hs, _, hb, _⟩ :=
    positive_remainder_exists hd (show d < b by dsimp [d]; omega)
  obtain ⟨capacity, hcounts, hsum⟩ := c.originalWindow_responseClass_defects P W q u v hv
    hW hwindow hcutq hcutLq hC r d s k b a hr hs hk hb
    (by dsimp [d]; omega) hcountP hcountW
  have heq : c.originalResponseClassExponent P W a b =
      classDefect (c.originalResponseClassWord P (r * d) capacity) 1 d s (r * s - 1) 0 := by
    funext X
    exact hcounts X
  rw [heq]
  exact hsum

end SkewCornerDescent.Matrix.SelectedCoordinate
