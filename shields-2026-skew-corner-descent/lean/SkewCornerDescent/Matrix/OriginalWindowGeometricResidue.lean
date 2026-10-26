/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowSharedCoreAssembly

/-!
# Geometric residue matching from complete original windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`, `lem:original-transfer`). The actual selected occurrence
produces a nonempty window core; literal windows produce every frame size and
compatible block. No residue-matching or rank premise is added. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

include c

/-- The actual selected prime divides the cross difference of the complete
original source, common window, and literal amalgamation. Every finite frame and
its compatibility are constructed inside the proof. -/
theorem originalWindow_cross_difference_dvd {n k m : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hqtop : q < P.xi 0) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hB : 0 < originalSelectedCount (hD := hD) W) :
    cellSchur D hD.1 ∣ A.schur * W.schur - P.schur ^ 2 := by
  have hkpos := (c.originalSelectedCorner_residue_singular W hB).1
  cases k with
  | zero => omega
  | succ b =>
    obtain ⟨_, hk, hm, _, _⟩ := originalAmalgamation_row_alignment P W A q v u z
      hq hqtop hv hwindow hW hA
    exact (originalSelectedCorner_dvd_of_pos (hD := hD) W hB).trans
      (originalWindow_frame_cross_difference_dvd P (n - (b + 1)) b W A
        q v u z hq hqtop hv hwindow hW hA (by omega) (by omega))

/-- The complete literal cross-determinant assembly supplies the geometric
residue identity itself, with no additional residue equality assumed. -/
theorem originalWindow_residue_cross_identity {n k m : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hqtop : q < P.xi 0) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hB : 0 < originalSelectedCount (hD := hD) W) :
    c.residueMap A.schur * c.residueMap W.schur = c.residueMap P.schur ^ 2 := by
  have hz := (c.residueMap_eq_zero_iff _).mpr
    (c.originalWindow_cross_difference_dvd P W A q v u z hq hqtop hv hwindow hW hA hB)
  rw [map_sub, map_mul, map_pow] at hz
  exact sub_eq_zero.mp hz

end SkewCornerDescent.Matrix.SelectedCoordinate
