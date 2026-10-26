/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.FieldCommonCore
import SkewCornerDescent.Matrix.OriginalMultiplicity

/-!
# Selected-prime divisibility for arbitrary compatible borders

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`lem:original-transfer`). The actual residue kernel transfers the complete singular
common-core identity back to divisibility by the selected connected function.
This criterion does not claim integral divisibility by every power in the whole core.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)
  {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

include c

/-- A selected prime dividing the complete common core divides the full border cross
difference. No rank, kernel vector or proper-minor unit is an additional premise. -/
theorem selected_commonCore_cross_difference_dvd
    (A : Matrix (α ⊕ Unit) α Lambda) (R : Matrix (α ⊕ Unit) (Unit ⊕ β) Lambda)
    (T : Matrix (α ⊕ Unit) (Unit ⊕ γ) Lambda)
    (C : Matrix (Unit ⊕ β) (Unit ⊕ β) Lambda)
    (S : Matrix (Unit ⊕ β) (Unit ⊕ γ) Lambda) (B : Matrix γ (Unit ⊕ γ) Lambda)
    (r s : (Unit ⊕ β) → Lambda) (t : (α ⊕ Unit) → Lambda)
    (q : (Unit ⊕ γ) → Lambda) (z : Lambda) (hC : cellSchur D hD.1 ∣ C.det) :
    let M00 := borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) Lambda)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j)
      (Matrix.of fun _ (_ : Unit ⊕ Fin 0) => z) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) Lambda)
    let M10 := borderedCoreMatrix A R (Matrix.of fun i (_ : Unit ⊕ Fin 0) => t i) C
      (Matrix.of fun i (_ : Unit ⊕ Fin 0) => s i) (0 : Matrix (Fin 0) (Unit ⊕ Fin 0) Lambda)
    let M01 := borderedCoreMatrix (0 : Matrix (Fin 0 ⊕ Unit) (Fin 0) Lambda)
      (Matrix.of fun (_ : Fin 0 ⊕ Unit) j => r j) (Matrix.of fun _ j => q j) C S B
    let M11 := borderedCoreMatrix A R T C S B
    cellSchur D hD.1 ∣ M11.det * M00.det - M10.det * M01.det := by
  classical
  have hC0 : (C.map c.residueMap).det = 0 := by
    have hz := (c.residueMap_eq_zero_iff _).mpr hC
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using hz
  have hz := commonCore_cross_difference_of_singular (A.map c.residueMap)
    (R.map c.residueMap) (T.map c.residueMap) (C.map c.residueMap)
    (S.map c.residueMap) (B.map c.residueMap)
    (fun i => c.residueMap (r i)) (fun i => c.residueMap (s i))
    (fun i => c.residueMap (t i)) (fun i => c.residueMap (q i)) (c.residueMap z) hC0
  dsimp only at hz ⊢
  apply (c.residueMap_eq_zero_iff _).mp
  simp only [map_sub, map_mul, RingHom.map_det, RingHom.mapMatrix_apply,
    borderedCoreMatrix_map c.residueMap (map_zero c.residueMap),
    Matrix.map_zero c.residueMap (map_zero c.residueMap)]
  simpa only [Matrix.map, Matrix.of_apply] using hz

end SkewCornerDescent.Matrix.SelectedCoordinate
