/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueResponseHessian
import SkewCornerDescent.Matrix.SchurResponseHessianFactor
import SkewCornerDescent.Matrix.DressedProfileProjection

/-!
# Full residue Hessian as two profile inverse projections

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
When the two surviving generator lengths sum to the actual interval span,
the full mixed Hessian is the negative sum of the two complete inverse
projections. Coincident generators retain both copies. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full eight-path Hessian has exactly the two projected positions.
The full endpoint profiles and all inverse entries remain in both projections. -/
theorem residue_hessian_profile_projection {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ) (p q : ℕ+)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsum : (p : ℤ) + (q : ℤ) = x - y) :
    c.residueIntervalHessian row col x y p q =
      let I := ⅟(vertexBetaMatrix c.residueMap row col)
      let B := vertexOutgoing c.residueMap col x
      let C := vertexIncoming c.residueMap row y
      let A := endpointProfile (fun i => x - row i) (fun i => (B * I) () i)
      let T := endpointProfile (fun i => col i - y) (fun i => (I * C) i ())
      (-profileInverseProjection row col I A T (x - (q : ℤ)) -
        profileInverseProjection row col I A T (x - (p : ℤ))) := by
  let I := ⅟(vertexBetaMatrix c.residueMap row col)
  let B := vertexOutgoing c.residueMap col x
  let C := vertexIncoming c.residueMap row y
  let DB : Matrix Unit ν (OtherField c.top) := fun _ j => if x - col j = (p : ℤ) then 1 else 0
  let EB : Matrix Unit ν (OtherField c.top) := fun _ j => if x - col j = (q : ℤ) then 1 else 0
  let DC : Matrix ν Unit (OtherField c.top) := fun i _ => if row i - y = (p : ℤ) then 1 else 0
  let EC : Matrix ν Unit (OtherField c.top) := fun i _ => if row i - y = (q : ℤ) then 1 else 0
  let DP : Matrix ν ν (OtherField c.top) := fun i j => if row i - col j = (p : ℤ) then 1 else 0
  let EP : Matrix ν ν (OtherField c.top) := fun i j => if row i - col j = (q : ℤ) then 1 else 0
  have hf := schur_hessian_dressed_paths B DB EB C DC EC I DP EP
  have hs : c.residueIntervalHessian row col x y p q =
      -((EB - B * I * EP) * I * (DC - DP * I * C)) () () -
        ((DB - B * I * DP) * I * (EC - EP * I * C)) () () := by
    simpa only [residueIntervalHessian, B, C, I, DB, EB, DC, EC, DP, EP,
      Matrix.neg_mul, Matrix.sub_apply, Matrix.neg_apply] using
      congrFun (congrFun hf ()) ()
  have hfirst := dressed_profile_inverse_projection row col x y (p : ℤ) (q : ℤ) hsum B C I
  have hsecond := dressed_profile_inverse_projection row col x y (q : ℤ) (p : ℤ)
    (by omega) B C I
  exact hs.trans (congrArg₂ (fun a b : OtherField c.top => -a - b) hfirst hsecond)

end SkewCornerDescent.Matrix.SelectedCoordinate
