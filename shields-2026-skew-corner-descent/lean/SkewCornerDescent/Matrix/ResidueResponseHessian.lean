/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueEndpointGradient
import SkewCornerDescent.Matrix.SchurResponseHessian

/-!
# Full surviving-generator Hessian of an actual residue interval

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual mapped entries supply affine higher-generator jets. Both orders of the
full removed inverse's internal derivatives remain in the eight-path identity.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

private noncomputable def integerEntryDerivation {F : Type*} [Field F]
    (f : F →+ F) (hone : f 1 = 0)
    (hmul : ∀ a b, f (a * b) = a * f b + b * f a) : Derivation ℤ F F where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zsmul f
  map_one_eq_zero' := hone
  leibniz' := by intro a b; exact hmul a b

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Higher surviving generators give zero mixed second jets on every actual
mapped entry, including literal `h₀` and coincident generators. -/
theorem residue_hh_higher_second (p q : ℕ+) (hp : c.top < p) (hq : c.top < q) (i : ℤ) :
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩ (c.residueMap (hh i))) = 0 := by
  rw [c.residue_hh_higher_derivative q hq]
  split_ifs <;> simp

/-- The complete eight-path mixed higher-generator contraction for a residue
interval. The full removed inverse is retained in every ordered path. -/
noncomputable def residueIntervalHessian {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ) (p q : ℕ+)
    [Invertible (vertexBetaMatrix c.residueMap row col)] : OtherField c.top :=
  let B := vertexOutgoing c.residueMap col x
  let C := vertexIncoming c.residueMap row y
  let P := vertexBetaMatrix c.residueMap row col
  let DB : Matrix Unit ν (OtherField c.top) := fun _ j => if x - col j = (p : ℤ) then 1 else 0
  let EB : Matrix Unit ν (OtherField c.top) := fun _ j => if x - col j = (q : ℤ) then 1 else 0
  let DC : Matrix ν Unit (OtherField c.top) := fun i _ => if row i - y = (p : ℤ) then 1 else 0
  let EC : Matrix ν Unit (OtherField c.top) := fun i _ => if row i - y = (q : ℤ) then 1 else 0
  let DP : Matrix ν ν (OtherField c.top) := fun i j => if row i - col j = (p : ℤ) then 1 else 0
  let EP : Matrix ν ν (OtherField c.top) := fun i j => if row i - col j = (q : ℤ) then 1 else 0
  (-(EB * ⅟P * DC) - DB * ⅟P * EC + EB * ⅟P * DP * ⅟P * C +
    DB * ⅟P * EP * ⅟P * C + B * ⅟P * DP * ⅟P * EC +
    B * ⅟P * EP * ⅟P * DC - B * ⅟P * DP * ⅟P * EP * ⅟P * C -
    B * ⅟P * EP * ⅟P * DP * ⅟P * C) () ()

set_option backward.isDefEq.respectTransparency false in
/-- The exact mixed higher-generator response derivative retains the complete
removed inverse and all eight ordered paths. All derivative matrices are the
actual index selectors of the original beta entries. -/
theorem residue_interval_response_hessian {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ) (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.residueMap (hh (x - y)) -
          (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col) *
            vertexIncoming c.residueMap row y) () ())) =
      c.residueIntervalHessian row col x y p q := by
  classical
  let dp := residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
  let dq := residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
  let fp : OtherField c.top →+ OtherField c.top := dp.toLinearMap.toAddMonoidHom
  let fq : OtherField c.top →+ OtherField c.top := dq.toLinearMap.toAddMonoidHom
  have hpone : fp 1 = 0 := dp.map_one_eq_zero
  have hqone : fq 1 = 0 := dq.map_one_eq_zero
  have hpmul (a b) : fp (a * b) = a * fp b + b * fp a := by
    change dp (a * b) = a * dp b + b * dp a
    simpa only [smul_eq_mul] using dp.leibniz a b
  have hqmul (a b) : fq (a * b) = a * fq b + b * fq a := by
    change dq (a * b) = a * dq b + b * dq a
    simpa only [smul_eq_mul] using dq.leibniz a b
  let : Algebra ℤ (OtherField c.top) := Ring.toIntAlgebra (OtherField c.top)
  let : Module ℤ (OtherField c.top) :=
    (Ring.toIntAlgebra (OtherField c.top)).toModule
  let δp := integerEntryDerivation fp hpone hpmul
  let δq := integerEntryDerivation fq hqone hqmul
  have hdp (a) : δp a = dp a := rfl
  have hdq (a) : δq a = dq a := rfl
  have h := entryDeriv_retainedResponse_hessian δp δq
    (fun _ _ : Unit => c.residueMap (hh (x - y)))
    (vertexOutgoing c.residueMap col x) (vertexIncoming c.residueMap row y)
    (vertexBetaMatrix c.residueMap row col)
    (by ext i j; exact c.residue_hh_higher_second p q hp hq (x - y))
    (by ext i j; exact c.residue_hh_higher_second p q hp hq (x - col j))
    (by ext i j; exact c.residue_hh_higher_second p q hp hq (row i - y))
    (by ext i j; exact c.residue_hh_higher_second p q hp hq (row i - col j))
  have hDB : entryDeriv δp (vertexOutgoing c.residueMap col x) =
      (fun (_ : Unit) (j : ν) => if x - col j = (p : ℤ) then 1 else 0) := by
    ext i j
    exact c.residue_hh_higher_derivative p hp (x - col j)
  have hEB : entryDeriv δq (vertexOutgoing c.residueMap col x) =
      (fun (_ : Unit) (j : ν) => if x - col j = (q : ℤ) then 1 else 0) := by
    ext i j
    exact c.residue_hh_higher_derivative q hq (x - col j)
  have hDC : entryDeriv δp (vertexIncoming c.residueMap row y) =
      (fun (i : ν) (_ : Unit) => if row i - y = (p : ℤ) then 1 else 0) := by
    ext i j
    exact c.residue_hh_higher_derivative p hp (row i - y)
  have hEC : entryDeriv δq (vertexIncoming c.residueMap row y) =
      (fun (i : ν) (_ : Unit) => if row i - y = (q : ℤ) then 1 else 0) := by
    ext i j
    exact c.residue_hh_higher_derivative q hq (row i - y)
  have hDP : entryDeriv δp (vertexBetaMatrix c.residueMap row col) =
      (fun (i j : ν) => if row i - col j = (p : ℤ) then 1 else 0) := by
    ext i j
    exact c.residue_hh_higher_derivative p hp (row i - col j)
  have hEP : entryDeriv δq (vertexBetaMatrix c.residueMap row col) =
      (fun (i j : ν) => if row i - col j = (q : ℤ) then 1 else 0) := by
    ext i j
    exact c.residue_hh_higher_derivative q hq (row i - col j)
  rw [hDB, hEB, hDC, hEC, hDP, hEP] at h
  have he := congrFun (congrFun h ()) ()
  simpa only [entryDeriv, retainedResponse, Matrix.sub_apply, hdp, hdq,
    dp, dq, residueIntervalHessian] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
