/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.LinearCombination

/-!
# Normalized endpoint vectors of a singular selected core

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). The complete adjugate identities identify every endpoint
profile coefficient with its original extreme cofactor, normalized by the corner
cofactor. Only the actual proper deleted minor is inverted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Each complete adjugate row determines the normalized incoming coefficients
of a singular selected core with invertible actual proper minor. -/
theorem selected_core_incoming_adjugate {n : ℕ} {F : Type*} [CommRing F]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    [Invertible (A.submatrix Fin.succ Fin.castSucc)] (hdet : A.det = 0)
    (k : Fin (n + 1)) (i : Fin n) :
    A.adjugate k i.succ =
      -A.adjugate k 0 *
        ((Matrix.of fun _ : Unit => fun j : Fin n => A 0 j.castSucc) *
          ⅟(A.submatrix Fin.succ Fin.castSucc)) () i := by
  let M := A.submatrix Fin.succ Fin.castSucc
  let row : Matrix Unit (Fin n) F := Matrix.of fun _ j => A 0 j.castSucc
  let q : Matrix Unit (Fin n) F := Matrix.of fun _ j => A.adjugate k j.succ
  let a := A.adjugate k 0
  have hrow : a • row + q * M = 0 := by
    ext u j
    cases u
    have h := congrArg (fun B => B k j.castSucc) (Matrix.adjugate_mul A)
    rw [hdet, zero_smul] at h
    simp only [Matrix.mul_apply, Matrix.zero_apply] at h
    rw [Fin.sum_univ_succ] at h
    change a * row () j + ∑ k, q () k * M k j = 0
    exact h
  have hmul := congrArg (fun B => B * ⅟M) hrow
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, mul_invOf_self,
    Matrix.mul_one, Matrix.zero_mul] at hmul
  have hscalar := congrArg (fun B => B () i) hmul
  change a * (row * ⅟M) () i + A.adjugate k i.succ = 0 at hscalar
  change A.adjugate k i.succ = -a * (row * ⅟M) () i
  linear_combination hscalar

/-- The complete adjugate column similarly determines every outgoing profile
coefficient, without assuming the selected core itself is invertible. -/
theorem selected_core_outgoing_adjugate {n : ℕ} {F : Type*} [CommRing F]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    [Invertible (A.submatrix Fin.succ Fin.castSucc)] (hdet : A.det = 0) (i : Fin n) :
    A.adjugate i.castSucc 0 =
      -A.adjugate (Fin.last n) 0 *
        (⅟(A.submatrix Fin.succ Fin.castSucc) *
          (Matrix.of fun j : Fin n => fun _ : Unit => A j.succ (Fin.last n))) i () := by
  let M := A.submatrix Fin.succ Fin.castSucc
  let col : Matrix (Fin n) Unit F := Matrix.of fun j _ => A j.succ (Fin.last n)
  let q : Matrix (Fin n) Unit F := Matrix.of fun j _ => A.adjugate j.castSucc 0
  let a := A.adjugate (Fin.last n) 0
  have hcol : M * q + a • col = 0 := by
    ext j u
    cases u
    have h := congrArg (fun B => B j.succ 0) (Matrix.mul_adjugate A)
    rw [hdet, zero_smul] at h
    simp only [Matrix.mul_apply, Matrix.zero_apply] at h
    rw [Fin.sum_univ_castSucc] at h
    change (∑ k, M j k * q k ()) + a * col j () = 0
    simpa only [M, q, a, col, Matrix.submatrix_apply, Matrix.of_apply, mul_comm] using h
  have hmul := congrArg (fun B => ⅟M * B) hcol
  simp only [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, invOf_mul_self,
    Matrix.one_mul, Matrix.mul_zero] at hmul
  have hscalar := congrArg (fun B => B i ()) hmul
  change A.adjugate i.castSucc 0 + a * (⅟M * col) i () = 0 at hscalar
  change A.adjugate i.castSucc 0 = -a * (⅟M * col) i ()
  linear_combination hscalar

/-- Every mixed selected-core cofactor factors into the two complete normalized
endpoint coefficients and the actual corner cofactor. No diagonal-only inverse
or independent endpoint coefficients are substituted. -/
theorem selected_core_mixed_adjugate {n : ℕ} {F : Type*} [CommRing F]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    [Invertible (A.submatrix Fin.succ Fin.castSucc)] (hdet : A.det = 0) (i j : Fin n) :
    A.adjugate j.castSucc i.succ = A.adjugate (Fin.last n) 0 *
      (((Matrix.of fun _ : Unit => fun k : Fin n => A 0 k.castSucc) *
        ⅟(A.submatrix Fin.succ Fin.castSucc)) () i *
      (⅟(A.submatrix Fin.succ Fin.castSucc) *
        (Matrix.of fun k : Fin n => fun _ : Unit => A k.succ (Fin.last n))) j ()) := by
  rw [selected_core_incoming_adjugate A hdet j.castSucc i,
    selected_core_outgoing_adjugate A hdet j]
  ring

end SkewCornerDescent.Matrix
