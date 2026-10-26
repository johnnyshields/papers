/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalRemovedCancellation
import SkewCornerDescent.Matrix.OriginalClosureInventory

/-!
# Complete removed-factor cancellation in the original defect

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). The multiplicative law for the complete original
corner inventories transfers to the complete removed determinants before normal substitution.
The literal window construction must supply the amalgamation and closure inventories. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A multiplicative corner-inventory law cancels complete removed factors at every normal order.
All selected occurrence counts are derived from the actual complementary determinants. -/
theorem originalRemovedMatrix_multiplicative_cancel {n m k : ℕ}
    (P : Profile n) (Q : Profile m) (R : Profile k) (a b d : ℕ)
    (hcorner : (jtMatrix (fun j : Fin n => P.xi j.succ)
          (fun j => P.zeta j.castSucc)).det ^ a =
      (jtMatrix (fun j : Fin m => Q.xi j.succ)
          (fun j => Q.zeta j.castSucc)).det ^ b *
        (jtMatrix (fun j : Fin k => R.xi j.succ)
          (fun j => R.zeta j.castSucc)).det ^ d) :
    (originalRemovedMatrix (hD := hD) P).det ^ a =
      (originalRemovedMatrix (hD := hD) Q).det ^ b *
        (originalRemovedMatrix (hD := hD) R).det ^ d := by
  let ψ := cellSchur D hD.1
  let u := cellSchur (diagramInterior D) hD.1.interior
  let B := originalSelectedCount (hD := hD) P
  let C := originalSelectedCount (hD := hD) Q
  let E := originalSelectedCount (hD := hD) R
  have hp : Prime ψ := (irreducible_cellSchur hD).prime
  have hQ0 : (jtMatrix (fun j : Fin m => Q.xi j.succ)
      (fun j => Q.zeta j.castSucc)).det ≠ 0 := by
    simpa only [betaDet, jtMatrix] using Q.minor_ne_zero
  have hR0 : (jtMatrix (fun j : Fin k => R.xi j.succ)
      (fun j => R.zeta j.castSucc)).det ≠ 0 := by
    simpa only [betaDet, jtMatrix] using R.minor_ne_zero
  have ht := congrArg (primeOrder ψ) hcorner
  rw [primeOrder_pow hp, primeOrder_mul hp (pow_ne_zero b hQ0) (pow_ne_zero d hR0),
    primeOrder_pow hp, primeOrder_pow hp,
    ← originalSelectedCount_eq_primeOrder (hD := hD) P,
    ← originalSelectedCount_eq_primeOrder (hD := hD) Q,
    ← originalSelectedCount_eq_primeOrder (hD := hD) R] at ht
  have hcount : B * a = C * b + E * d := by
    simpa only [B, C, E, mul_comm] using ht
  have hP := congrArg (fun z : Lambda => z ^ a)
    (originalRemovedMatrix_cross_cofactor (hD := hD) P)
  have hQ := congrArg (fun z : Lambda => z ^ b)
    (originalRemovedMatrix_cross_cofactor (hD := hD) Q)
  have hR := congrArg (fun z : Lambda => z ^ d)
    (originalRemovedMatrix_cross_cofactor (hD := hD) R)
  simp only [mul_pow, ← pow_mul] at hP hQ hR
  change ψ ^ (B * a) * _ = u ^ (B * a) * _ at hP
  change ψ ^ (C * b) * _ = u ^ (C * b) * _ at hQ
  change ψ ^ (E * d) * _ = u ^ (E * d) * _ at hR
  apply mul_left_cancel₀ (pow_ne_zero (B * a) hp.ne_zero)
  calc
    _ = u ^ (B * a) *
        (jtMatrix (fun j : Fin n => P.xi j.succ)
          (fun j => P.zeta j.castSucc)).det ^ a := hP
    _ = (u ^ (C * b) *
          (jtMatrix (fun j : Fin m => Q.xi j.succ)
            (fun j => Q.zeta j.castSucc)).det ^ b) *
        (u ^ (E * d) *
          (jtMatrix (fun j : Fin k => R.xi j.succ)
            (fun j => R.zeta j.castSucc)).det ^ d) := by
      rw [hcount, hcorner, pow_add]
      ring
    _ = ψ ^ (B * a) * ((originalRemovedMatrix (hD := hD) Q).det ^ b *
        (originalRemovedMatrix (hD := hD) R).det ^ d) := by
      rw [← hQ, ← hR, hcount, pow_add]
      ring

/-- The exact exponent law of the original full-window defect cancels removed determinants.
The corner inventories of the literal overlap and closure are DERIVED geometric inputs:
`literalWindow_component_inventory` is their component-level substrate, not their assembly. -/
theorem originalRemovedMatrix_defect_cancel {n m k : ℕ}
    (A : Profile n) (W : Profile m) (H : Profile k) (Λ : Lambda) (b v d : ℕ)
    (hv : v ≤ b) (hd : d + v = b)
    (hA : (jtMatrix (fun j : Fin n => A.xi j.succ)
      (fun j => A.zeta j.castSucc)).det = Λ ^ (2 * b - v))
    (hW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ v)
    (hH : (jtMatrix (fun j : Fin k => H.xi j.succ)
      (fun j => H.zeta j.castSucc)).det = Λ ^ (2 * b)) :
    (originalRemovedMatrix (hD := hD) A).det ^ b =
      (originalRemovedMatrix (hD := hD) W).det ^ b *
        (originalRemovedMatrix (hD := hD) H).det ^ d := by
  apply originalRemovedMatrix_multiplicative_cancel A W H b b d
  rw [hA, hW, hH, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  have he : 2 * b - v + v = 2 * b := Nat.sub_add_cancel (by omega)
  nlinarith

/-- The closure inventory is produced from its actual cells. The remaining overlap-inventory
premise is DERIVED and must be supplied by the literal full-window amalgamation construction. -/
theorem originalRemovedMatrix_actual_defect_cancel {n m k l : ℕ}
    (U : Profile n) (W : Profile m) (A : Profile k) (H : Profile l)
    (shift : ℤ × ℤ) (hclosure : originalHorizontalClosure U = translate shift H.cells)
    (Λ : Lambda) (b v d : ℕ) (hv : v ≤ b) (hd : d + v = b)
    (hU : (jtMatrix (fun j : Fin n => U.xi j.succ)
      (fun j => U.zeta j.castSucc)).det = Λ ^ b)
    (hW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ v)
    (hA : (jtMatrix (fun j : Fin k => A.xi j.succ)
      (fun j => A.zeta j.castSucc)).det = Λ ^ (2 * b - v)) :
    (originalRemovedMatrix (hD := hD) A).det ^ b =
      (originalRemovedMatrix (hD := hD) W).det ^ b *
        (originalRemovedMatrix (hD := hD) H).det ^ d := by
  apply originalRemovedMatrix_defect_cancel A W H Λ b v d hv hd hA hW
  rw [originalHorizontalClosure_profile_inventory U H shift hclosure, hU, ← pow_mul,
    Nat.mul_comm b 2]

end SkewCornerDescent.Matrix.SelectedCoordinate
