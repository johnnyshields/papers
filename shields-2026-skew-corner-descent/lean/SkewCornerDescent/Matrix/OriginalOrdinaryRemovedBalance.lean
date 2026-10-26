/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOrdinaryClosureCofactor
import SkewCornerDescent.Matrix.OriginalAmalgamationCornerPower
import SkewCornerDescent.Matrix.OriginalRemovedCancellation

/-!
# Exact removed-power balance in both actual ordinary closure directions

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete literal corner inventories give the closure square and the actual
amalgamation power. The original prime-order cancellation then balances the
whole removed determinants, without a supplied first jet or factor match.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Either actual ordinary closure squares the complete removed determinant.
The statement retains all nonselected blocks and selected proper cofactors. -/
theorem originalOrdinaryClosure_removed_square {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    (originalRemovedMatrix (hD := hD) Q).det =
      (originalRemovedMatrix (hD := hD) P).det ^ 2 := by
  have h := originalRemovedMatrix_pair_power (hD := hD) Q P 2 1 (by
    rw [pow_one, originalOrdinaryClosure_complementary_square P Q z hQ])
  simpa only [pow_one] using h

/-- Original corner powers and complete actual overlap geometry supply the
entire removed-factor comparison identity in both ordinary closure directions. -/
theorem originalOrdinary_removed_power_balance {n m k l : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile k) (Q : Profile l)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells ∨
      originalVerticalClosure P = translate w Q.cells)
    (Λ : Lambda) (b a d : ℕ) (hab : a ≤ b) (hd : d + a = b)
    (hKP : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a) :
    (originalRemovedMatrix (hD := hD) A).det ^ b =
      (originalRemovedMatrix (hD := hD) P).det ^ a *
        (originalRemovedMatrix (hD := hD) Q).det ^ d := by
  have hKA := originalAmalgamation_corner_power P W A q v u z hv hwindow hW hA Λ b a hab hKP hKW
  have hAeq : (originalRemovedMatrix (hD := hD) A).det ^ b =
      (originalRemovedMatrix (hD := hD) P).det ^ (2 * b - a) := by
    apply originalRemovedMatrix_pair_power A P (2 * b - a) b
    rw [hKA, hKP, ← pow_mul, ← pow_mul, Nat.mul_comm (2 * b - a) b]
  have hQeq := originalOrdinaryClosure_removed_square (hD := hD) P Q w hQ
  have hpow : 2 * b - a = a + 2 * d := by omega
  rw [hAeq, hQeq, ← pow_mul, ← pow_add, hpow]

end SkewCornerDescent.Matrix.SelectedCoordinate
