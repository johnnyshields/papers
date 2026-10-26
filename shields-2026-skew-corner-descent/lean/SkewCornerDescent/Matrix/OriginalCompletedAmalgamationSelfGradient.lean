/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationLongSelfGradient
import SkewCornerDescent.Matrix.OriginalAmalgamationGapPeriodData

/-!
# Closed original amalgamation self-profile gradients

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original corner powers produce the actual rank offset and short-range bound.
The actual completed-gap word supplies its period and higher index; complete
literal windows supply both full source endpoint polynomials.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual amalgamation prefix long-entry gradient is its full source
self-profile coefficient. All count, period, profile, and inverse suppliers are
composed inside this declaration from the original geometric hypotheses. -/
theorem originalCompleted_amalgamation_prefix_self_gradient {n m an : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an)
    (q : ℤ) (u v w : ℤ × ℤ) (hq0 : 0 ≤ q) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate w A.cells)
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hn : 2 ≤ (b - a) * r) (i : Fin ((b - a) * r)) (J H : ℕ+)
    (hH : (H : ℤ) = (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r (b - a) hn hgap J H hH
    ∃ hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P =
      (b - a) * r,
    ∃ hshort : (b - a) * r < originalSelectedCount (hD := hD) P,
      let s : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
      let t : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
      let E := originalSelectedEnumeration (hD := hD) P
      residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
        (c.regularResidue (c.originalInternalResponseMatrix A
          ⟨i.val, by have := i.isLt; omega⟩
          ⟨i.val + (b - a) * r, by have := i.isLt; omega⟩)) =
        ((c.originalResidueLeftEndpointPolynomial P (some (E s)) (some (E t)) *
          c.originalResidueRightEndpointPolynomial P (some (E s)) (some (E t))).toLaurent).coeff
          (originalHessenbergDistance (hD := hD) P s.succ s.succ - (J : ℤ)) := by
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hCW : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  have hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = (b - a) * r := by
    rw [hcountP, hcountW, ← Nat.mul_sub_left_distrib, Nat.mul_comm]
  have hWP : originalSelectedCount (hD := hD) W ≤ originalSelectedCount (hD := hD) P := by
    rw [hcountW, hcountP]
    exact Nat.mul_le_mul_left r (Nat.le_of_lt hab)
  have hinv := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v w u hv hwindow hW.symm hA
  have hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A := by omega
  have hshift : originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P =
      (b - a) * r := by omega
  have hshort : (b - a) * r < originalSelectedCount (hD := hD) P := by omega
  obtain ⟨hApos, hdata⟩ := c.originalCompleted_amalgamation_gap_period_data P W A q u v w
    hq0 hv hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW hgap
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨ne_of_gt hApos⟩
  obtain ⟨hpA, hsum⟩ := hdata
  have hHA : (H : ℤ) = (b - a) • windowSum
      (fun x => c.originalCompletedGap A ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ) := by
    rw [hsum]
    exact hH
  obtain ⟨_, hgrad⟩ := c.originalAmalgamation_prefix_long_self_gradient P A q v w hq0 hv
    hwindow hA (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) r (b - a) hn hpA hshift hshort i J H hHA
  exact ⟨hAP, hshift, hshort, hgrad⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
