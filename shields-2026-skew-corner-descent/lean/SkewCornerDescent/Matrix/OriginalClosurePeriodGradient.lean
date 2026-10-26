/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureCorePhase
import SkewCornerDescent.Matrix.OriginalPeriodCorePhaseGradient
import SkewCornerDescent.Matrix.OriginalClosureGapPeriod
import SkewCornerDescent.Matrix.OriginalInternalMarkedDerivative

/-!
# Complete period-length gradients across the actual closure splice

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original nullspace supplies core phases, gap periods, and the same exact
period total in the actual closure. No closure phase or gradient is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual closure interval of the prescribed period length has its full
constant normal high gradient, including intervals crossing the true splice. -/
theorem originalCompleted_closure_period_gradient {n m qn : ℕ}
    (P : Profile n) (W : Profile m) (Q : Profile qn)
    (z : ℤ × ℤ) (hQ : originalHorizontalClosure P = translate z Q.cells)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (d : ℕ) (hn : 2 ≤ d * r)
    (i t : Fin (originalSelectedCount (hD := hD) Q))
    (ht : t.val = i.val + d * r) (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (c.normalSeries (c.originalLocalResponse Q
        (some (originalSelectedEnumeration Q i)) (some (originalSelectedEnumeration Q t)))) =
      PowerSeries.C (c.normalCoefficient⁻¹ *
        c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))) := by
  have hcountQ := originalHorizontalClosure_profile_selected_count (hD := hD) P Q z hQ
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by
    have hpos := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega⟩
  have hpQ := c.originalHorizontalClosure_completed_gap_period P Q z hQ r hgap
  have hsum := c.originalHorizontalClosure_completed_gap_window P Q z hQ r
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    rw [hz, zero_mul] at hn
    omega
  have hphase (k : ℕ) (hk : k < (c.top : ℕ)) :
      (c.originalSelectedCoreRight Q t).coeff k = (c.originalSelectedCoreRight Q i).coeff k :=
    (c.originalCompleted_closure_core_phase P W Q z hQ q u v hv hW hwindow hq hLq
      Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap d i t ht k hk).2
  exact c.original_period_response_normal_gradient_of_core_phase Q r d hrpos hd hpQ
    i t ht hphase J H (by rw [hsum]; exact hH)

end SkewCornerDescent.Matrix.SelectedCoordinate
