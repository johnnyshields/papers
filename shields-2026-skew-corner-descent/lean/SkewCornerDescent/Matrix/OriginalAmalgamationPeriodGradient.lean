/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationCorePhase
import SkewCornerDescent.Matrix.OriginalAmalgamationGapPeriodData
import SkewCornerDescent.Matrix.OriginalPeriodCorePhaseGradient
import SkewCornerDescent.Matrix.OriginalInternalMarkedDerivative

/-!
# Complete actual period gradients through the amalgamation splice

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal windows and source corner powers supply the full proper-core phases,
completed gap period, and unchanged period total of the actual amalgamation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full actual amalgamation period-length response has its constant normal
high gradient, including intervals crossing the prefix-to-source splice. -/
theorem originalCompleted_amalgamation_period_gradient {n m an : ℕ}
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
    (active : OtherField c.top)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (d : ℕ) (hn : 2 ≤ d * r)
    (i t : Fin (originalSelectedCount (hD := hD) A))
    (ht : t.val = i.val + d * r) (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (c.normalSeries (c.originalLocalResponse A
        (some (originalSelectedEnumeration A i)) (some (originalSelectedEnumeration A t)))) =
      PowerSeries.C (c.normalCoefficient⁻¹ *
        c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))) := by
  obtain ⟨hApos, hdata⟩ := c.originalCompleted_amalgamation_gap_period_data P W A q u v w
    hq0 hv hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW hgap
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨ne_of_gt hApos⟩
  obtain ⟨hpA, hsum⟩ := hdata
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    rw [hz, zero_mul] at hn
    omega
  have hphase (k : ℕ) (hk : k < (c.top : ℕ)) :
      (c.originalSelectedCoreRight A t).coeff k = (c.originalSelectedCoreRight A i).coeff k :=
    (c.originalCompleted_amalgamation_core_phase P W A q u v w hq0 hv hW hwindow hA hq hLq
      Λ b a r ha hab hrpos hr hKU hKW active hresponse hgap d i t ht k hk).2
  exact c.original_period_response_normal_gradient_of_core_phase A r d hrpos hd hpA
    i t ht hphase J H (by rw [hsum]; exact hH)

end SkewCornerDescent.Matrix.SelectedCoordinate
