/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFirstCyclicHighZero
import SkewCornerDescent.Matrix.OriginalFirstLogCyclic
import SkewCornerDescent.Matrix.OriginalAmalgamationGapPeriodData

/-!
# High-generator independence of the full original first logarithm

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
At period length at least three, actual gap-period transports and the
complete cyclic comparison prove independence of the protected generator.
Both closures retain their original cap and removed-factor suppliers. The
two-state boundary is not claimed here. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original first logarithmic coefficient omits every generator
above a period of at least three states. Both actual closures and all cap and
removed-factor cancellations are supplied by the original first-log assembly. -/
theorem originalCompleted_first_log_high_zero {n m an qn : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an) (Q : Profile qn)
    (q : ℤ) (u v w z : ℤ × ℤ) (hq0 : 0 ≤ q) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate w A.cells)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hn : 3 ≤ (b - a) * r)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hH : c.top < H)
    (hheight : (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (κ : OtherField c.top)
    (hmatch : (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur)) ^ b =
      κ * ((PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ (b - a))) :
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (PowerSeries.coeff 1 (PowerSeries.logOf
        (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ (b - a))⁻¹)))) = 0 := by
  let d := b - a
  let n := d * r
  have hn3 : 3 ≤ n := hn
  have hn2 : 2 ≤ n := by omega
  let : NeZero n := ⟨by omega⟩
  obtain ⟨hshort, hcountA, hcountQ, hfirst⟩ := c.originalCompleted_first_log_cyclic
    P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
    hKU hKW hmax hn2 κ hmatch
  have hshort' : n < originalSelectedCount (hD := hD) P := hshort
  have hcountA' : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + n := hcountA
  obtain ⟨hposA, hpA, hsumA⟩ := c.originalCompleted_amalgamation_gap_period_data
    P W A q u v w hq0 hv hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW hgap
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨ne_of_gt hposA⟩
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega⟩
  have hpQ : Function.Periodic
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) Q)) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_period P Q z hQ r hgap
    · exact c.originalVerticalClosure_completed_gap_period P Q z hQ r hgap
  have hsumQ : windowSum
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x)) 1 r 0 =
      windowSum (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_window P Q z hQ r
    · exact c.originalVerticalClosure_completed_gap_window P Q z hQ r
  have hmaxA := originalAmalgamation_component_span P W A q v w u hv hwindow hW.symm hA
    (c.top : ℕ) hmax
  have hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_profile_component_span P Q z hQ hmax
    · exact c.originalVerticalClosure_profile_component_span P Q z hQ hmax
  have hA0 := c.originalInternal_first_cyclic_high_zero A hmaxA r d hn hpA H hH
    (by rw [hsumA]; exact hheight) n (by omega)
  have hQ0 := c.originalInternal_first_cyclic_high_zero Q hmaxQ r d hn hpQ H hH
    (by rw [hsumQ]; exact hheight) (originalSelectedCount (hD := hD) P) (by omega)
  dsimp only at hfirst hA0 hQ0 ⊢
  rw [hfirst, map_sub, map_nsmul, map_nsmul, hA0, hQ0, nsmul_zero, nsmul_zero, sub_self]

end SkewCornerDescent.Matrix.SelectedCoordinate
