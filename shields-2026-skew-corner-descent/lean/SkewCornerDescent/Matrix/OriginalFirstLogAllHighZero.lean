/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFirstLogTwoHighZero

/-!
# All-period high-generator independence of the original first logarithm

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Short-entry exclusion handles periods of at least three states; exact actual
occurrence balance handles the two-state boundary. Both branches retain the
complete original first logarithm and genuine inverse jets. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full original first logarithm omits the resolving generator at every
eligible period, with the two-state occurrence cancellation included. -/
theorem originalCompleted_first_log_all_high_zero {n m an qn : ℕ}
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
    (active : OtherField c.top)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hn : 2 ≤ (b - a) * r) (J H : ℕ+)
    (hH : (H : ℤ) = (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ))
    (κ : OtherField c.top)
    (hmatch : (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur)) ^ b =
      κ * ((PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ (b - a))) :
    let d := b - a
    let K := c.originalInternalPeriodHigherIndex P r d
      (show 2 ≤ d * r by dsimp only [d]; omega) hgap J H hH
    let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = active) → δ (PowerSeries.coeff 1 logDefect) = 0 := by
  by_cases htwo : (b - a) * r = 2
  · exact c.originalCompleted_first_log_two_high_zero P W A Q q u v w z hq0 hv
      hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW active hresponse
      hgap hmax htwo J H hH κ hmatch
  · have hn3 : 3 ≤ (b - a) * r := by omega
    let K := c.originalInternalPeriodHigherIndex P r (b - a) hn hgap J H hH
    have hcountQ : originalSelectedCount (hD := hD) Q =
        2 * originalSelectedCount (hD := hD) P := by
      rcases hQ with hQ | hQ
      · exact originalHorizontalClosure_profile_selected_count P Q z hQ
      · exact originalVerticalClosure_profile_selected_count P Q z hQ
    refine ⟨hcountQ, ?_⟩
    intro _hactive
    apply c.originalCompleted_first_log_high_zero P W A Q q u v w z hq0 hv
      hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW hmax hn3 hgap K.val
      K.property _ κ hmatch
    change _ < (H : ℤ)
    rw [hH]
    have hj := J.pos
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
