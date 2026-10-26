/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalSecondHighZero
import SkewCornerDescent.Matrix.ResidueGeneratorAffineCoefficient

/-!
# Ordinary affine extraction from the whole original comparison

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
At every eligible period, the actual whole comparison coefficient is
represented by a unique affine polynomial in the protected original generator
over all other surviving generators. Its ordinary linear coefficient is the
derivative supplied by the cyclic identity. The two-state cancellation is
included; the nonliteral discrepancy producer remains separate. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original normal coefficient is the unique ordinary affine
polynomial in the high generator at every eligible period of at least two states. -/
theorem originalCompleted_normal_affine_coefficient {n m an qn : ℕ}
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
    let n := d * r
    let K := c.originalInternalPeriodHigherIndex P r d
      (show 2 ≤ d * r by dsimp only [d]; omega) hgap J H hH
    let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = active) →
      ∃ p : Polynomial (residueGeneratorCoefficientField c.top ⟨K.val, ne_of_gt K.property⟩),
        p.natDegree ≤ 1 ∧ Polynomial.aeval (residueGenerator c.top ⟨K.val, ne_of_gt K.property⟩) p =
          PowerSeries.coeff n logDefect ∧
        ((p.coeff 1 : residueGeneratorCoefficientField c.top ⟨K.val, ne_of_gt K.property⟩) :
          OtherField c.top) = δ (PowerSeries.coeff n logDefect) ∧
        ∀ q : Polynomial (residueGeneratorCoefficientField c.top ⟨K.val, ne_of_gt K.property⟩),
          Polynomial.aeval (residueGenerator c.top ⟨K.val, ne_of_gt K.property⟩) q =
            PowerSeries.coeff n logDefect → q = p := by
  obtain ⟨hcountQ, hsecond⟩ := c.originalCompleted_normal_second_high_zero
    P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
    hKU hKW active hresponse hgap hmax hn J H hH κ hmatch
  refine ⟨hcountQ, ?_⟩
  intro hactive
  exact residueGenerator_affine_polynomial c.top _ _ (hsecond hactive)

end SkewCornerDescent.Matrix.SelectedCoordinate
