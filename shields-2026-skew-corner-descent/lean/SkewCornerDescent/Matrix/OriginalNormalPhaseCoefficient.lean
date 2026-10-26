/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalPhaseEnergy
import SkewCornerDescent.Matrix.OriginalNormalAffineCoefficient

/-!
# The ordinary original normal coefficient as filtered phase energy

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`eq:normal-interface`). The complete original comparison coefficient has a
unique affine polynomial representation over every other surviving generator.
Its ordinary linear coefficient is the full phase-filtered half-sum of squares
and whole first-log correction, including the two-state boundary. Phase
discrepancy data remain explicit; their geometric producer and the literal-root
alternative are not asserted here. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The ordinary high-generator coefficient of the whole original normal
comparison is its complete filtered phase energy and full first-log correction.
The discrepancy hypotheses are explicit; no derivative is renamed a coefficient. -/
theorem originalCompleted_normal_phase_energy_coefficient {n m an qn : ℕ}
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
    let protectedIndex := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hcountP : originalSelectedCount (hD := hD) P = b * r,
    ∃ hshort : n < originalSelectedCount (hD := hD) P,
    ∃ hcountA : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n,
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have hn' : 2 ≤ n := hn
      omega⟩ = active) →
    letI : NeZero b := ⟨by omega⟩
    letI : NeZero r := ⟨ne_of_gt hrpos⟩
    let C := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    let incoming := fun (i : Fin r) (k : ZMod b) =>
      (C (ZMod.ringEquivCongr hcountP.symm (phaseCycleEquiv b r (i,k)))).1
    let K := fun i : Fin r => ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    let ZP := ∏ i : Fin n, (c.originalInternalResidue P
      ⟨i.val, by have := i.isLt; omega⟩)⁻¹
    ∃ p : Polynomial (residueGeneratorCoefficientField c.top
      ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩), p.natDegree ≤ 1 ∧
      Polynomial.aeval
        (residueGenerator c.top ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩) p =
          PowerSeries.coeff n logDefect ∧
      (∀ q : Polynomial (residueGeneratorCoefficientField c.top
      ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩),
        Polynomial.aeval
          (residueGenerator c.top ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩) q =
            PowerSeries.coeff n logDefect → q = p) ∧
    ∀ choices : Fin r → Option ℕ,
    (∀ i, match choices i with
      | none => ∀ k, incoming i k = incoming i (k + (d : ZMod b))
      | some w => 0 < w ∧ 2 * w < K i ∧
          (∀ k l, l < w → (incoming i k).coeff l =
            (incoming i (k + (d : ZMod b))).coeff l) ∧
          (K i : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ)) →
    ((p.coeff 1 : residueGeneratorCoefficientField c.top
      ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩) : OtherField c.top) =
      (-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^n * ZP *
        (d • (∑ i : Fin r, match choices i with
          | none => 0
          | some w => if (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
              ((1/2 : OtherField c.top) * ∑ k : ZMod b,
                ((incoming i k).coeff w -
                  (incoming i (k + (d : ZMod b))).coeff w)^2) *
                (completeResponseCycle (c.originalInternalResidue P) active
                  (i.val : ZMod (originalSelectedCount (hD := hD) P)))⁻¹
            else 0) -
          ((n + 1 : ℕ) : OtherField c.top) *
            c.residueMap (pderiv J (cellSchur D hD.1)) * PowerSeries.coeff 1 logDefect) := by
  obtain ⟨hcountP, hshort, hcountA, hcountQ, henergy⟩ :=
    c.originalCompleted_normal_phase_energy_derivative P W A Q q u v w z hq0 hv
      hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW active hresponse
      hgap hmax hn J H hH κ hmatch
  obtain ⟨_, haffine⟩ := c.originalCompleted_normal_affine_coefficient
    P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
    hKU hKW active hresponse hgap hmax hn J H hH κ hmatch
  refine ⟨hcountP, hshort, hcountA, hcountQ, ?_⟩
  intro hactive
  obtain ⟨p, hdegree, heval, hcoeff, hunique⟩ := haffine hactive
  have hd := henergy hactive
  generalize hC : finiteWordCycle (c.originalInternalEndpointProfiles Q)
    (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega) = C at hd ⊢
  dsimp only at hd ⊢
  refine ⟨p, hdegree, heval, hunique, ?_⟩
  intro choices hchoice
  exact hcoeff.trans (hd choices hchoice)

end SkewCornerDescent.Matrix.SelectedCoordinate
